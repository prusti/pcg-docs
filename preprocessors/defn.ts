#!/usr/bin/env node

import * as process from "process";
import * as fs from "fs";
import * as path from "path";
import {
  Book,
  BookContext,
  forEachChapter,
  runPreprocessor,
} from "./mdbook";

interface MacroInfo {
  name: string;
  argCount: number;
}

interface DefnSite {
  id: string;
  chapterPath: string;
}

function parseMacros(macrosPath: string): Map<string, MacroInfo> {
  const macros = new Map<string, MacroInfo>();
  const content = fs.readFileSync(macrosPath, "utf-8");
  for (const line of content.split("\n")) {
    const trimmed = line.trim();
    if (!trimmed) continue;
    const match = trimmed.match(/^\\([a-zA-Z]+):\{(.*)\}$/);
    if (!match) {
      process.stderr.write(`Warning: could not parse macro line: ${trimmed}\n`);
      continue;
    }
    const [, name, definition] = match;
    const argNums = [...definition.matchAll(/#(\d+)/g)].map((m) =>
      parseInt(m[1], 10)
    );
    const argCount = argNums.length > 0 ? Math.max(...argNums) : 0;
    macros.set(name, { name, argCount });
  }
  return macros;
}

function chapterPathToHtml(chapterPath: string): string {
  return chapterPath.replace(/\.md$/, ".html");
}

/// Computes a relative path from `fromChapter` to `toChapter` (both as .md paths from src root).
function relativeHtmlPath(fromChapter: string, toChapter: string): string {
  const fromDir = path.dirname(fromChapter);
  const toHtml = chapterPathToHtml(toChapter);
  return path.relative(fromDir, toHtml);
}

interface MathSegment {
  start: number;
  end: number;
  isDisplay: boolean;
}

interface WrapperConfig {
  name: string;
  /// Number of arguments to skip before the content argument being checked.
  skipArgs: number;
}

/// Macros whose content argument should not be auto-linked.
const WRAPPER_CONFIGS: WrapperConfig[] = [
  { name: "\\defn", skipArgs: 1 },
  { name: "\\href", skipArgs: 1 },
  { name: "\\htmlId", skipArgs: 1 },
  { name: "\\noref", skipArgs: 0 },
];

/// Finds all math segments (both `$...$` and `$$...$$`) in the content,
/// returning their start/end positions (of the inner content, excluding delimiters).
function findMathSegments(content: string): MathSegment[] {
  const segments: MathSegment[] = [];
  let i = 0;
  while (i < content.length) {
    if (content[i] === "$") {
      if (content[i + 1] === "$") {
        const innerStart = i + 2;
        const end = content.indexOf("$$", innerStart);
        if (end === -1) break;
        segments.push({ start: i, end: end + 2, isDisplay: true });
        i = end + 2;
      } else {
        const innerStart = i + 1;
        const end = content.indexOf("$", innerStart);
        if (end === -1) break;
        segments.push({ start: i, end: end + 1, isDisplay: false });
        i = end + 1;
      }
    } else if (content[i] === "`") {
      // Skip code spans/blocks to avoid processing $ inside code
      if (content.startsWith("```", i)) {
        const endFence = content.indexOf("```", i + 3);
        i = endFence === -1 ? content.length : endFence + 3;
      } else {
        const endTick = content.indexOf("`", i + 1);
        i = endTick === -1 ? content.length : endTick + 1;
      }
    } else {
      i++;
    }
  }
  return segments;
}

/// Matches a brace-delimited argument starting at position `pos`.
/// Returns the content inside the braces and the position after the closing brace.
function matchBraceArg(
  text: string,
  pos: number
): { arg: string; end: number } | null {
  if (pos >= text.length || text[pos] !== "{") return null;
  let depth = 1;
  let i = pos + 1;
  while (i < text.length && depth > 0) {
    if (text[i] === "{") depth++;
    else if (text[i] === "}") depth--;
    i++;
  }
  if (depth !== 0) return null;
  return { arg: text.slice(pos + 1, i - 1), end: i };
}

/// Checks whether position `pos` in `text` is inside the content argument of
/// any wrapper macro defined in WRAPPER_CONFIGS.
function isInsideWrapper(text: string, pos: number): boolean {
  for (const { name, skipArgs } of WRAPPER_CONFIGS) {
    let searchStart = 0;
    while (true) {
      const idx = text.indexOf(name, searchStart);
      if (idx === -1 || idx >= pos) break;
      let cursor = idx + name.length;
      let skipped = true;
      for (let k = 0; k < skipArgs; k++) {
        const arg = matchBraceArg(text, cursor);
        if (!arg) { skipped = false; break; }
        cursor = arg.end;
      }
      if (!skipped) { searchStart = cursor; continue; }
      const targetArg = matchBraceArg(text, cursor);
      if (!targetArg) { searchStart = cursor; continue; }
      if (pos > cursor && pos < targetArg.end) return true;
      searchStart = targetArg.end;
    }
  }
  return false;
}

/// Collects all `\defn{id}{content}` sites from math content.
function collectDefnSites(
  content: string,
  chapterPath: string,
  macros: Map<string, MacroInfo>,
  defnMap: Map<string, DefnSite>
): void {
  const segments = findMathSegments(content);
  const defnPattern = /\\defn\{([^}]+)\}\{/g;
  for (const seg of segments) {
    const mathContent = content.slice(seg.start, seg.end);
    let match;
    defnPattern.lastIndex = 0;
    while ((match = defnPattern.exec(mathContent)) !== null) {
      const id = match[1];
      if (defnMap.has(id)) {
        const existing = defnMap.get(id)!;
        process.stderr.write(
          `Error: duplicate \\defn for "${id}" in ${chapterPath} (first defined in ${existing.chapterPath})\n`
        );
        process.exit(1);
      }
      if (!macros.has(id)) {
        process.stderr.write(
          `Warning: \\defn id "${id}" does not match any known macro name\n`
        );
      }
      defnMap.set(id, { id, chapterPath });
    }
  }
}

/// Builds a regex that matches any of the defined macro names (as `\macroname`).
function buildMacroPattern(definedMacroNames: string[]): RegExp | null {
  if (definedMacroNames.length === 0) return null;
  const escaped = definedMacroNames.map((n) =>
    n.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")
  );
  return new RegExp(`\\\\(${escaped.join("|")})(?![a-zA-Z])`, "g");
}

/// Resolves `\ref{id}{content}` to `\href{file.html#defn-id}{content}`.
function resolveManualRefs(
  text: string,
  defnMap: Map<string, DefnSite>,
  fromChapter: string
): string {
  return text.replace(
    /\\ref\{([^}]+)\}/g,
    (match, id: string) => {
      const defnSite = defnMap.get(id);
      if (!defnSite) {
        process.stderr.write(`Warning: \\ref id "${id}" has no matching \\defn\n`);
        return match;
      }
      const htmlPath = relativeHtmlPath(fromChapter, defnSite.chapterPath);
      return `\\href{${htmlPath}#defn-${id}}`;
    }
  );
}

/// Strips `\noref{content}` wrappers, leaving just the content.
function stripNoref(text: string): string {
  return text.replace(/\\noref\{/g, "{");
}

/// Processes a single math segment, replacing `\defn`, `\ref`, `\noref`, and wrapping macro references.
function processMathContent(
  mathText: string,
  defnMap: Map<string, DefnSite>,
  macros: Map<string, MacroInfo>,
  macroPattern: RegExp | null,
  fromChapter: string
): string {
  let result = mathText.replace(
    /\\defn\{([^}]+)\}/g,
    (_match, id: string) => `\\htmlId{defn-${id}}`
  );

  result = resolveManualRefs(result, defnMap, fromChapter);

  if (!macroPattern) return stripNoref(result);

  // Now wrap macro references with \href, working on the result after defn replacement
  let output = "";
  let lastIndex = 0;
  macroPattern.lastIndex = 0;

  let match;
  while ((match = macroPattern.exec(result)) !== null) {
    const macroName = match[1];
    const matchStart = match.index;

    if (!defnMap.has(macroName)) continue;
    if (isInsideWrapper(result, matchStart)) continue;

    const defnSite = defnMap.get(macroName)!;
    const macroInfo = macros.get(macroName)!;
    const href = `${relativeHtmlPath(fromChapter, defnSite.chapterPath)}#defn-${macroName}`;

    output += result.slice(lastIndex, matchStart);

    let macroEnd = match.index + match[0].length;
    let fullMacroText = match[0];
    for (let i = 0; i < macroInfo.argCount; i++) {
      const arg = matchBraceArg(result, macroEnd);
      if (!arg) break;
      fullMacroText += result.slice(macroEnd, arg.end);
      macroEnd = arg.end;
    }

    const needsBraces =
      matchStart > 0 && (result[matchStart - 1] === "_" || result[matchStart - 1] === "^");
    const hrefText = `\\href{${href}}{${fullMacroText}}`;
    output += needsBraces ? `{${hrefText}}` : hrefText;
    lastIndex = macroEnd;
    macroPattern.lastIndex = macroEnd;
  }

  output += result.slice(lastIndex);
  return stripNoref(output);
}

/// Returns true if position `pos` falls inside any of the given math segments.
function isInsideMath(pos: number, segments: MathSegment[]): boolean {
  return segments.some((seg) => pos >= seg.start && pos < seg.end);
}

/// Resolves `\ref{id}{content}` outside of math to HTML links.
/// Leaves `\ref` inside math for `processMathContent` to handle.
function resolveTextRefs(
  content: string,
  defnMap: Map<string, DefnSite>,
  mathSegments: MathSegment[],
  fromChapter: string
): string {
  const pattern = /\\ref\{([^}]+)\}\{/g;
  let output = "";
  let lastIndex = 0;
  let match;
  while ((match = pattern.exec(content)) !== null) {
    if (isInsideMath(match.index, mathSegments)) continue;

    const id = match[1];
    const contentArg = matchBraceArg(content, match.index + match[0].length - 1);
    if (!contentArg) continue;

    output += content.slice(lastIndex, match.index);
    const defnSite = defnMap.get(id);
    if (!defnSite) {
      process.stderr.write(`Warning: \\ref id "${id}" has no matching \\defn\n`);
      output += contentArg.arg;
    } else {
      const htmlPath = relativeHtmlPath(fromChapter, defnSite.chapterPath);
      output += `<a href="${htmlPath}#defn-${id}" class="defn-ref">${contentArg.arg}</a>`;
    }
    lastIndex = contentArg.end;
    pattern.lastIndex = contentArg.end;
  }
  output += content.slice(lastIndex);
  return output;
}

/// Processes a chapter's content, transforming non-math refs then math segments.
function processChapterContent(
  content: string,
  defnMap: Map<string, DefnSite>,
  macros: Map<string, MacroInfo>,
  macroPattern: RegExp | null,
  chapterPath: string
): string {
  const mathSegments = findMathSegments(content);
  const withTextRefs = resolveTextRefs(content, defnMap, mathSegments, chapterPath);

  const segments = findMathSegments(withTextRefs);
  let result = "";
  let lastEnd = 0;

  for (const seg of segments) {
    result += withTextRefs.slice(lastEnd, seg.start);
    const mathText = withTextRefs.slice(seg.start, seg.end);
    const delimLen = seg.isDisplay ? 2 : 1;
    const inner = mathText.slice(delimLen, mathText.length - delimLen);
    const processed = processMathContent(inner, defnMap, macros, macroPattern, chapterPath);
    const delim = seg.isDisplay ? "$$" : "$";
    result += delim + processed + delim;
    lastEnd = seg.end;
  }

  result += withTextRefs.slice(lastEnd);
  return result;
}

runPreprocessor((context, book) => {
  const sections = book.sections ?? [];

  const rootDir = context.root ?? ".";
  const macrosPath = path.join(rootDir, "macros.txt");
  const macros = parseMacros(macrosPath);

  const defnMap = new Map<string, DefnSite>();
  forEachChapter(sections, (chapter) => {
    if (chapter.content && chapter.path) {
      collectDefnSites(chapter.content, chapter.path, macros, defnMap);
    }
  });

  const definedMacroNames = [...defnMap.keys()].filter((k) => macros.has(k));
  const macroPattern = buildMacroPattern(definedMacroNames);

  forEachChapter(sections, (chapter) => {
    if (chapter.content && chapter.path) {
      chapter.content = processChapterContent(
        chapter.content,
        defnMap,
        macros,
        macroPattern,
        chapter.path
      );
    }
  });
});
