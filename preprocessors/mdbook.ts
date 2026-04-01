/// Shared types and utilities for mdbook preprocessors.
import * as process from "process";

export interface Chapter {
  name?: string;
  content?: string;
  path?: string;
  sub_items?: Array<{ Chapter?: Chapter }>;
}

export interface Section {
  Chapter?: Chapter;
}

export interface Book {
  sections?: Section[];
}

export interface BookContext {
  root?: string;
  config?: Record<string, unknown>;
}

/// Recursively visits a chapter and all its sub-chapters.
function visitChapter(
  chapter: Chapter,
  fn: (chapter: Chapter) => void
): void {
  fn(chapter);
  if (chapter.sub_items) {
    for (const item of chapter.sub_items) {
      if (item.Chapter) {
        visitChapter(item.Chapter, fn);
      }
    }
  }
}

/// Calls `fn` on every chapter in the book's sections.
export function forEachChapter(
  sections: Section[],
  fn: (chapter: Chapter) => void
): void {
  for (const section of sections) {
    if (section.Chapter) {
      visitChapter(section.Chapter, fn);
    }
  }
}

/// Reads the mdbook preprocessor input from stdin, parses it, and calls `processBook`.
/// Handles the `supports` subcommand automatically.
export function runPreprocessor(
  processBook: (context: BookContext, book: Book) => void
): void {
  if (process.argv.length > 2 && process.argv[2] === "supports") {
    process.exit(process.argv[3] === "html" ? 0 : 1);
  }

  const chunks: string[] = [];
  process.stdin.setEncoding("utf-8");

  process.stdin.on("data", (chunk: string) => {
    chunks.push(chunk);
  });

  process.stdin.on("end", () => {
    const input = chunks.join("");
    if (!input || input.trim() === "") {
      process.exit(0);
    }

    try {
      const [context, book] = JSON.parse(input) as [BookContext, Book];
      processBook(context, book);
      process.stdout.write(JSON.stringify(book));
    } catch (error) {
      const err = error as Error;
      process.stderr.write(`Error in preprocessor: ${err.message}\n`);
      process.exit(1);
    }
  });
}
