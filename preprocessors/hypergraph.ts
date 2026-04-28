#!/usr/bin/env node

import * as yaml from 'js-yaml';
import { Chapter, forEachChapter, runPreprocessor } from './mdbook';

runPreprocessor((_context, book) => {
    forEachChapter(book.sections ?? [], processChapter);
});

function processChapter(chapter: Chapter): void {
    if (!chapter.content) return;

    const content = chapter.content;
    const hypergraphPattern = /```hypergraph(?:-yaml)?\n([\s\S]*?)```/g;
    let result = '';
    let lastIndex = 0;
    let counter = 0;
    let match;

    while ((match = hypergraphPattern.exec(content)) !== null) {
        result += content.slice(lastIndex, match.index);
        lastIndex = match.index + match[0].length;

        const rawData = match[1];
        const isYaml = match[0].includes('hypergraph-yaml');
        const graphId = `hypergraph-${(chapter.name || 'unknown').replace(/[^a-zA-Z0-9]/g, '-')}-${counter++}`;

        try {
            const rawParsed: Record<string, unknown> = isYaml
                ? yaml.load(rawData) as Record<string, unknown>
                : JSON.parse(rawData);
            const { height = '400px', couplingAlgorithms = [], ...graphData } = rawParsed;

            const jsonData = JSON.stringify(graphData, null, 2);
            const couplingData = JSON.stringify(couplingAlgorithms);

            result += `<div class="hypergraph-container" id="${graphId}" data-height="${height}" data-coupling-algorithms='${couplingData}'>
    <script type="application/json" class="hypergraph-data">${jsonData}</script>
</div>`;
        } catch (e) {
            const err = e as Error;
            const errorType = isYaml ? 'YAML' : 'JSON';
            result += `<div class="hypergraph-error">
    <p>Error: Invalid ${errorType} in hypergraph definition: ${err.message}</p>
    <pre><code>${rawData}</code></pre>
</div>`;
        }
    }

    result += content.slice(lastIndex);
    chapter.content = result;
}

