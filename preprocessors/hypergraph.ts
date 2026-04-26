#!/usr/bin/env node

import * as yaml from 'js-yaml';
import { Chapter, forEachChapter, runPreprocessor } from './mdbook';

runPreprocessor((_context, book) => {
    forEachChapter(book.sections ?? [], processChapter);
});

function processChapter(chapter: Chapter): void {
    if (!chapter.content) return;

    const hypergraphPattern = /```hypergraph(?:-yaml)?\n([\s\S]*?)```/g;
    let match;
    let newContent = chapter.content;
    let counter = 0;

    while ((match = hypergraphPattern.exec(chapter.content)) !== null) {
        const rawData = match[1];
        const isYaml = match[0].includes('hypergraph-yaml');
        const graphId = `hypergraph-${(chapter.name || 'unknown').replace(/[^a-zA-Z0-9]/g, '-')}-${counter++}`;

        try {
            let parsedData: any;

            if (isYaml) {
                parsedData = yaml.load(rawData);
            } else {
                parsedData = JSON.parse(rawData);
            }

            const height = parsedData.height ?? '400px';
            delete parsedData.height;

            const couplingAlgorithms = parsedData.couplingAlgorithms ?? [];
            delete parsedData.couplingAlgorithms;

            const jsonData = JSON.stringify(parsedData, null, 2);
            const couplingData = JSON.stringify(couplingAlgorithms);

            const replacement = `<div class="hypergraph-container" id="${graphId}" data-height="${height}" data-coupling-algorithms='${couplingData}'>
    <script type="application/json" class="hypergraph-data">${jsonData}</script>
</div>`;

            newContent = newContent.replace(match[0], replacement);
        } catch (e) {
            const err = e as Error;
            const errorType = isYaml ? 'YAML' : 'JSON';
            const replacement = `<div class="hypergraph-error">
    <p>Error: Invalid ${errorType} in hypergraph definition: ${err.message}</p>
    <pre><code>${rawData}</code></pre>
</div>`;
            newContent = newContent.replace(match[0], replacement);
        }
    }

    chapter.content = newContent;
}

