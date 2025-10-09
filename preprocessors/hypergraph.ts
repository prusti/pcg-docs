#!/usr/bin/env node

import * as process from 'process';
import * as yaml from 'js-yaml';

interface Chapter {
    name?: string;
    content?: string;
    sub_items?: Array<{ Chapter?: Chapter }>;
}

interface Section {
    Chapter?: Chapter;
}

interface Book {
    sections?: Section[];
}

if (process.argv.length > 2 && process.argv[2] === 'supports') {
    if (process.argv[3] === 'html') {
        process.exit(0);
    } else {
        process.exit(1);
    }
}

let chunks: string[] = [];
process.stdin.setEncoding('utf-8');

process.stdin.on('data', (chunk: string) => {
    chunks.push(chunk);
});

process.stdin.on('end', () => {
    const input = chunks.join('');

    if (!input || input.trim() === '') {
        process.exit(0);
    }

    try {
        const [context, book] = JSON.parse(input) as [any, Book];

        if (book && book.sections && Array.isArray(book.sections)) {
            book.sections.forEach((section) => {
                if (section.Chapter) {
                    processChapter(section.Chapter);
                }
            });
        }

        process.stdout.write(JSON.stringify(book));
    } catch (error) {
        const err = error as Error;
        process.stderr.write('Error processing book: ' + err.message + '\n');
        try {
            const book = JSON.parse(input) as Book;
            if (book && book.sections && Array.isArray(book.sections)) {
                book.sections.forEach((section) => {
                    if (section.Chapter) {
                        processChapter(section.Chapter);
                    }
                });
            }
            process.stdout.write(JSON.stringify(book));
        } catch (e2) {
            const err2 = e2 as Error;
            process.stderr.write('Failed to parse alternative format: ' + err2.message + '\n');
            process.exit(1);
        }
    }
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

            const height = parsedData.height || '400px';
            if (parsedData.height) {
                delete parsedData.height;
            }

            const couplingAlgorithms = parsedData.couplingAlgorithms || [];
            if (parsedData.couplingAlgorithms) {
                delete parsedData.couplingAlgorithms;
            }

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

    if (chapter.sub_items) {
        chapter.sub_items.forEach((item) => {
            if (item.Chapter) {
                processChapter(item.Chapter);
            }
        });
    }
}

