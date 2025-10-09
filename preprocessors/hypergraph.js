#!/usr/bin/env node
"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
const process = __importStar(require("process"));
const yaml = __importStar(require("js-yaml"));
if (process.argv.length > 2 && process.argv[2] === 'supports') {
    if (process.argv[3] === 'html') {
        process.exit(0);
    }
    else {
        process.exit(1);
    }
}
let chunks = [];
process.stdin.setEncoding('utf-8');
process.stdin.on('data', (chunk) => {
    chunks.push(chunk);
});
process.stdin.on('end', () => {
    const input = chunks.join('');
    if (!input || input.trim() === '') {
        process.exit(0);
    }
    try {
        const [context, book] = JSON.parse(input);
        if (book && book.sections && Array.isArray(book.sections)) {
            book.sections.forEach((section) => {
                if (section.Chapter) {
                    processChapter(section.Chapter);
                }
            });
        }
        process.stdout.write(JSON.stringify(book));
    }
    catch (error) {
        const err = error;
        process.stderr.write('Error processing book: ' + err.message + '\n');
        try {
            const book = JSON.parse(input);
            if (book && book.sections && Array.isArray(book.sections)) {
                book.sections.forEach((section) => {
                    if (section.Chapter) {
                        processChapter(section.Chapter);
                    }
                });
            }
            process.stdout.write(JSON.stringify(book));
        }
        catch (e2) {
            const err2 = e2;
            process.stderr.write('Failed to parse alternative format: ' + err2.message + '\n');
            process.exit(1);
        }
    }
});
function processChapter(chapter) {
    if (!chapter.content)
        return;
    const hypergraphPattern = /```hypergraph(?:-yaml)?\n([\s\S]*?)```/g;
    let match;
    let newContent = chapter.content;
    let counter = 0;
    while ((match = hypergraphPattern.exec(chapter.content)) !== null) {
        const rawData = match[1];
        const isYaml = match[0].includes('hypergraph-yaml');
        const graphId = `hypergraph-${(chapter.name || 'unknown').replace(/[^a-zA-Z0-9]/g, '-')}-${counter++}`;
        try {
            let parsedData;
            if (isYaml) {
                parsedData = yaml.load(rawData);
            }
            else {
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
        }
        catch (e) {
            const err = e;
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
