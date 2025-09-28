#!/usr/bin/env node

const process = require('process');

// Check if this is a supports check
if (process.argv.length > 2 && process.argv[2] === 'supports') {
    // We support the HTML renderer
    if (process.argv[3] === 'html') {
        process.exit(0);
    } else {
        process.exit(1);
    }
}

// Read input from stdin
let chunks = [];
process.stdin.setEncoding('utf-8');

process.stdin.on('data', (chunk) => {
    chunks.push(chunk);
});

process.stdin.on('end', () => {
    const input = chunks.join('');

    if (!input || input.trim() === '') {
        // If no input, just exit successfully (mdbook might be testing)
        process.exit(0);
    }

    try {
        const [context, book] = JSON.parse(input);

        // Process each section
        if (book && book.sections && Array.isArray(book.sections)) {
            book.sections.forEach((section) => {
                if (section.Chapter) {
                    processChapter(section.Chapter);
                }
            });
        }

        // Output the processed book
        process.stdout.write(JSON.stringify(book));
    } catch (error) {
        process.stderr.write('Error processing book: ' + error.message + '\n');
        // Try alternative format (just the book object)
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
        } catch (e2) {
            process.stderr.write('Failed to parse alternative format: ' + e2.message + '\n');
            process.exit(1);
        }
    }
});

function processChapter(chapter) {
    if (!chapter.content) return;

    // Find and replace hypergraph code blocks
    const hypergraphPattern = /```hypergraph\n([\s\S]*?)```/g;
    let match;
    let newContent = chapter.content;
    let counter = 0;

    while ((match = hypergraphPattern.exec(chapter.content)) !== null) {
        const graphData = match[1];
        const graphId = `hypergraph-${(chapter.name || 'unknown').replace(/[^a-zA-Z0-9]/g, '-')}-${counter++}`;

        try {
            // Validate JSON
            JSON.parse(graphData);

            // Create HTML container with the graph data
            const replacement = `<div class="hypergraph-container" id="${graphId}">
    <script type="application/json" class="hypergraph-data">${graphData}</script>
</div>`;

            newContent = newContent.replace(match[0], replacement);
        } catch (e) {
            // If JSON is invalid, leave as code block with error message
            const replacement = `<div class="hypergraph-error">
    <p>Error: Invalid JSON in hypergraph definition</p>
    <pre><code>${graphData}</code></pre>
</div>`;
            newContent = newContent.replace(match[0], replacement);
        }
    }

    chapter.content = newContent;

    // Process sub-chapters recursively
    if (chapter.sub_items) {
        chapter.sub_items.forEach((item) => {
            if (item.Chapter) {
                processChapter(item.Chapter);
            }
        });
    }
}
