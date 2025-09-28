const path = require('path');

module.exports = {
  entry: './src-js/hypergraph-renderer.js',
  output: {
    filename: 'hypergraph.js',
    path: path.resolve(__dirname, 'theme'),
  },
  mode: 'production'
};
