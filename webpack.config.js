const path = require('path');

module.exports = {
  entry: './src-js/hypergraph-renderer.ts',
  output: {
    filename: 'hypergraph.js',
    path: path.resolve(__dirname, 'theme'),
  },
  module: {
    rules: [
      {
        test: /\.ts$/,
        use: 'ts-loader',
        exclude: /node_modules/,
      },
    ],
  },
  resolve: {
    extensions: ['.ts', '.js'],
  },
  mode: 'production'
};
