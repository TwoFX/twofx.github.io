const path = require("path");
const CopyPlugin = require("copy-webpack-plugin");

module.exports = {
  mode: "development",
  devtool: "source-map",
  plugins: [
    new CopyPlugin({
      patterns: [
        {
          from: "node_modules/bootstrap/dist/css/bootstrap.min.css",
          to: "bootstrap.css",
        },
        {
          from: "src/style.css",
          to: "style.css",
        },
        { from: "node_modules/jszip/dist/jszip.min.js", to: "jszip.js" },
        { from: "node_modules/epubjs/dist/epub.min.js", to: "epub.js" },
        { from: "node_modules/katex/dist/katex.css", to: "katex/katex.css" },
        { from: "node_modules/katex/dist/fonts", to: "katex/fonts" },
        {
          from: "src/index.html",
          to: "index.html",
        },
        {
          from: "media",
          to: "media",
        },
        { from: "tests/test.html", to: "tests.html" },
        { from: "node_modules/mocha/mocha.js", to: "mocha.js" },
        { from: "node_modules/mocha/mocha.css", to: "mocha.css" },
        { from: "node_modules/chai/chai.js", to: "chai.js" },
      ],
    }),
  ],
  entry: {
    main: path.resolve(__dirname, "src/index.js"),
    test: path.resolve(__dirname, "tests/test.js"),
  },
  output: {
    filename: "[name].js",
    path: path.resolve(__dirname, "docs"),
  },
  module: {
    rules: [
      {
        test: /\.txt$/i,
        use: ["raw-loader"],
      },
    ],
  },
};
