This repository stores documentation on the PCG design and implementation. It is
intended to be the authoritative source on information about the PCG.

Currently the published version of these documents are accessible at: https://zackg.me/pcg-docs

The deployed version will eventually be accessible at: https://viperproject.github.io/pcg-docs

## Local Development

Ensure that you have `mdbook` and `mdbook katex`

```
cargo install mdbook
cargo install mdbook-katex
```

Once you have the prerequisites, run `mdbook serve` from the root directory. The
book should then be hosted on at `http://localhost:3000`

## Deployment

The documentation will automatically be built and deployed upon a push to
`main`. This is implemented via a Github action.
