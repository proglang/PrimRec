# CPP 2027 paper template

This directory contains a CPP-oriented ACM SIGPLAN template for the
primitive-recursion paper.

## Format

The template uses:

```tex
\documentclass[sigplan,10pt,anonymous,review]{acmart}
```

This is the standard ACM SIGPLAN review setup used by CPP-style
submissions.  For camera-ready, remove `review,anonymous` and fill in the
ACM metadata (`DOI`, `ISBN`, copyright, conference dates, and author
blocks) according to the acceptance instructions.

## Build

From this directory:

```sh
make
```

or directly:

```sh
latexmk -pdf main.tex
```

The template reuses repository-level support files:

- `../agda.sty`
- `../unicodeletters.tex`
- `../jfprefs.bib`

## Notes for the rewrite

- Keep the main CPP submission within the current CPP page limit
  specified by the CFP.
- Treat categorical distributivity as infrastructure.
- Make `Everything.agda` the trusted artifact entry point.
- Include a paper-to-code table so reviewers can locate claims quickly.
- Before submission, verify the exact current CPP CFP formatting
  instructions and adjust the class options/metadata if needed.
