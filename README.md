# Do Your Exercise

A personal repository of textbook exercise solutions and Lean 4 formalizations.

[Website](https://j346huan.github.io/DoYourExercise/) · [Repository](https://github.com/j346huan/DoYourExercise)

## Content

- `Atiyah69`: Atiyah–Macdonald, _Introduction to Commutative Algebra_ (1969), Chapter 1.
- `Hartshorne77`: Hartshorne, _Algebraic Geometry_ (1977).

The editable files are in `content/`. Statements, natural-language proofs, Lean source, and Lean translations remain separate. Exercise titles are optional and are used only when the textbook supplies an individual title. Exercise identities use `chapter.problem` or `chapter.section.problem`; there are no topic tags.

See [AUTHORING.md](AUTHORING.md) for the file format. The [Chapter 1 import record](content/Atiyah69/IMPORT.md) records source provenance separately from the reading interface.

## Local use

Install Node.js 22.13+ (Node 22 recommended on Windows):

```sh
npm ci
npm run dev
```

On this computer, `./Start-Notebook.ps1` selects a compatible installed runtime.

Edit canonical files in `content/`, then refresh the page. Do not edit generated files in `public/content/`, `public/catalog.json`, or `LeanExercises/`.

```sh
npm run content:build
npm test
npm run typecheck
npm run build
```

## Publishing

Each push to `main` builds and publishes to GitHub Pages. The deployable output is `site-dist/`.

For the equivalent local production build in PowerShell:

```powershell
$env:SITE_BASE_PATH = '/DoYourExercise'
npm run build
```

## Lean

The project pins Lean and Mathlib to `v4.24.0`. After installing Lean through elan:

```sh
npm run lean:prepare
lake update
lake exe cache get
npm run lean:check
```

No Lean proofs are currently included. Canonical Lean sources, when added, live beside their exercise's statement and proof. Generated module copies allow later exercises to import earlier results. Only a successful compiler check creates the evidence required for `formalized` status.
