# Do Your Exercise

My repository of textbook exercise solutions and Lean 4 formalizations.

[Website](https://j346huan.github.io/DoYourExercise/) · [Repository](https://github.com/j346huan/DoYourExercise)


See [AUTHORING.md](AUTHORING.md) for the file format. 

## Local use

Install Node.js 22.13+ (Node 22 recommended on Windows):

```sh
npm ci
npm run dev
```

On Windows, you can also start the site with `./Start-Notebook.ps1`.

Edit canonical files in `content/`, then refresh the page. Do not edit generated files in `public/content/` or `public/catalog.json`.

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

This repository displays completed Lean proofs and records how they were checked. Lean development, Mathlib, examples, drafts, generated modules, and compiler caches live outside the repository, under `D:\lean` on this computer. The local workflow is documented in `D:\lean\README.md` and launched with `D:\lean\Exercise.ps1`.

Only finished `proof.lean` files and their `verification.json` records belong in the exercise folders. An optional `translation.tex` explains the formalization. Exercise modules can import Mathlib and other completed exercise modules; see [AUTHORING.md](AUTHORING.md#lean-formalizations) for naming and metadata.

The website does not run Lean. It checks that a recorded successful run matches the current final sources, then displays the compiler version, Mathlib revision, commands, date, and any recorded declarations and axioms. The Lean source and verification record are downloadable from the exercise page.
