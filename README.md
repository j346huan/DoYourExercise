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

