# Do Your Exercise

A personal mathematical notebook: linked textbook exercises, natural-language proofs, and Lean 4 formalizations. The compact charcoal interface is inspired by [noro6's simulator](https://noro6.github.io/kc-web/), with an independent mathematical workflow.

## This edition

Six original demo exercises are included. Four are solved in natural language and have **unverified Lean examples**; two are unsolved. The algebra and geometry notebooks demonstrate same-book and cross-book references, chapters with sections, and chapters without sections. Atiyah–Macdonald (1969) and Hartshorne (1977) are empty planned collections. No real textbook exercises or claimed formal verifications are included.

## Run locally

Install Node.js 22.13+ (Node 22 is recommended on Windows), then:

```sh
npm ci
npm run dev
```

On this computer you can also run `./Start-Notebook.ps1`, which selects an installed compatible runtime.

Open the local address printed by the server. The content watcher rebuilds the catalog when you edit `content/`; refresh the page to load changed catalog metadata or statements. Proof/source files are fetched separately when their view opens. This is a static publishing workflow, not an in-browser editor.

```sh
npm run content:build
npm test
npm run typecheck
npm run build
```

The deployable artifact is `site-dist/`. GitHub Actions runs these checks and rebuilds the entire notebook on each push to `main`.

## Add or edit an exercise

The canonical editable files are under `content/`, not the generated `public/content/` directory:

```text
content/
  Notebook26/
    book.json
    Notebook26-1-1-2/
      meta.json
      statement.tex
      proof.tex
      proof.lean
      translation.tex
      verification.json   # only after a successful Lean check
```

- `statement.tex`: only the problem statement.
- `proof.tex`: the natural-language solution; omit for an unsolved exercise.
- `proof.lean`: the Lean 4 source; optional for a solved exercise.
- `translation.tex`: a literal human explanation of that Lean source, required when Lean code is supplied.
- `meta.json`: title, numbering, topic tags, status, and references.
- `verification.json`: generated compilation evidence for `formalized` status; never write it manually.

Each part is separately downloadable. The searchable catalog contains statements and metadata, **never the full natural proof, Lean code, or translation**. An AI can read an individual `statement.tex` without loading the rest of the exercise.

See [CONTRIBUTING.md](CONTRIBUTING.md) for complete examples and supported TeX syntax.

## Stable references

A book ID is the first author's last name plus publication year: `Atiyah69`, `Hartshorne77`. Add a stable suffix only for a collision, such as `Smith26a` and `Smith26b`. Set the book ID explicitly in `book.json`; it must match the directory and use ASCII letters and digits.

Exercise numbering is `chapter.section.problem`, or `chapter.problem` when the book has no sections. The full identity is `BookID,numbering`. Folders and static exercise pages replace punctuation with dashes:

- Identity: `Notebook26,1.1.2`
- Folder: `content/Notebook26/Notebook26-1-1-2/`
- Website route: `#/problem/Notebook26-1-1-2`
- Shareable static page: `exercises/Notebook26-1-1-2/index.html`

Write `\exref{1.1.1}` for a same-book link or `\exref{Notebook26,1.1.1}` for a cross-book link. `BookID:1.1.1` is also accepted. Unknown references stop the build. Topic tags are independent of exercise identities and behave as searchable filters.

## Reading workspace

- Search by approximate title, statement text, reference, or topic.
- Combine filters: `[associativity] book:Notebook26 status:solved`.
- Press `/` to focus search. Use arrow keys and Enter for results; Escape dismisses popups.
- Click a book to expand chapters, sections, and exercises.
- The square-plus buttons open **internal tabs**, preserving the page you were reading.
- Open tabs are stored only in this browser's local storage. Scroll positions are retained while the app remains open.
- Hover or keyboard-focus an exercise reference for a statement preview and new-tab button.
- The Lean popup displays source beside its literal explanation.

## Lean workspace

The project pins Lean and Mathlib to `v4.24.0`. Install Lean via [elan](https://github.com/leanprover/elan), then from the repository root:

```sh
npm run lean:prepare
lake update
lake exe cache get
npm run lean:check
```

Mathlib and its cache can be large. They are not needed to run the website.

`lean:prepare` copies canonical tag-folder sources into generated valid Lean module paths. For example:

```text
content/Notebook26/Notebook26-1-1-1/proof.lean
    → LeanExercises/Notebook26/Ex_1_1_1.lean
```

A later proof can import `LeanExercises.Notebook26.Ex_1_1_1`, or import `Mathlib` directly. Edit the original tag-folder `proof.lean`, then prepare again; do not edit the generated module copy. Run `lake update` once and commit the resulting `lake-manifest.json` to lock exact dependency commits.

`lean:check` regenerates modules and runs `lake build`. Only a successful compilation writes verification records. Evidence binds to all canonical Lean sources, the toolchain, Lake configuration, and dependency manifest; changing one invalidates it. After reviewing a successfully checked proof, change its status to `formalized`. The site build rejects missing or stale evidence and rejects `sorry`, `admit`, and `axiom` tokens in included proof files. This is a conservative authoring check, not a security sandbox or a claim that a natural-language statement has been mechanically compared to its Lean formulation.

The current sample snippets have not been compiled. They remain `solved`.

## GitHub Pages

The intended repository is `j346huan/DoYourExercise`. Once it exists, select **Settings → Pages → Source → GitHub Actions**. The included workflow publishes the `site-dist/` artifact, with the correct repository base path. The expected address is `https://j346huan.github.io/DoYourExercise/`.

For an equivalent local production build in PowerShell:

```powershell
$env:SITE_BASE_PATH = '/DoYourExercise'
npm run build
```

For a custom domain or a root user site, build with an empty `SITE_BASE_PATH` and adjust the workflow accordingly. Hash routes and tag-named redirect pages work on static GitHub Pages without a server or rewrite rules. There is no hosted database or server-side upload endpoint.

## Contributions and future submissions

The initial workflow is reviewed GitHub pull requests. The repository includes an issue form for new books, unlisted exercises, and corrections. A direct web submission system is intentionally deferred. When added, it should preserve this file format and use a review process before publishing contributions.

## Assets

- Original sample covers were generated for Do Your Exercise.
- Atiyah–Macdonald cover: CRC Press / Taylor & Francis, [publisher page](https://www.routledge.com/Introduction-To-Commutative-Algebra/Atiyah-MacDonald/p/book/9780367091286).
- Hartshorne cover: Springer Nature, [publisher page](https://link.springer.com/book/10.1007/978-1-4757-3849-0).
- Publisher cover art remains owned by the respective rights holders; no open license is asserted.
- Typesetting uses KaTeX; interface icons use Lucide.

