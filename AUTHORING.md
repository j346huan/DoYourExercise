# Adding solutions

## Files

Create or update the exercise folder under `content/<BookID>/`. Use the book ID followed by the exercise number, replacing dots with dashes: `content/AtiyahMcdonald69/AtiyahMcdonald69-1-1/` for `AtiyahMcdonald69,1.1`, or `<BookID>-<chapter>-<section>-<problem>` when sections are numbered.

Add these files:

- `proof.tex`: the solution.
- `meta.json`: the exercise metadata.

Optionally keep the question in `statement.tex` in the same folder for private reference. This file is ignored by Git and excluded from the website. Do not force-add it to Git.

For a solved exercise:

```json
{
  "tag": "1.1",
  "chapter": "1",
  "section": null,
  "number": "1",
  "title": "",
  "status": "solved",
  "updated": "YYYY-MM-DD",
  "dependencies": [],
  "lean": null,
  "coverage": "proof"
}
```

Replace `updated` with the date of the edit. Set `section` to its number when applicable. Use the textbook's exercise title, or leave `title` empty. For an unsolved exercise, set `status` to `unsolved` and `coverage` to `empty`, and omit `proof.tex`. For an incomplete solution, include `proof.tex` with `status` set to `unsolved` and `coverage` to `partial`.

## TeX and references

Write UTF-8 TeX fragments without a document preamble or custom macro definitions. Use `$...$` for inline mathematics and `\[...\]` for an unnumbered display, with each equation on one source line. Text formatting supports `\textbf{...}`, `\emph{...}`, `\textit{...}`, and `\texttt{...}`; lists support `enumerate` and `itemize`.

Use `\exref{1.1}` for a reference within the same book and `\exref{AtiyahMcdonald69,1.1}` for another book. List referenced exercises in `dependencies` using their full identities, such as `"AtiyahMcdonald69,1.1"`.

## Lean formalizations

Develop and check Lean proofs in the external workspace under `D:\lean`, following `D:\lean\README.md`. Keep temporary proofs, examples, helper projects, Lake configuration, Mathlib, and compiled files there. Add only completed `proof.lean` files and their external `verification.json` records to the exercise folder. `translation.tex` is optional.

Set the `lean` field to the corresponding module:

```json
"lean": {
  "module": "LeanExercises.Hartshorne77.Ex_II_1_1",
  "verified": false
}
```

The module name is `LeanExercises.<BookID>.Ex_<tag>`, replacing dots in the exercise tag with underscores. Import Mathlib or another completed exercise with its exact module name:

```lean
import Mathlib
import LeanExercises.Hartshorne77.Ex_II_1_1
import LeanExercises.AtiyahMcdonald69.Ex_1_1
```

Use a distinct namespace for each exercise and refer to its theorems by their qualified names. Imports do not create namespaces automatically. Record referenced exercises in the metadata `dependencies` as well; metadata references do not create Lean imports. Final proofs must not depend on drafts or private helper modules. Do not include proof placeholders.

The external checker writes `verification.json`, containing the successful result, source and library hashes, Lean toolchain, exact Mathlib commit, commands, and time. It can also record checked declaration names and their axioms. Retain the generated record without editing it. After checking that the formalization covers the exercise, set `status` to `formalized`.

The website derives `lean.verified` from the record and current sources; a metadata flag alone does not establish verification. Changing any final Lean file invalidates records for the library, so run the external verification workflow again before publishing formalized entries. Ordinary website builds only validate and display these records; they do not compile Lean or create a Lean workspace.

## Books and chapters

Add a new chapter or section to the book's `book.json` before adding its exercises. To add a book, create `content/<BookID>/book.json` with its ID, title, authors, year, cover, chapters, and publication details, following an existing book's format.

## Preview and publish

```sh
npm run content:build
npm test
npm run dev
```

Commit the solution and metadata files in `content/` and push to `main` to publish.
