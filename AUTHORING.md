# Adding solutions

## Files

Create or update the exercise folder under `content/<BookID>/`. Use the book ID followed by the exercise number, replacing dots with dashes: `content/Atiyah69/Atiyah69-1-1/` for `Atiyah69,1.1`, or `<BookID>-<chapter>-<section>-<problem>` when sections are numbered.

Add these files:

- `statement.tex`: the question.
- `proof.tex`: the solution.
- `meta.json`: the exercise metadata.

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

Use `\exref{1.1}` for a reference within the same book and `\exref{Atiyah69,1.1}` for another book. List referenced exercises in `dependencies` using their full identities, such as `"Atiyah69,1.1"`.

## Lean formalizations

Add `proof.lean` and its explanation in `translation.tex` to the exercise folder. Set the `lean` field to the corresponding module:

```json
"lean": {
  "module": "LeanExercises.Atiyah69.Ex_1_1",
  "verified": false
}
```

Import Mathlib or earlier exercise modules as needed. Generate the modules and check the proof:

```sh
npm run lean:prepare
npm run lean:check
```

After a successful check, set `status` to `formalized`. The check generates `verification.json`; rerun it after editing Lean code or dependencies.

## Books and chapters

Add a new chapter or section to the book's `book.json` before adding its exercises. To add a book, create `content/<BookID>/book.json` with its ID, title, authors, year, cover, chapters, and publication details, following an existing book's format.

## Preview and publish

```sh
npm run content:build
npm test
npm run dev
```

Commit the files in `content/` and push to `main` to publish.
