# Contributing to Do Your Exercise

The sample notebooks are original demonstrations. Add real textbook work only after checking its numbering, edition, statement, and source. Keep new submissions in a pull request for review.

## A new book

Create `content/Author26/book.json`:

```json
{
  "id": "Author26",
  "title": "Book title",
  "shortTitle": "Short title",
  "authors": "Author Name",
  "year": 2026,
  "description": "About this collection.",
  "kind": "textbook",
  "cover": "covers/author26.jpg",
  "coverCredit": "Cover attribution",
  "chapters": [
    {
      "id": "1",
      "title": "Chapter title",
      "sections": [{ "id": "1", "title": "Section title" }]
    }
  ]
}
```

Add the cover file to `public/covers/`. A missing cover can be represented by `null`; the book remains available through a companion card. Omit `sections` entirely for a chapter without sections. Letter and Roman-numeral chapter IDs are supported. Use the first author's surname plus publication year for IDs and add a suffix only when an ID would collide.

## A new exercise

For a chapter with sections, create `content/Author26/Author26-1-1-1/meta.json`:

```json
{
  "tag": "1.1.1",
  "chapter": "1",
  "section": "1",
  "number": "1",
  "title": "A descriptive exercise title",
  "tags": ["commutative-algebra", "ideals"],
  "status": "unsolved",
  "sample": false,
  "updated": "2026-09-05",
  "dependencies": [],
  "lean": null
}
```

Place only the statement in `statement.tex`. For a chapter without sections, use `"section": null`, tag `1.1`, and folder `Author26-1-1`.

For a natural solution, add `proof.tex` and set `status` to `solved`. To include Lean code, also add `proof.lean`, `translation.tex`, and metadata:

```json
"lean": {
  "module": "LeanExercises.Author26.Ex_1_1_1",
  "verified": false
}
```

The module name must use the exact book ID and exercise numbering with underscores. Dependencies are full exercise identities, for example `"dependencies": ["Notebook26,1.1.1"]`. The website links them and uses them to show related exercises. Lean imports themselves go in `proof.lean`.

A solved exercise may have no Lean formalization. An unsolved exercise must not include a completed proof. `formalized` requires all proof files plus current evidence produced by `npm run lean:check`.

## TeX fragments

Use UTF-8 TeX **fragments**, without `\documentclass`, packages, custom macro definitions, bibliography commands, or a full document preamble. The website is not a complete TeX compiler.

Supported prose syntax:

- Plain paragraphs separated by a blank line.
- Inline math with `$...$` or `\(...\)`.
- Display math with `\[...\]`, `$$...$$`, `equation`, `align`, or `gather` environments, including starred variants.
- Nested `\textbf{...}`, `\emph{...}`, and `\textit{...}`; math and references work inside them.
- Literal code with `\texttt{...}`.
- `enumerate` and `itemize` with `\item` (simple lists; nested list environments are not supported).
- `%` comments and escaped special characters such as `\%`, `\$`, and `\_`.
- Same-book links: `\exref{1.1.1}`.
- Cross-book links: `\exref{Notebook26,1.1.1}`.

Math uses KaTeX's supported commands. Unsupported expressions remain visible as highlighted source instead of silently disappearing. Unknown prose commands remain visible as text. Arbitrary HTML is never interpreted, and trusted HTML commands in math are disabled.

Example `proof.tex`:

```tex
By \exref{1.1.1}, $n+0=n$. Hence
\[
(n+0)+m=n+m.
\]
This proves the claim.
```

## Review and validation

```sh
npm run content:build
npm test
npm run typecheck
npm run build
```

Check the exercise page and its references. The validator rejects inconsistent folder tags, unknown chapters or sections, broken references, missing statements, and invalid proof status. Source indexing is automatic on build; committing the original files is enough for the publishing workflow.

For Lean, follow the pinned-toolchain setup in the README and run `npm run lean:check`. Do not manually create or edit compilation evidence. If any canonical Lean file, toolchain, Lake configuration, or dependency manifest changes, recompile before retaining a formalized status. Verify that the Lean theorem actually matches the mathematical statement and that the translation faithfully explains the code.

Never commit API tokens, passwords, `.env` files, `.lake/`, `node_modules/`, `.tools/`, or generated static output. Direct browser uploads and anonymous submissions are planned for a future version.
