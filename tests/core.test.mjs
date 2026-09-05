import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import katex from 'katex';
import {
  searchProblems,
  resolveReference,
  routeFromHash,
  restoreWorkspace,
  navigateWorkspace,
  closeWorkspaceTab,
} from '../lib/core.mjs';
const { problems, books, tex } = JSON.parse(
  readFileSync(new URL('./fixtures/catalog.json', import.meta.url), 'utf8'),
);
test('same-book and cross-book references resolve to unique exercises', () => {
  assert.equal(resolveReference('1.1.1', 'Notebook26'), 'Notebook26,1.1.1');
  assert.equal(
    resolveReference('Notebook26:1.2.1', 'Geometry26'),
    'Notebook26,1.2.1',
  );
  assert.equal(new Set(problems.map((p) => p.id)).size, problems.length);
});
test('fuzzy search tolerates spelling errors', () => {
  assert.ok(
    searchProblems(problems, 'parenthess').some((p) => p.tag === '1.2.1'),
  );
  assert.equal(
    searchProblems(problems, 'zero on the rght')[0].title,
    'Zero on the right',
  );
});
test('search combines text, book, and status filters', () => {
  const found = searchProblems(
    problems,
    'parentheses book:Notebook26 status:solved',
  );
  assert.equal(found.length, 1);
  assert.equal(found[0].tag, '1.2.1');
  assert.equal(searchProblems(problems, 'status:unsolved').length, 2);
});
test('search finds chapter tags and cross-book citation syntax', () => {
  assert.ok(
    searchProblems(problems, '(Notebook26,1.1.1)').some(
      (p) => p.id === 'Notebook26,1.1.1',
    ),
  );
});
test('internal tabs preserve earlier pages and closing the active tab picks its neighbor', () => {
  const home = { tabs: [{ id: 'a', route: '/' }], active: 'a' };
  const opened = navigateWorkspace(
    home,
    '/problem/Notebook26-1-1-1',
    true,
    'b',
  );
  assert.equal(opened.tabs[0].route, '/');
  assert.equal(opened.active, 'b');
  const replaced = navigateWorkspace(
    opened,
    '/problem/Notebook26-1-1-2',
    false,
    'unused',
  );
  assert.equal(replaced.tabs.length, 2);
  assert.equal(replaced.tabs[1].route, '/problem/Notebook26-1-1-2');
  assert.deepEqual(closeWorkspaceTab(replaced, 'b'), home);
  assert.deepEqual(closeWorkspaceTab(home, 'a'), home);
});
test('tab persistence rejects malformed records and invalid routes', () => {
  assert.equal(restoreWorkspace('garbage'), null);
  assert.equal(restoreWorkspace('{"tabs":[]}'), null);
  assert.equal(routeFromHash('#%ZZ'), '/not-found');
  assert.equal(
    routeFromHash('#/problem/Notebook26-1-1-1'),
    '/problem/Notebook26-1-1-1',
  );
});
test('catalog omits statements and does not inline proofs or Lean code', () => {
  for (const p of problems) {
    assert.ok(!('statement' in p));
    assert.ok(!p.files.includes('statement.tex'));
    assert.ok(!('proof' in p));
    assert.ok(!('translation' in p));
    assert.ok(!('code' in p));
    assert.ok(Array.isArray(p.files));
  }
  assert.equal(books.find((b) => b.id === 'Atiyah69').chapters.length, 0);
  assert.equal(books.find((b) => b.id === 'Hartshorne77').chapters.length, 0);
});
test('every sample mathematical expression typesets successfully', () => {
  function check(nodes) {
    for (const n of nodes) {
      if (n.kind === 'math')
        assert.doesNotThrow(() =>
          katex.renderToString(n.value, {
            displayMode: n.display,
            throwOnError: true,
            trust: false,
          }),
        );
      if (n.children) check(n.children);
      if (n.items) n.items.forEach(check);
    }
  }
  for (const text of tex) check(parseTex(text));
});
test('Lean examples are not advertised as formalized without compiler evidence', () => {
  for (const p of problems.filter((p) => p.lean)) {
    assert.equal(p.status, 'solved');
    assert.equal(p.lean.verified, false);
    assert.match(
      p.lean.module,
      /^LeanExercises\.[A-Za-z0-9]+\.Ex_[A-Za-z0-9_]+$/,
    );
  }
});
import { parseTex } from '../lib/tex.mjs';
test('nested TeX formatting preserves mathematical expressions and references', () => {
  const parsed = parseTex(
    String.raw`\textbf{Claim: $n+0=n$. \emph{See \exref{1.1.1}}}`,
  );
  assert.equal(parsed[0].kind, 'bold');
  assert.ok(parsed[0].children.some((n) => n.kind === 'math'));
  const italic = parsed[0].children.find((n) => n.kind === 'italic');
  assert.ok(
    italic.children.some((n) => n.kind === 'reference' && n.value === '1.1.1'),
  );
});
test('TeX environments support numbered lists and aligned displays', () => {
  const parsed = parseTex(
    String.raw`\begin{enumerate}\item First $n$\item Second\end{enumerate}\begin{align*}a&=b\\b&=c\end{align*}`,
  );
  assert.equal(parsed[0].kind, 'list');
  assert.equal(parsed[0].ordered, true);
  assert.equal(parsed[0].items.length, 2);
  assert.equal(parsed[1].kind, 'math');
  assert.doesNotThrow(() =>
    katex.renderToString(parsed[1].value, {
      displayMode: true,
      throwOnError: true,
    }),
  );
});
test('TeX parser preserves literal markup as text and handles escaped delimiters', () => {
  const parsed = parseTex(String.raw`<script>bad</script> Cost: \$5; $n+0=n$`);
  assert.ok(
    parsed.some(
      (n) => n.kind === 'text' && n.value.includes('<script>bad</script>'),
    ),
  );
  assert.equal(parsed.filter((n) => n.kind === 'math').length, 1);
});

test('untitled exercises remain searchable by chapter and reference', () => {
  const untitled = problems.map((p) => ({ ...p, title: '', tags: undefined }));
  assert.ok(
    searchProblems(untitled, 'working with sum book:Notebook26').some(
      (p) => p.id === 'Notebook26,1.1.1',
    ),
  );
  assert.equal(
    searchProblems(untitled, '(Notebook26,1.1.2)')[0].id,
    'Notebook26,1.1.2',
  );
});
