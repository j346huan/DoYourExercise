import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import katex from 'katex';
import { parseTex } from '../lib/tex.mjs';
import { resolveReference } from '../lib/core.mjs';

const { problems } = JSON.parse(readFileSync('public/catalog.json', 'utf8'));
function* walk(nodes) {
  for (const node of nodes) {
    yield node;
    if (node.children) yield* walk(node.children);
    for (const item of node.items || []) yield* walk(item);
  }
}

test('every published TeX fragment typesets with the website renderer', () => {
  let expressions = 0;
  for (const problem of problems) {
    for (const file of problem.files.filter((file) => file.endsWith('.tex'))) {
      const source = readFileSync(`${problem.sourcePath}/${file}`, 'utf8');
      for (const node of walk(parseTex(source))) {
        const context = `${problem.id}/${file}: ${node.value}`;
        if (node.kind === 'math') {
          assert.doesNotThrow(
            () =>
              katex.renderToString(node.value, {
                displayMode: node.display,
                throwOnError: true,
                trust: false,
                strict: 'warn',
                maxExpand: 1000,
              }),
            context,
          );
          expressions++;
        }
        if (node.kind === 'text') {
          assert.doesNotMatch(node.value, /\\[a-zA-Z]+|\\\[|\\\]/, context);
        }
        if (node.kind === 'reference') {
          const id = resolveReference(node.value, problem.book);
          assert.ok(
            problems.some((p) => p.id === id),
            context,
          );
        }
      }
    }
  }
  assert.ok(expressions > 0, 'The collection contains rendered mathematics');
});

test('the published catalog contains statements but no proof contents', () => {
  for (const problem of problems) {
    const statement = readFileSync(
      `${problem.sourcePath}/statement.tex`,
      'utf8',
    );
    assert.equal(problem.statement, statement);
    for (const key of ['proof', 'translation', 'leanCode'])
      assert.equal(problem[key], undefined);
    for (const file of problem.files.filter((f) => f !== 'statement.tex')) {
      assert.equal(
        readFileSync(`public/${problem.sourcePath}/${file}`, 'utf8'),
        readFileSync(`${problem.sourcePath}/${file}`, 'utf8'),
      );
    }
  }
});
