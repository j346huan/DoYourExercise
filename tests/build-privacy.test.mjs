import test from 'node:test';
import assert from 'node:assert/strict';
import {
  mkdtempSync,
  mkdirSync,
  writeFileSync,
  readFileSync,
  readdirSync,
  unlinkSync,
  rmSync,
} from 'node:fs';
import { execFileSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const builder = fileURLToPath(
  new URL('../scripts/build-content.mjs', import.meta.url),
);
test('builds exclude local statements and also work without them', () => {
  const prefix = path.join(tmpdir(), 'exercise-privacy-test-');
  const root = mkdtempSync(prefix);
  const folder = 'content/Test26/Test26-1-1';
  const write = (name, value) => {
    const destination = path.join(root, name);
    mkdirSync(path.dirname(destination), { recursive: true });
    writeFileSync(destination, value);
  };
  const snapshot = () =>
    Object.fromEntries(
      readdirSync(path.join(root, 'public'), {
        recursive: true,
        withFileTypes: true,
      })
        .filter((entry) => entry.isFile())
        .map((entry) => {
          const name = path.join(entry.parentPath, entry.name);
          return [path.relative(root, name), readFileSync(name, 'utf8')];
        }),
    );
  try {
    write(
      'content/Test26/book.json',
      JSON.stringify({
        id: 'Test26',
        title: 'Test book',
        authors: 'Test author',
        chapters: [{ id: '1', title: 'Chapter 1' }],
      }),
    );
    const meta = {
      tag: '1.1',
      chapter: '1',
      section: null,
      number: '1',
      title: '',
      status: 'solved',
    };
    write(`${folder}/meta.json`, JSON.stringify(meta));
    write(`${folder}/proof.tex`, 'The solution.');
    const privateText = String.raw`PRIVATE_STATEMENT_SENTINEL_7b849c \exref{missing}`;
    write(`${folder}/statement.tex`, privateText);
    write(`public/${folder}/statement.tex`, privateText);
    write('public/catalog.json', JSON.stringify({ statement: privateText }));
    const build = () =>
      execFileSync(process.execPath, [builder], { cwd: root, stdio: 'pipe' });
    build();
    const withLocalStatement = snapshot();
    assert.ok(
      Object.keys(withLocalStatement).every(
        (name) => !name.endsWith('statement.tex'),
      ),
    );
    assert.ok(
      Object.values(withLocalStatement).every(
        (text) => !text.includes(privateText),
      ),
    );
    assert.equal(
      readFileSync(path.join(root, folder, 'statement.tex'), 'utf8'),
      privateText,
    );
    const catalog = JSON.parse(
      withLocalStatement[path.join('public', 'catalog.json')],
    );
    assert.ok(!('statement' in catalog.problems[0]));
    assert.deepEqual(catalog.problems[0].files, ['proof.tex']);
    unlinkSync(path.join(root, folder, 'statement.tex'));
    build();
    assert.deepEqual(snapshot(), withLocalStatement);
    write(
      `${folder}/meta.json`,
      JSON.stringify({ ...meta, statement: privateText }),
    );
    assert.throws(build, /statement must not be stored in meta.json/);
  } finally {
    assert.ok(path.resolve(root).startsWith(path.resolve(prefix)));
    rmSync(root, { recursive: true, force: true });
  }
});
