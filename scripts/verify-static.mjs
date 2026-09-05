import assert from 'node:assert/strict';
import { readFileSync, existsSync } from 'node:fs';
import path from 'node:path';
const base = process.env.SITE_BASE_PATH || '';
const html = readFileSync('site-dist/index.html', 'utf8');
const urls = [...html.matchAll(/(?:src|href)="([^"]+)"/g)]
  .map((m) => m[1])
  .filter((u) => u.startsWith(base + '/'));
for (const url of urls) {
  const local = path.join('site-dist', url.slice(base.length).split('?')[0]);
  assert.ok(existsSync(local), `Missing page resource ${url}`);
}
const catalog = JSON.parse(readFileSync('site-dist/catalog.json', 'utf8'));
for (const p of catalog.problems) {
  for (const file of p.files)
    assert.ok(existsSync(path.join('site-dist', p.sourcePath, file)));
  assert.ok(existsSync(`site-dist/exercises/${p.slug}/index.html`));
}
for (const b of catalog.books)
  if (b.cover) assert.ok(existsSync(`site-dist/${b.cover}`));
assert.ok(existsSync('site-dist/.nojekyll'));
assert.ok(!existsSync('site-dist/server'));
console.log(
  `Static artifact verified: ${urls.length} linked assets, ${catalog.problems.length} exercise pages, and all separate source files.`,
);
console.log(
  'Root-relative links: ' +
    [...html.matchAll(/(?:src|href)="(\/(?!\/)[^"]+)"/g)]
      .map((m) => m[1])
      .filter((u) => !u.startsWith(base + '/'))
      .join(', '),
);

