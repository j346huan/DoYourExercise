import { spawnSync } from 'node:child_process';
import { existsSync, writeFileSync, mkdirSync, cpSync, rmSync } from 'node:fs';
import path from 'node:path';
const base = process.env.SITE_BASE_PATH || '';
if (base && !/^\/[A-Za-z0-9_-]+$/.test(base))
  throw Error(
    'SITE_BASE_PATH must be empty or one safe repository path segment',
  );
for (const args of [
  ['scripts/build-content.mjs'],
  ['node_modules/vinext/dist/cli.js', 'build'],
]) {
  const r = spawnSync(process.execPath, args, {
    stdio: 'inherit',
    env: { ...process.env, NEXT_PUBLIC_BASE_PATH: base },
  });
  if (r.status !== 0) process.exit(r.status || 1);
}
const source = [`dist/client${base}`, `out${base}`, 'out', 'dist/client'].find(
  (d) => existsSync(`${d}/index.html`),
);
if (!source) throw Error('Static export index.html was not produced.');
const target = path.resolve('site-dist');
if (target !== path.join(process.cwd(), 'site-dist'))
  throw Error('Unsafe output path');
rmSync(target, { recursive: true, force: true });
mkdirSync(target, { recursive: true });
cpSync(source, target, { recursive: true });
if (existsSync('dist/client/404.html'))
  cpSync('dist/client/404.html', path.join(target, '404.html'));
writeFileSync(path.join(target, '.nojekyll'), '');
console.log(
  `GitHub Pages artifact ready: site-dist/ (base path: ${base || '/'})`,
);
