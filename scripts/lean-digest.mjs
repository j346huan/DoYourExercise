import { readdir, readFile } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import path from 'node:path';
export async function leanProjectDigest() {
  const paths = ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json'];
  async function walk(dir) {
    for (const item of await readdir(dir, { withFileTypes: true })) {
      const p = path.join(dir, item.name);
      if (item.isDirectory()) await walk(p);
      else if (item.name === 'proof.lean') paths.push(p);
    }
  }
  await walk('content');
  const hash = createHash('sha256');
  for (const p of paths.sort()) {
    const source = await readFile(p).catch((e) => {
      if (e.code === 'ENOENT') return Buffer.from('absent');
      throw e;
    });
    hash.update(p.replaceAll('\\', '/') + '\0');
    hash.update(source);
    hash.update('\0');
  }
  return hash.digest('hex');
}
