import { readFile, writeFile } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { leanProjectDigest } from './lean-digest.mjs';
const prepare = spawnSync(
  process.execPath,
  ['scripts/build-content.mjs', '--prepare-lean'],
  { stdio: 'inherit' },
);
if (prepare.status !== 0) process.exit(1);
const before = await leanProjectDigest();
const result = spawnSync('lake', ['build'], {
  stdio: 'inherit',
  shell: process.platform === 'win32',
});
if (result.error || result.status !== 0) {
  console.error(
    'Lean check failed or Lake is not installed. No verification records were written.',
  );
  process.exit(1);
}
const projectDigest = await leanProjectDigest();
if (before !== projectDigest)
  throw Error('Lean inputs changed during compilation; rerun the check.');
const catalog = JSON.parse(await readFile('public/catalog.json', 'utf8'));
const toolchain = (await readFile('lean-toolchain', 'utf8')).trim();
for (const p of catalog.problems.filter((p) =>
  p.files.includes('proof.lean'),
)) {
  const source = await readFile(`${p.sourcePath}/proof.lean`, 'utf8');
  const sha256 = createHash('sha256').update(source).digest('hex');
  await writeFile(
    `${p.sourcePath}/verification.json`,
    JSON.stringify(
      {
        result: 'passed',
        sha256,
        projectDigest,
        toolchain,
        checkedAt: new Date().toISOString(),
      },
      null,
      2,
    ) + '\n',
  );
}
console.log(
  'Lean compiled successfully. Verification records written; set status to formalized after reviewing the proof.',
);
