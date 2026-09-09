import { readdir, readFile } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import path from 'node:path';

export const normalizeLeanSource = (source) =>
  source.replace(/^\uFEFF/, '').replace(/\r\n?/g, '\n');

export const leanSourceDigest = (source) =>
  createHash('sha256').update(normalizeLeanSource(source)).digest('hex');

// This checks recorded provenance only. Lean compilation happens outside this repository.
export async function leanProjectDigest(repoRoot = process.cwd()) {
  const paths = [];
  async function walk(dir) {
    for (const entry of await readdir(path.join(repoRoot, dir), { withFileTypes: true })) {
      const relative = path.posix.join(dir, entry.name);
      if (entry.isDirectory()) await walk(relative);
      else if (entry.name === 'proof.lean') paths.push(relative);
    }
  }
  await walk('content');
  const hash = createHash('sha256');
  for (const relative of paths.sort()) {
    const source = normalizeLeanSource(await readFile(path.join(repoRoot, relative), 'utf8'));
    hash.update(relative + '\0' + source + '\0');
  }
  return hash.digest('hex');
}

export function validLeanVerification(record, source, projectDigest) {
  return !!(
    record && record.result === 'passed' &&
    record.sha256 === leanSourceDigest(source) &&
    record.projectDigest === projectDigest &&
    /^leanprover\/lean4:v[\w.-]+$/.test(record.toolchain) &&
    record.mathlib?.git === 'https://github.com/leanprover-community/mathlib4.git' &&
    /^[a-f0-9]{40}$/.test(record.mathlib?.rev) &&
    typeof record.checker?.command === 'string' && record.checker.command.trim() &&
    typeof record.checkedAt === 'string' && /^\d{4}-\d{2}-\d{2}T/.test(record.checkedAt) && Number.isFinite(Date.parse(record.checkedAt)) &&
    ['checkedDeclarations', 'axioms'].every((key) => record[key] === undefined ||
      (Array.isArray(record[key]) && record[key].every((entry) => typeof entry === 'string' && entry.trim())))
  );
}
