import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, mkdir, writeFile, readFile, rm, access } from 'node:fs/promises';
import { execFileSync } from 'node:child_process';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { leanProjectDigest, leanSourceDigest, validLeanVerification } from '../scripts/lean-digest.mjs';

const builder = fileURLToPath(new URL('../scripts/build-content.mjs', import.meta.url));
const proof = 'import Mathlib\n\nnamespace Test26.Ex_1_1\ntheorem identity (n : Nat) : n = n := rfl\nend Test26.Ex_1_1\n';
const directory = 'content/Test26/Test26-1-1';
const metadata = {
  tag: '1.1', chapter: '1', section: null, number: '1', title: '', status: 'solved',
  lean: { module: 'LeanExercises.Test26.Ex_1_1', verified: true },
};

async function fixture(t) {
  const root = await mkdtemp(path.join(os.tmpdir(), 'exercise-lean-record-'));
  t.after(async () => { await rm(root, { recursive: true, force: true }); });
  const write = async (relative, source) => {
    const destination = path.join(root, relative);
    await mkdir(path.dirname(destination), { recursive: true });
    await writeFile(destination, source);
  };
  await write('content/Test26/book.json', JSON.stringify({
    id: 'Test26', title: 'Test book', authors: 'Test author', chapters: [{ id: '1', title: 'Chapter 1' }],
  }));
  await write(`${directory}/meta.json`, JSON.stringify(metadata));
  await write(`${directory}/proof.tex`, 'The proof.');
  await write(`${directory}/proof.lean`, proof);
  return { root, write, build: () => execFileSync(process.execPath, [builder], { cwd: root, stdio: 'pipe' }) };
}

async function evidence(root) {
  return {
    result: 'passed', sha256: leanSourceDigest(proof), projectDigest: await leanProjectDigest(root),
    toolchain: 'leanprover/lean4:v4.24.0',
    mathlib: { git: 'https://github.com/leanprover-community/mathlib4.git', rev: 'f897ebcf72cd16f89ab4577d0c826cd14afaafc7' },
    checker: { command: 'lake build LeanExercises' }, checkedAt: '2026-09-08T12:00:00.000Z',
    checkedDeclarations: ['Test26.Ex_1_1.identity'], axioms: [],
  };
}

test('website builds display Lean files without generating a Lean project or trusting metadata flags', async (t) => {
  const { root, build } = await fixture(t);
  build();
  for (const generated of ['LeanExercises', 'LeanExercises.lean', 'lakefile.toml', 'lean-toolchain', '.lake'])
    await assert.rejects(access(path.join(root, generated)));
  const catalog = JSON.parse(await readFile(path.join(root, 'public/catalog.json'), 'utf8'));
  assert.equal(catalog.problems[0].lean.verified, false);
  assert.equal(catalog.problems[0].lean.verification, undefined);
  assert.deepEqual(catalog.problems[0].files, ['proof.tex', 'proof.lean']);
});

test('matching external verification is displayed and downloadable without a translation file', async (t) => {
  const { root, write, build } = await fixture(t);
  const record = await evidence(root);
  await write(`${directory}/verification.json`, JSON.stringify(record));
  await write(`${directory}/meta.json`, JSON.stringify({ ...metadata, status: 'formalized' }));
  build();
  const catalog = JSON.parse(await readFile(path.join(root, 'public/catalog.json'), 'utf8'));
  assert.equal(catalog.problems[0].lean.verified, true);
  assert.deepEqual(catalog.problems[0].lean.verification, record);
  assert.ok(catalog.problems[0].files.includes('verification.json'));
  assert.equal(await readFile(path.join(root, 'public', directory, 'verification.json'), 'utf8'), JSON.stringify(record));
});

test('editing any canonical Lean dependency invalidates recorded verification', async (t) => {
  const { root, write, build } = await fixture(t);
  const second = 'content/Test26/Test26-1-2';
  await write(`${second}/meta.json`, JSON.stringify({ ...metadata, tag: '1.2', number: '2', lean: { module: 'LeanExercises.Test26.Ex_1_2', verified: false } }));
  await write(`${second}/proof.tex`, 'Another proof.');
  await write(`${second}/proof.lean`, 'import LeanExercises.Test26.Ex_1_1\n');
  await write(`${directory}/verification.json`, JSON.stringify(await evidence(root)));
  await write(`${directory}/meta.json`, JSON.stringify({ ...metadata, status: 'formalized' }));
  build();
  await write(`${second}/proof.lean`, 'import LeanExercises.Test26.Ex_1_1\n-- Changed dependency.\n');
  assert.throws(build, /matching external verification record/);
});

test('Lean evidence hashes normalize line endings and exclude machine-specific configuration', async (t) => {
  const { root, write } = await fixture(t);
  const before = await leanProjectDigest(root);
  assert.equal(leanSourceDigest(proof), leanSourceDigest('\uFEFF' + proof.replaceAll('\n', '\r\n')));
  await write(`${directory}/proof.lean`, proof.replaceAll('\n', '\r\n'));
  assert.equal(await leanProjectDigest(root), before);
  await write('lakefile.toml', 'temporary external configuration');
  await write('lean-toolchain', 'different local toolchain');
  assert.equal(await leanProjectDigest(root), before);
  await write(`${directory}/proof.lean`, proof + '-- Edited.\n');
  assert.notEqual(await leanProjectDigest(root), before);
});

test('verification records require compiler and dependency provenance with valid optional audit fields', async (t) => {
  const { root } = await fixture(t);
  const record = await evidence(root);
  assert.equal(validLeanVerification(record, proof, record.projectDigest), true);
  for (const changes of [
    { result: 'failed' }, { sha256: '0'.repeat(64) }, { projectDigest: '0'.repeat(64) },
    { toolchain: null }, { mathlib: { ...record.mathlib, rev: 'master' } },
    { checker: { command: '' } }, { checkedAt: 'unknown' }, { axioms: [42] },
  ]) assert.equal(validLeanVerification({ ...record, ...changes }, proof, record.projectDigest), false);
});


test('display-only builds accept checked Lean comments containing mathematical axiom terminology', async (t) => {
  const { root, write, build } = await fixture(t);
  const source = proof + '-- This proof does not use the axiom of choice.\n';
  await write(`${directory}/proof.lean`, source);
  const record = { ...(await evidence(root)), sha256: leanSourceDigest(source) };
  await write(`${directory}/verification.json`, JSON.stringify(record));
  await write(`${directory}/meta.json`, JSON.stringify({ ...metadata, status: 'formalized' }));
  build();
  const catalog = JSON.parse(await readFile(path.join(root, 'public/catalog.json'), 'utf8'));
  assert.equal(catalog.problems[0].lean.verified, true);
  assert.equal(await readFile(path.join(root, 'public', directory, 'proof.lean'), 'utf8'), source);
});
