import { readdir, readFile, writeFile, mkdir, rm } from 'node:fs/promises';
import path from 'node:path';
import { createHash } from 'node:crypto';
import { leanProjectDigest } from './lean-digest.mjs';
const projectDigest = await leanProjectDigest();
const root = process.cwd();
const readJSON = async (p) =>
  JSON.parse((await readFile(p, 'utf8')).replace(/^\uFEFF/, ''));
const write = async (p, data) => {
  await mkdir(path.dirname(p), { recursive: true });
  await writeFile(p, data);
};
const identifier = /^[A-Za-z][A-Za-z0-9]*$/;
const part = /^[A-Za-z0-9]+$/;
const books = [];
const problems = [];
const generated = [];
const publicContent = path.join(root, 'public/content');
const leanRoot = path.join(root, 'LeanExercises');
// Only remove known generated directories inside this checkout.
for (const dir of [
  publicContent,
  leanRoot,
  path.join(root, 'public/exercises'),
]) {
  if (!dir.startsWith(root + path.sep)) throw Error('Unsafe output path');
  await rm(dir, { recursive: true, force: true });
}
for (const folder of (await readdir('content', { withFileTypes: true }))
  .filter((x) => x.isDirectory())
  .sort((a, b) => a.name.localeCompare(b.name))) {
  const base = path.join('content', folder.name);
  const book = await readJSON(path.join(base, 'book.json'));
  if (!identifier.test(book.id) || folder.name !== book.id)
    throw Error(`Invalid book ID: ${folder.name}`);
  if (books.some((x) => x.id === book.id))
    throw Error(`Duplicate book ID ${book.id}`);
  if (!book.title || !book.authors || !Array.isArray(book.chapters))
    throw Error(`Invalid book metadata: ${book.id}`);
  const chapterIds = new Set();
  for (const ch of book.chapters) {
    if (!part.test(ch.id) || chapterIds.has(ch.id))
      throw Error(`Invalid/duplicate chapter ${book.id}:${ch.id}`);
    chapterIds.add(ch.id);
    const sectionIds = new Set();
    for (const s of ch.sections || []) {
      if (!part.test(s.id) || sectionIds.has(s.id))
        throw Error(`Invalid/duplicate section ${s.id}`);
      sectionIds.add(s.id);
    }
  }
  books.push(book);
  await write(
    path.join(publicContent, book.id, 'book.json'),
    JSON.stringify(book, null, 2),
  );
  for (const dir of (await readdir(base, { withFileTypes: true })).filter((x) =>
    x.isDirectory(),
  )) {
    const source = path.join(base, dir.name);
    const meta = await readJSON(path.join(source, 'meta.json'));
    meta.dependencies ??= [];
    if (
      !Array.isArray(meta.dependencies) ||
      meta.dependencies.some((d) => typeof d !== 'string')
    )
      throw Error('Dependencies must be a list of reference strings');
    const ch = book.chapters.find((x) => x.id === meta.chapter);
    if (!ch) throw Error(`Unknown chapter in ${dir.name}`);
    if (meta.section && !ch.sections?.some((x) => x.id === meta.section))
      throw Error(`Unknown section in ${dir.name}`);
    if (ch.sections?.length && !meta.section)
      throw Error(`Missing section in ${dir.name}`);
    if (!part.test(meta.number) || typeof meta.title !== 'string')
      throw Error(`Invalid exercise metadata in ${dir.name}`);
    const tag = [meta.chapter, meta.section, meta.number]
      .filter(Boolean)
      .join('.');
    const slug = `${book.id}-${tag.replaceAll('.', '-')}`;
    if (meta.tag !== tag || dir.name !== slug)
      throw Error(`Expected folder ${slug} and tag ${tag}`);
    const files = {};
    for (const name of [
      'statement.tex',
      'proof.tex',
      'proof.lean',
      'translation.tex',
    ]) {
      try {
        const text = (await readFile(path.join(source, name), 'utf8')).replace(
          /^\uFEFF/,
          '',
        );
        if (text.trim() || name === 'statement.tex') {
          files[name] = text;
          await write(path.join(publicContent, book.id, slug, name), text);
        }
      } catch (e) {
        if (e.code !== 'ENOENT') throw e;
      }
    }
    if (!('statement.tex' in files))
      throw Error(`${slug} has no statement.tex`);
    if (!['unsolved', 'solved', 'formalized'].includes(meta.status))
      throw Error(`Invalid status for ${slug}`);
    if (meta.status !== 'unsolved' && !files['proof.tex'])
      throw Error(`${slug} needs proof.tex`);
    if (
      meta.status === 'unsolved' &&
      (files['proof.lean'] ||
        (files['proof.tex'] && meta.coverage !== 'partial'))
    )
      throw Error(
        `${slug}: only partial notes may accompany an unsolved exercise`,
      );
    if (
      meta.coverage === 'partial' &&
      (meta.status !== 'unsolved' || !files['proof.tex'])
    )
      throw Error(`${slug}: partial notes need proof.tex and unsolved status`);
    if (meta.coverage && !['proof', 'partial', 'empty'].includes(meta.coverage))
      throw Error(`Invalid coverage for ${slug}`);
    if (
      meta.coverage === 'empty' &&
      (meta.status !== 'unsolved' || files['proof.tex'])
    )
      throw Error(`${slug}: empty entries must be unsolved without proof.tex`);
    if (meta.source) {
      const url = new URL(meta.source.url);
      if (
        !['http:', 'https:'].includes(url.protocol) ||
        !meta.source.label ||
        !Array.isArray(meta.source.pages) ||
        !meta.source.pages.length ||
        meta.source.pages.some((page) => !Number.isInteger(page) || page < 1) ||
        !['summary', 'missing'].includes(meta.source.statement)
      )
        throw Error(`Invalid source attribution for ${slug}`);
    }
    if (files['proof.lean']) {
      const leanModule = `LeanExercises.${book.id}.Ex_${tag.replaceAll('.', '_')}`;
      if (meta.lean?.module !== leanModule)
        throw Error(`${slug} must use module ${leanModule}`);
      if (!files['translation.tex'])
        throw Error(`${slug} needs a Lean translation`);
      if (/\b(sorry|admit|axiom)\b/.test(files['proof.lean']))
        throw Error(`${slug}: proof placeholders are not accepted`);
      await write(
        path.join(root, ...leanModule.split('.')) + '.lean',
        files['proof.lean'],
      );
      generated.push(leanModule);
    }
    if (
      meta.status === 'formalized' &&
      !process.argv.includes('--prepare-lean')
    ) {
      const evidence = await readJSON(
        path.join(source, 'verification.json'),
      ).catch(() => null);
      const digest = createHash('sha256')
        .update(files['proof.lean'] || '')
        .digest('hex');
      if (
        !files['proof.lean'] ||
        !evidence ||
        evidence.sha256 !== digest ||
        evidence.result !== 'passed' ||
        evidence.projectDigest !== projectDigest
      )
        throw Error(
          `${slug}: formalized requires matching verification.json from npm run lean:check`,
        );
    }
    const record = {
      ...meta,
      id: `${book.id},${tag}`,
      slug,
      book: book.id,
      bookTitle: book.title,
      chapterTitle: ch.title,
      sectionTitle:
        ch.sections?.find((x) => x.id === meta.section)?.title || null,
      statement: files['statement.tex'],
      files: Object.keys(files),
      sourcePath: `content/${book.id}/${slug}`,
    };
    problems.push(record);
    await write(
      path.join(publicContent, book.id, slug, 'meta.json'),
      JSON.stringify(meta, null, 2),
    );
    // Human-shareable static page named after the exercise tag; works under any Pages subpath.
    await write(
      `public/exercises/${slug}/index.html`,
      `<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width"><title>Do Your Exercise — ${slug}</title><meta http-equiv="refresh" content="0;url=../../#/problem/${slug}"><a href="../../#/problem/${slug}">Open ${slug}</a></html>`,
    );
  }
}
for (const p of problems) {
  const files = await Promise.all(
    p.files
      .filter((f) => f.endsWith('.tex'))
      .map((f) => readFile(path.join(p.sourcePath, f), 'utf8')),
  );
  for (const content of files)
    for (const match of content.matchAll(/\\exref\{([^}]+)\}/g)) {
      const ref = match[1].replace(':', ',');
      const id = ref.includes(',') ? ref : `${p.book},${ref}`;
      if (!problems.some((x) => x.id === id))
        throw Error(`Broken reference ${ref} in ${p.slug}`);
    }
  for (const ref of p.dependencies || [])
    if (!problems.some((x) => x.id === ref))
      throw Error(`Unknown dependency ${ref}`);
}
books.sort(
  (a, b) =>
    ['Atiyah69', 'Hartshorne77'].indexOf(a.id) -
    ['Atiyah69', 'Hartshorne77'].indexOf(b.id),
);
problems.sort((a, b) => a.id.localeCompare(b.id, undefined, { numeric: true }));
await write(
  'LeanExercises.lean',
  generated.map((m) => `import ${m}`).join('\n') + '\n',
);
await write(
  'public/catalog.json',
  JSON.stringify({ version: 1, books, problems }, null, 2),
);
console.log(
  `Indexed ${books.length} books, ${problems.length} exercises. Statements indexed separately; proof files loaded on demand.`,
);
