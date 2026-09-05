import Fuse from 'fuse.js';
export function resolveReference(reference, book) {
  const clean = reference
    .trim()
    .replace(/^\(|\)$/g, '')
    .replace(':', ',');
  return clean.includes(',') ? clean : `${book},${clean}`;
}
export function referenceLabel(problem, currentBook) {
  return `(${problem.book === currentBook ? problem.tag : problem.id})`;
}
export function routeFromHash(hash) {
  try {
    const value = decodeURIComponent(hash.replace(/^#/, '') || '/');
    return value === '/' || /^\/problem\/[A-Za-z0-9-]+$/.test(value)
      ? value
      : '/not-found';
  } catch {
    return '/not-found';
  }
}
export function searchProblems(problems, query) {
  const books = [...query.matchAll(/\bbook:([^\s]+)/gi)].map((x) =>
    x[1].toLowerCase(),
  );
  const states = [...query.matchAll(/\bstatus:(\w+)/gi)].map((x) =>
    x[1].toLowerCase(),
  );
  const term = query
    .replace(/\b(?:book|status):[^\s]+/gi, '')
    .replace(/[(),]/g, ' ')
    .trim();
  const filtered = problems.filter(
    (p) =>
      (!books.length ||
        books.some(
          (b) =>
            p.book.toLowerCase().includes(b) ||
            p.bookTitle.toLowerCase().includes(b),
        )) &&
      (!states.length || states.includes(p.status)),
  );
  if (!term) return filtered;
  const fuse = new Fuse(filtered, {
    keys: [
      { name: 'title', weight: 3 },
      { name: 'id', weight: 3 },
      { name: 'slug', weight: 2 },
      { name: 'tag', weight: 2 },
      'bookTitle',
      'chapterTitle',
      'sectionTitle',
    ],
    threshold: 0.35,
    ignoreLocation: true,
  });
  return fuse.search(term).map((x) => x.item);
}
export function restoreWorkspace(raw) {
  try {
    const data = JSON.parse(raw);
    const tabs = data.tabs
      .filter(
        (t) =>
          typeof t.id === 'string' &&
          typeof t.route === 'string' &&
          routeFromHash(t.route) === t.route,
      )
      .slice(0, 30);
    if (!tabs.length) return null;
    const ids = new Set(tabs.map((t) => t.id));
    if (ids.size !== tabs.length) return null;
    return { tabs, active: ids.has(data.active) ? data.active : tabs[0].id };
  } catch {
    return null;
  }
}
export function navigateWorkspace(state, route, newTab, id) {
  if (newTab) return { tabs: [...state.tabs, { id, route }], active: id };
  return {
    ...state,
    tabs: state.tabs.map((t) => (t.id === state.active ? { ...t, route } : t)),
  };
}
export function closeWorkspaceTab(state, id) {
  if (state.tabs.length === 1)
    return {
      tabs: [{ id: state.tabs[0].id, route: '/' }],
      active: state.tabs[0].id,
    };
  const index = state.tabs.findIndex((t) => t.id === id);
  const tabs = state.tabs.filter((t) => t.id !== id);
  return {
    tabs,
    active:
      state.active === id ? tabs[Math.max(0, index - 1)].id : state.active,
  };
}
