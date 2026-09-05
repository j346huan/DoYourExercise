'use client';
import Image from 'next/image';
import React, { useEffect, useMemo, useRef, useState } from 'react';
import {
  BookOpen,
  Library,
  Plus,
  X,
  ChevronRight,
  ChevronDown,
  ArrowUpRight,
  ArrowLeft,
  ArrowRight,
  SquarePlus,
  Check,
  CheckCheck,
  Circle,
  Code2,
  FileCode2,
  Download,
  Copy,
  Link as LinkIcon,
  GitBranch,
  Info,
  Tag,
  BookMarked,
  FolderOpen,
  ExternalLink,
  Layers,
  HelpCircle,
  LoaderCircle,
} from 'lucide-react';
import { Tabs, TabsList, TabsTrigger, TabsContent } from '@/components/ui/tabs';
import {
  Dialog,
  DialogContent,
  DialogTitle,
  DialogDescription,
  DialogHeader,
} from '@/components/ui/dialog';
import {
  Command,
  CommandInput,
  CommandList,
  CommandItem,
  CommandEmpty,
} from '@/components/ui/command';
import { TexContent, ExerciseReference } from '@/components/tex-content';
import type { Catalog, Problem, WorkspaceState } from '@/lib/types';
import {
  searchProblems,
  routeFromHash,
  restoreWorkspace,
  navigateWorkspace,
  closeWorkspaceTab,
} from '@/lib/core.mjs';
const BASE = process.env.NEXT_PUBLIC_BASE_PATH || '';
const asset = (p: string) => `${BASE}/${p}`;
const STORAGE = 'do-your-exercise:workspace:v1';
const repository = 'https://github.com/j346huan/DoYourExercise';
const initial: WorkspaceState = {
  tabs: [{ id: 'library', route: '/' }],
  active: 'library',
};
function Badge({ status }: { status: string }) {
  return (
    <span className={`status ${status}`}>
      {status === 'formalized' ? (
        <CheckCheck size={13} />
      ) : status === 'solved' ? (
        <Check size={13} />
      ) : (
        <Circle size={11} />
      )}{' '}
      {status}
    </span>
  );
}
function NewTab({
  onClick,
  label = 'Open in a new internal tab',
}: {
  onClick: () => void;
  label?: string;
}) {
  return (
    <button
      className="icon-button new-tab"
      title={label}
      aria-label={label}
      onClick={onClick}
    >
      <SquarePlus size={16} />
    </button>
  );
}
function useSource(problem: Problem | null, file: string | null) {
  const [state, setState] = useState<{
    key: string;
    loading: boolean;
    text: string;
    error: string;
  }>({ key: '', loading: false, text: '', error: '' });
  const key = problem && file ? `${problem.sourcePath}/${file}` : '';
  useEffect(() => {
    if (!key) return;
    const controller = new AbortController();
    fetch(asset(key), { signal: controller.signal })
      .then((r) => {
        if (!r.ok) throw Error(`Source unavailable (${r.status}).`);
        return r.text();
      })
      .then((text) => setState({ key, loading: false, text, error: '' }))
      .catch((e) => {
        if (e.name !== 'AbortError')
          setState({ key, loading: false, text: '', error: e.message });
      });
    return () => controller.abort();
  }, [key]);
  return state.key === key
    ? state
    : { key, loading: !!key, text: '', error: '' };
}
export default function ExerciseApp() {
  const [catalog, setCatalog] = useState<Catalog | null>(null),
    [error, setError] = useState(''),
    [workspace, setWorkspace] = useState<WorkspaceState>(initial),
    [ready, setReady] = useState(false);
  const [query, setQuery] = useState(''),
    [searchOpen, setSearchOpen] = useState(false),
    [bookDialog, setBookDialog] = useState<{
      book: string;
      chapter?: string;
      section?: string;
    } | null>(null),
    [expanded, setExpanded] = useState<string[]>([]),
    [modal, setModal] = useState<{
      kind: 'about' | 'latex' | 'lean' | 'contribute';
      slug?: string;
    } | null>(null),
    [notice, setNotice] = useState('');
  const searchRef = useRef<HTMLInputElement>(null),
    mainRef = useRef<HTMLDivElement>(null);
  const scrolls = useRef<Record<string, number>>({});
  useEffect(() => {
    const controller = new AbortController();
    fetch(asset('catalog.json'), { signal: controller.signal })
      .then((r) => {
        if (!r.ok) throw Error('The exercise catalog could not be loaded.');
        return r.json();
      })
      .then((data) => {
        setCatalog(data as Catalog);
        restoreClientWorkspace();
      })
      .catch((e) => {
        if (e.name !== 'AbortError') setError(e.message);
      });
    function restoreClientWorkspace() {
      let restored: WorkspaceState | null = null;
      try {
        restored = restoreWorkspace(localStorage.getItem(STORAGE));
      } catch {}
      const route = routeFromHash(location.hash);
      let state = restored || initial;
      if (location.hash) {
        const existing =
          state.tabs.find((t) => t.id === state.active && t.route === route) ||
          state.tabs.find((t) => t.route === route);
        state = existing
          ? { ...state, active: existing.id }
          : navigateWorkspace(state, route, true, crypto.randomUUID());
      }
      setWorkspace(state);
      setReady(true);
    }
    return () => controller.abort();
  }, []);
  useEffect(() => {
    if (ready)
      try {
        localStorage.setItem(STORAGE, JSON.stringify(workspace));
      } catch {}
  }, [workspace, ready]);
  useEffect(() => {
    const handler = () => {
      const route = routeFromHash(location.hash);
      setWorkspace((s) => {
        const existing = s.tabs.find((t) => t.route === route);
        return existing
          ? { ...s, active: existing.id }
          : navigateWorkspace(s, route, false, '');
      });
      setBookDialog(null);
      setModal(null);
    };
    window.addEventListener('hashchange', handler);
    return () => window.removeEventListener('hashchange', handler);
  }, []);
  useEffect(() => {
    const handler = (e: KeyboardEvent) => {
      const target = e.target as HTMLElement;
      if (
        e.key === '/' &&
        !['INPUT', 'TEXTAREA'].includes(target.tagName) &&
        !target.isContentEditable
      ) {
        e.preventDefault();
        searchRef.current?.focus();
        setSearchOpen(true);
      }
      if (e.key === 'Escape') setSearchOpen(false);
    };
    window.addEventListener('keydown', handler);
    return () => window.removeEventListener('keydown', handler);
  }, []);
  useEffect(() => {
    if (!notice) return;
    const t = setTimeout(() => setNotice(''), 3000);
    return () => clearTimeout(t);
  }, [notice]);
  const activeTab =
    workspace.tabs.find((t) => t.id === workspace.active) || workspace.tabs[0];
  const problem =
    catalog?.problems.find((p) => activeTab.route === `/problem/${p.slug}`) ||
    null;
  useEffect(() => {
    if (mainRef.current)
      mainRef.current.scrollTop = scrolls.current[workspace.active] || 0;
    document.title = problem
      ? `${problem.tag} · ${problem.title} — Do Your Exercise`
      : 'Do Your Exercise — A mathematical notebook';
  }, [workspace.active, activeTab.route, problem]);
  function updateRoute(state: WorkspaceState) {
    setWorkspace(state);
    const tab = state.tabs.find((t) => t.id === state.active);
    if (tab) history.pushState(null, '', `#${tab.route}`);
    setSearchOpen(false);
  }
  function navigate(route: string, newTab = false) {
    scrolls.current[workspace.active] = mainRef.current?.scrollTop || 0;
    const state = navigateWorkspace(
      workspace,
      route,
      newTab,
      crypto.randomUUID(),
    );
    if (!newTab) scrolls.current[workspace.active] = 0;
    updateRoute(state);
    setBookDialog(null);
    setModal(null);
  }
  function switchTab(id: string) {
    scrolls.current[workspace.active] = mainRef.current?.scrollTop || 0;
    updateRoute({ ...workspace, active: id });
  }
  function browse(book: string, chapter?: string, section?: string) {
    setBookDialog({ book, chapter, section });
    setExpanded(
      chapter
        ? [`c:${chapter}`, ...(section ? [`s:${chapter}:${section}`] : [])]
        : [],
    );
    setSearchOpen(false);
  }
  function filter(value: string) {
    setQuery(value);
    setSearchOpen(true);
    searchRef.current?.focus();
  }
  const results = useMemo(
    () => (catalog ? searchProblems(catalog.problems, query) : []),
    [catalog, query],
  );
  const currentBook = catalog?.books.find((b) => b.id === problem?.book);
  const selectedBook = catalog?.books.find((b) => b.id === bookDialog?.book);
  const modalProblem =
    catalog?.problems.find((p) => p.slug === modal?.slug) || null;
  const selectedFile =
    modal?.kind === 'latex'
      ? 'proof.tex'
      : modal?.kind === 'lean'
        ? 'proof.lean'
        : null;
  const source = useSource(modalProblem, selectedFile),
    translation = useSource(
      modal?.kind === 'lean' ? modalProblem : null,
      'translation.tex',
    );
  const counts = useMemo(
    () => ({
      formalized:
        catalog?.problems.filter((p) => p.status === 'formalized').length || 0,
      solved:
        catalog?.problems.filter((p) => p.status === 'solved').length || 0,
      unsolved:
        catalog?.problems.filter((p) => p.status === 'unsolved').length || 0,
    }),
    [catalog],
  );
  const allTags = useMemo(
    () =>
      catalog ? [...new Set(catalog.problems.flatMap((p) => p.tags))] : [],
    [catalog],
  );
  async function copy(text: string) {
    try {
      await navigator.clipboard.writeText(text);
      setNotice('Copied to clipboard');
    } catch {
      setNotice('Clipboard unavailable. Select the source text to copy it.');
    }
  }
  function toggle(key: string) {
    setExpanded((prev) =>
      prev.includes(key) ? prev.filter((k) => k !== key) : [...prev, key],
    );
  }
  return (
    <div className="notebook-shell">
      <header className="masthead">
        <a
          className="brand"
          href="#/"
          onClick={(e) => {
            e.preventDefault();
            navigate('/');
          }}
        >
          <BookOpen />
          <span>
            Do Your Exercise<small>A MATHEMATICAL NOTEBOOK</small>
          </span>
        </a>
        <div className="search-container">
          <Command
            shouldFilter={false}
            className="global-search"
            onKeyDown={(e) => {
              if (e.key === 'Escape') setSearchOpen(false);
            }}
          >
            <CommandInput
              ref={searchRef}
              aria-label="Search exercises"
              placeholder="Search exercises, topics, or a reference…"
              value={query}
              onValueChange={(v) => {
                setQuery(v);
                setSearchOpen(true);
              }}
              onFocus={() => setSearchOpen(true)}
            />
            <kbd className="search-key">/</kbd>
            {searchOpen && (
              <div className="search-popover">
                <div className="search-hint">
                  {query ? 'SEARCH RESULTS' : 'EXPLORE THE NOTEBOOK'}
                  <button
                    aria-label="Close search"
                    onClick={() => setSearchOpen(false)}
                  >
                    <X size={16} />
                  </button>
                </div>
                <CommandList>
                  <CommandEmpty>
                    No exercises found. Try a title, a tag, or a book
                    identifier.
                  </CommandEmpty>
                  {results.map((p: Problem) => (
                    <CommandItem
                      key={p.id}
                      value={p.id}
                      onSelect={() => {
                        navigate(`/problem/${p.slug}`);
                        setQuery('');
                      }}
                    >
                      <FileCode2 size={17} />
                      <div>
                        <strong>{p.title}</strong>
                        <small>
                          {p.id} <span>· {p.tags.slice(0, 2).join(' · ')}</span>
                        </small>
                      </div>
                      <Badge status={p.status} />
                      <button
                        className="icon-button"
                        aria-label={`Open ${p.title} in a new internal tab`}
                        onClick={(e) => {
                          e.stopPropagation();
                          navigate(`/problem/${p.slug}`, true);
                          setQuery('');
                        }}
                      >
                        <SquarePlus size={16} />
                      </button>
                    </CommandItem>
                  ))}
                </CommandList>
                <div className="search-help">
                  <span>
                    <kbd>↑</kbd>
                    <kbd>↓</kbd> navigate · <kbd>↵</kbd> open
                  </span>
                  <span>
                    Try{' '}
                    <button onClick={() => setQuery('[associativity]')}>
                      [associativity]
                    </button>{' '}
                    or{' '}
                    <button onClick={() => setQuery('status:unsolved')}>
                      status:unsolved
                    </button>
                  </span>
                </div>
              </div>
            )}
          </Command>
        </div>
        <button
          className="header-help icon-button"
          onClick={() => setModal({ kind: 'about' })}
          aria-label="About this notebook"
        >
          <HelpCircle size={20} />
        </button>
        <span className="edition">
          <span />{' '}
          {catalog?.problems.some((p) => !p.sample)
            ? 'WORKING NOTEBOOK'
            : 'SAMPLE EDITION'}
        </span>
      </header>
      <Tabs
        className="notebook-tabs"
        value={workspace.active}
        onValueChange={(value) => switchTab(String(value))}
      >
        <div className="tab-bar">
          <TabsList aria-label="Open pages" className="workspace-tab-list">
            {workspace.tabs.map((t) => {
              const p = catalog?.problems.find(
                (p) => t.route === `/problem/${p.slug}`,
              );
              return (
                <div
                  className={`tab-item ${t.id === workspace.active ? 'selected' : ''}`}
                  key={t.id}
                >
                  <TabsTrigger value={t.id}>
                    {t.route === '/' ? (
                      <Library size={15} />
                    ) : (
                      <FileCode2 size={15} />
                    )}
                    <span>
                      {p
                        ? `${p.book} · ${p.tag}`
                        : t.route === '/'
                          ? 'Library'
                          : 'Exercise'}
                    </span>
                  </TabsTrigger>
                  {workspace.tabs.length > 1 && (
                    <button
                      className="tab-close"
                      aria-label={`Close ${p?.id || 'library'} tab`}
                      onClick={() =>
                        updateRoute(closeWorkspaceTab(workspace, t.id))
                      }
                    >
                      <X size={12} />
                    </button>
                  )}
                </div>
              );
            })}
          </TabsList>
          <button
            title="New library tab"
            aria-label="New library tab"
            onClick={() => navigate('/', true)}
          >
            <Plus size={17} />
          </button>
          <span className="tab-caption">YOUR WORKSPACE</span>
        </div>
        {workspace.tabs.map((t) => (
          <TabsContent key={t.id} value={t.id} className="workspace-panel">
            {t.id === workspace.active && (
              <div className="main-scroll" ref={mainRef}>
                <main className="workspace">
                  {!catalog ? (
                    <div className="loading-panel">
                      {error ? (
                        <>
                          <Info />
                          <h1>Unable to load the library</h1>
                          <p>{error}</p>
                          <button
                            className="primary-button"
                            onClick={() => location.reload()}
                          >
                            Try again
                          </button>
                        </>
                      ) : (
                        <>
                          <LoaderCircle className="spin" />
                          <p>Opening your notebook…</p>
                        </>
                      )}
                    </div>
                  ) : activeTab.route === '/' ? (
                    <>
                      <div className="page-heading">
                        <div>
                          <div className="eyebrow">THE LIBRARY</div>
                          <h1>Do your exercise.</h1>
                          <p className="intro">
                            Statements, proofs, and the details in between.
                          </p>
                        </div>
                        <div className="library-total">
                          <BookMarked size={18} />
                          <span>
                            <strong>{catalog.books.length}</strong> books{' '}
                            <span className="muted">/</span>{' '}
                            <strong>{catalog.problems.length}</strong> exercises
                          </span>
                        </div>
                      </div>
                      <div className="library-layout">
                        <div className="library-main">
                          <div className="section-heading">
                            <h2>
                              <Library size={17} /> Bookshelf
                            </h2>
                            <span>SELECT A BOOK TO BROWSE</span>
                          </div>
                          <section
                            className="shelf-grid"
                            aria-label="Bookshelf"
                          >
                            {catalog.books
                              .filter((b) => b.cover)
                              .map((b, index) => (
                                <button
                                  className="book-tile"
                                  key={b.id}
                                  onClick={() => browse(b.id)}
                                >
                                  <div className="book-image-area">
                                    <span className={`cover-badge ${b.kind}`}>
                                      {b.kind === 'sample'
                                        ? 'SAMPLE NOTEBOOK'
                                        : b.kind === 'planned'
                                          ? 'UP NEXT'
                                          : 'TEXTBOOK'}
                                    </span>
                                    <Image
                                      unoptimized
                                      className="book-cover"
                                      src={asset(b.cover!)}
                                      alt={`${b.title} front cover`}
                                      width={180}
                                      height={270}
                                    />
                                  </div>
                                  <div className="book-details">
                                    <div className="book-id">
                                      {String(index + 1).padStart(2, '0')}{' '}
                                      <span>{b.id}</span>
                                    </div>
                                    <h2>{b.title}</h2>
                                    <p>{b.authors}</p>
                                    <div className="book-foot">
                                      <span>
                                        {catalog.problems.filter(
                                          (p) => p.book === b.id,
                                        ).length
                                          ? `${catalog.problems.filter((p) => p.book === b.id).length} exercises`
                                          : 'Collection planned'}
                                      </span>
                                      <ArrowUpRight size={17} />
                                    </div>
                                  </div>
                                </button>
                              ))}
                          </section>
                          <div className="sample-note">
                            <Info size={16} />
                            <p>
                              Textbook solutions and original demo exercises are
                              labeled separately. Imported notes include a link
                              to their source.
                            </p>
                          </div>
                          <div className="section-heading exercise-section">
                            <h2>
                              <FileCode2 size={17} /> Inside the notebook
                            </h2>
                            <button
                              className="text-button"
                              onClick={() => filter('')}
                            >
                              Browse all <ArrowRight size={14} />
                            </button>
                          </div>
                          <div className="exercise-list">
                            {catalog.problems.map((p) => (
                              <div className="exercise-row" key={p.id}>
                                <span className={`row-status ${p.status}`}>
                                  {p.status === 'unsolved' ? (
                                    <Circle size={16} />
                                  ) : (
                                    <Check size={18} />
                                  )}
                                </span>
                                <button
                                  className="exercise-row-title"
                                  onClick={() => navigate(`/problem/${p.slug}`)}
                                >
                                  <strong>{p.title}</strong>
                                  <small>
                                    {p.id}
                                    <span> · {p.bookTitle}</span>
                                  </small>
                                </button>
                                <div className="row-tags">
                                  {p.tags.slice(0, 1).map((tag) => (
                                    <button
                                      className="tag"
                                      key={tag}
                                      onClick={() => filter(`[${tag}]`)}
                                    >
                                      {tag}
                                    </button>
                                  ))}
                                </div>
                                <Badge status={p.status} />
                                <NewTab
                                  label={`Open ${p.title} in a new internal tab`}
                                  onClick={() =>
                                    navigate(`/problem/${p.slug}`, true)
                                  }
                                />
                              </div>
                            ))}
                          </div>
                          {catalog.books
                            .filter((b) => !b.cover)
                            .map((b) => (
                              <button
                                className="companion-book"
                                key={b.id}
                                onClick={() => browse(b.id)}
                              >
                                <BookOpen size={22} />
                                <span>
                                  <strong>{b.title}</strong>
                                  <small>
                                    Companion sample · {b.id} · Chapters without
                                    sections
                                  </small>
                                </span>
                                <ChevronRight size={18} />
                              </button>
                            ))}
                        </div>
                        <aside className="library-sidebar">
                          <div className="aside-panel">
                            <h2>
                              <Layers size={16} /> At a glance
                            </h2>
                            {(
                              ['formalized', 'solved', 'unsolved'] as const
                            ).map((s) => (
                              <button
                                className="stat-row"
                                key={s}
                                onClick={() => filter(`status:${s}`)}
                              >
                                <Badge status={s} />
                                <strong>{counts[s]}</strong>
                              </button>
                            ))}
                            <p className="aside-caption">
                              Small steps. Written down.
                            </p>
                          </div>
                          <div className="aside-panel">
                            <h2>
                              <Tag size={16} /> Explore by topic
                            </h2>
                            <div className="topic-cloud">
                              {allTags.map((tag) => (
                                <button
                                  className="tag"
                                  key={tag}
                                  onClick={() => filter(`[${tag}]`)}
                                >
                                  {tag}
                                </button>
                              ))}
                            </div>
                          </div>
                          <div className="aside-panel note-panel">
                            <span className="note-number">
                              01 / FIELD NOTES
                            </span>
                            <h3>A proof has more than one form.</h3>
                            <p>
                              Read the argument, inspect its LaTeX source, or
                              follow the Lean proof one step at a time.
                            </p>
                            <button
                              className="text-button"
                              onClick={() => setModal({ kind: 'about' })}
                            >
                              About this notebook <ArrowUpRight size={14} />
                            </button>
                          </div>
                        </aside>
                      </div>
                    </>
                  ) : problem && currentBook ? (
                    <>
                      <nav className="breadcrumbs" aria-label="Breadcrumb">
                        <button onClick={() => navigate('/')}>
                          <Library size={14} /> Home
                        </button>
                        <NewTab
                          label="Open home in a new internal tab"
                          onClick={() => navigate('/', true)}
                        />
                        <ChevronRight />
                        <button onClick={() => browse(currentBook.id)}>
                          {currentBook.shortTitle}
                        </button>
                        <ChevronRight />
                        <button
                          onClick={() =>
                            browse(currentBook.id, problem.chapter)
                          }
                        >
                          Chapter {problem.chapter}
                        </button>
                        {problem.section && (
                          <>
                            <ChevronRight />
                            <button
                              onClick={() =>
                                browse(
                                  currentBook.id,
                                  problem.chapter,
                                  problem.section!,
                                )
                              }
                            >
                              § {problem.chapter}.{problem.section}
                            </button>
                          </>
                        )}
                        <ChevronRight />
                        <button
                          className="crumb-current"
                          onClick={() =>
                            browse(
                              currentBook.id,
                              problem.chapter,
                              problem.section || undefined,
                            )
                          }
                        >
                          Exercise {problem.tag}
                        </button>
                      </nav>
                      <ProblemPage
                        problem={problem}
                        catalog={catalog}
                        navigate={navigate}
                        browse={browse}
                        filter={filter}
                        sourceModal={(kind) =>
                          setModal({ kind, slug: problem.slug })
                        }
                        copyLink={() =>
                          copy(
                            `${location.origin}${BASE}/#/problem/${problem.slug}`,
                          )
                        }
                        contribute={() => setModal({ kind: 'contribute' })}
                      />
                    </>
                  ) : (
                    <div className="loading-panel">
                      <Info />
                      <h1>Exercise not found</h1>
                      <p>
                        This reference does not point to an exercise in the
                        current library.
                      </p>
                      <button
                        className="primary-button"
                        onClick={() => navigate('/')}
                      >
                        Return to the library
                      </button>
                    </div>
                  )}
                  <footer className="site-footer">
                    <span>
                      <BookOpen size={14} /> Do Your Exercise{' '}
                      <span className="footer-divider">/</span> A notebook in
                      progress.
                    </span>
                    <div>
                      <button onClick={() => setModal({ kind: 'about' })}>
                        About & sources
                      </button>
                      <button onClick={() => setModal({ kind: 'contribute' })}>
                        Contributing <ArrowUpRight size={12} />
                      </button>
                    </div>
                  </footer>
                </main>
              </div>
            )}
          </TabsContent>
        ))}
      </Tabs>
      <Dialog
        open={!!bookDialog}
        onOpenChange={(open) => {
          if (!open) setBookDialog(null);
        }}
      >
        <DialogContent className="book-dialog">
          <DialogHeader>
            <div className="eyebrow">BROWSE THE BOOK</div>
            <DialogTitle>{selectedBook?.title}</DialogTitle>
            <DialogDescription>
              {selectedBook?.authors} · {selectedBook?.id}
            </DialogDescription>
          </DialogHeader>
          <div className="book-dialog-body">
            {selectedBook?.chapters.length ? (
              <>
                <div className="tree-toolbar">
                  <span>Chapters / sections / exercises</span>
                  <button onClick={() => setExpanded([])}>Collapse all</button>
                </div>
                {selectedBook.chapters.map((ch) => (
                  <div className="chapter-node" key={ch.id}>
                    <button
                      className="chapter-toggle"
                      aria-expanded={expanded.includes(`c:${ch.id}`)}
                      onClick={() => toggle(`c:${ch.id}`)}
                    >
                      {expanded.includes(`c:${ch.id}`) ? (
                        <ChevronDown size={17} />
                      ) : (
                        <ChevronRight size={17} />
                      )}
                      <span className="chapter-number">
                        {ch.id.padStart(2, '0')}
                      </span>
                      <strong>{ch.title}</strong>
                      <span className="tree-count">
                        {
                          catalog?.problems.filter(
                            (p) =>
                              p.book === selectedBook.id && p.chapter === ch.id,
                          ).length
                        }
                      </span>
                    </button>
                    {expanded.includes(`c:${ch.id}`) && (
                      <div className="chapter-children">
                        {ch.sections?.length ? (
                          ch.sections.map((s) => (
                            <div className="section-node" key={s.id}>
                              <button
                                className="section-toggle"
                                aria-expanded={expanded.includes(
                                  `s:${ch.id}:${s.id}`,
                                )}
                                onClick={() => toggle(`s:${ch.id}:${s.id}`)}
                              >
                                {expanded.includes(`s:${ch.id}:${s.id}`) ? (
                                  <ChevronDown size={15} />
                                ) : (
                                  <ChevronRight size={15} />
                                )}
                                <span>
                                  {ch.id}.{s.id}
                                </span>
                                {s.title}
                              </button>
                              {expanded.includes(`s:${ch.id}:${s.id}`) && (
                                <TreeProblems
                                  problems={catalog!.problems.filter(
                                    (p) =>
                                      p.book === selectedBook.id &&
                                      p.chapter === ch.id &&
                                      p.section === s.id,
                                  )}
                                  navigate={navigate}
                                />
                              )}
                            </div>
                          ))
                        ) : (
                          <TreeProblems
                            problems={catalog!.problems.filter(
                              (p) =>
                                p.book === selectedBook.id &&
                                p.chapter === ch.id,
                            )}
                            navigate={navigate}
                          />
                        )}
                      </div>
                    )}
                  </div>
                ))}
              </>
            ) : (
              <div className="planned-empty">
                <BookOpen size={36} />
                <h3>A place for the next chapter.</h3>
                <p>{selectedBook?.description}</p>
                <span className="tag">Collection planned</span>
              </div>
            )}
          </div>
          <div className="dialog-foot">
            <span>
              {selectedBook?.kind === 'sample'
                ? 'Original demo content'
                : selectedBook?.kind === 'planned'
                  ? 'No textbook content added yet'
                  : 'Textbook collection'}
            </span>
            <span>
              <SquarePlus size={15} /> opens an internal tab
            </span>
          </div>
        </DialogContent>
      </Dialog>
      <Dialog
        open={!!modal}
        onOpenChange={(open) => {
          if (!open) setModal(null);
        }}
      >
        <DialogContent
          className={`source-dialog ${modal?.kind === 'lean' ? 'lean-dialog' : ''}`}
        >
          <DialogHeader>
            <div className="eyebrow">
              {modal?.kind === 'lean'
                ? 'TWO VIEWS OF ONE ARGUMENT'
                : modal?.kind === 'latex'
                  ? 'THE SOURCE'
                  : 'DO YOUR EXERCISE'}
            </div>
            <DialogTitle>
              {modal?.kind === 'lean'
                ? 'Lean 4 formalization'
                : modal?.kind === 'latex'
                  ? 'Natural proof · LaTeX source'
                  : modal?.kind === 'contribute'
                    ? 'Contributing to the notebook'
                    : 'A notebook for doing the work.'}
            </DialogTitle>
            <DialogDescription>
              {modalProblem
                ? `${modalProblem.id} · ${modalProblem.title}`
                : 'A personal collection of mathematical exercises and their proofs.'}
            </DialogDescription>
          </DialogHeader>
          {modal?.kind === 'latex' ? (
            <>
              <div className="source-toolbar">
                <span>proof.tex</span>
                <div>
                  <button
                    disabled={source.loading || !!source.error}
                    onClick={() => copy(source.text)}
                  >
                    <Copy size={14} /> Copy
                  </button>
                  <a
                    href={asset(`${modalProblem?.sourcePath}/proof.tex`)}
                    download
                  >
                    <Download size={14} /> Download
                  </a>
                </div>
              </div>
              <SourceText state={source} />
            </>
          ) : modal?.kind === 'lean' ? (
            <>
              <div className="verification-banner">
                <Info size={16} />
                {modalProblem?.status === 'formalized'
                  ? 'This proof has a recorded successful Lean check.'
                  : 'Sample Lean code · not compiler-verified. This exercise is marked solved, not formalized.'}
              </div>
              <div className="lean-columns">
                <section>
                  <div className="source-toolbar">
                    <span>
                      <Code2 size={15} /> Lean 4
                    </span>
                    <div>
                      <button
                        disabled={source.loading || !!source.error}
                        onClick={() => copy(source.text)}
                      >
                        <Copy size={14} /> Copy
                      </button>
                      <a
                        href={asset(`${modalProblem?.sourcePath}/proof.lean`)}
                        download
                        aria-label="Download Lean source"
                      >
                        <Download size={15} />
                      </a>
                    </div>
                  </div>
                  <SourceText state={source} />
                </section>
                <section>
                  <div className="source-toolbar">
                    <span>
                      <BookOpen size={15} /> Step-by-step translation
                    </span>
                  </div>
                  {translation.loading ? (
                    <p className="source-message">Loading translation…</p>
                  ) : translation.error ? (
                    <p className="source-message">{translation.error}</p>
                  ) : (
                    <div className="translation-text">
                      <TexContent
                        text={translation.text}
                        book={modalProblem!.book}
                        catalog={catalog!}
                        onNavigate={navigate}
                      />
                    </div>
                  )}
                </section>
              </div>
              <div className="lean-dependencies">
                <GitBranch size={15} />
                <div>
                  <strong>Imports & earlier results</strong>
                  <p>
                    {modalProblem?.dependencies.length
                      ? modalProblem.dependencies.map((id) => {
                          const p = catalog!.problems.find((p) => p.id === id);
                          return p ? (
                            <ExerciseReference
                              key={id}
                              problem={p}
                              currentBook={modalProblem.book}
                              onNavigate={navigate}
                            />
                          ) : (
                            id
                          );
                        })
                      : 'Mathlib · standard library lemmas'}
                  </p>
                  <small>Local module: {modalProblem?.lean?.module}</small>
                </div>
              </div>
            </>
          ) : modal?.kind === 'contribute' ? (
            <div className="about-content">
              <p>
                Submissions through this website are planned for a later
                version.
              </p>
              <p>
                For now, the collection is maintained as files. A contribution
                can add a proof to an unsolved exercise, suggest an unlisted
                exercise, or propose a book.
              </p>
              <ol>
                <li>Use the exercise’s stable tag for its folder.</li>
                <li>
                  Keep the statement, natural proof, Lean proof, and translation
                  separate.
                </li>
                <li>
                  Include references and a successful Lean check before marking
                  a proof formalized.
                </li>
              </ol>
              <p>
                The authoring guide in the repository explains the format and
                review process.
              </p>
              <a
                className="primary-button"
                href={`${repository}/blob/main/CONTRIBUTING.md`}
                target="_blank"
                rel="noreferrer"
              >
                Read the contribution guide <ExternalLink size={15} />
              </a>
            </div>
          ) : (
            <div className="about-content">
              <p>
                <strong>Do Your Exercise</strong> is a place to collect textbook
                problems, readable proofs, and their formal counterparts.
              </p>
              <h3>A small, connected workspace</h3>
              <p>
                Click an exercise to read it in the current internal tab. Use{' '}
                <SquarePlus className="inline-icon" size={16} /> to open
                another. Your open tabs are remembered on this device. Hover or
                focus a reference to preview its statement.
              </p>
              <h3>Find a thread to follow</h3>
              <p>
                Search tolerates small typos. Combine a topic such as{' '}
                <code>[associativity]</code> with <code>book:Notebook26</code>{' '}
                or <code>status:unsolved</code>. References look like{' '}
                <code>(1.1.1)</code> within a book and{' '}
                <code>(Notebook26,1.1.1)</code> between books.
              </p>
              <h3>About this edition</h3>
              <p>
                Atiyah–Macdonald Chapter 1 contains the author’s solution notes,
                transcribed from the original PDF. Statement summaries are
                reconstructed from those notes because the PDF omits the
                textbook statements. Partial notes and blank entries remain
                unsolved. Six original demo exercises are also included;
                Hartshorne remains a planned collection.
              </p>
              <h3>Sources & acknowledgments</h3>
              <p>
                Visual direction inspired by{' '}
                <a
                  href="https://noro6.github.io/kc-web/#/"
                  target="_blank"
                  rel="noreferrer"
                >
                  noro6’s simulator
                </a>
                . No game features are reproduced.
              </p>
              {catalog?.books
                .filter((b) => b.coverSource)
                .map((b) => (
                  <p key={b.id}>
                    <a href={b.coverSource} target="_blank" rel="noreferrer">
                      {b.title}
                    </a>{' '}
                    — cover image: {b.coverCredit}. All rights remain with their
                    respective owners.
                  </p>
                ))}
              <p>
                The sample algebra notebook cover was created for this project.
                Math is typeset with KaTeX.
              </p>
            </div>
          )}
        </DialogContent>
      </Dialog>
      <output className={`toast ${notice ? 'visible' : ''}`} aria-live="polite">
        {notice && (
          <>
            <Check size={16} />
            {notice}
          </>
        )}
      </output>
    </div>
  );
}
function TreeProblems({
  problems,
  navigate,
}: {
  problems: Problem[];
  navigate: (route: string, newTab?: boolean) => void;
}) {
  return (
    <div className="tree-problems">
      {problems.length ? (
        problems.map((p) => (
          <div className="tree-problem" key={p.id}>
            <button onClick={() => navigate(`/problem/${p.slug}`)}>
              <span className="tree-tag">{p.tag}</span>
              <span>{p.title}</span>
              <Badge status={p.status} />
            </button>
            <NewTab
              label={`Open exercise ${p.tag} in a new internal tab`}
              onClick={() => navigate(`/problem/${p.slug}`, true)}
            />
          </div>
        ))
      ) : (
        <p className="tree-empty">No exercises added yet.</p>
      )}
    </div>
  );
}
function SourceText({
  state,
}: {
  state: { loading: boolean; error: string; text: string };
}) {
  return state.loading ? (
    <p className="source-message">
      <LoaderCircle className="spin" size={18} /> Loading source…
    </p>
  ) : state.error ? (
    <p className="source-message error">{state.error}</p>
  ) : (
    <pre className="source-code">
      <code>{state.text}</code>
    </pre>
  );
}
function ProblemPage({
  problem: p,
  catalog,
  navigate,
  browse,
  filter,
  sourceModal,
  copyLink,
  contribute,
}: {
  problem: Problem;
  catalog: Catalog;
  navigate: (route: string, newTab?: boolean) => void;
  browse: (book: string, chapter?: string, section?: string) => void;
  filter: (value: string) => void;
  sourceModal: (kind: 'latex' | 'lean') => void;
  copyLink: () => void;
  contribute: () => void;
}) {
  const proof = useSource(
    p,
    p.files.includes('proof.tex') ? 'proof.tex' : null,
  );
  const siblings = catalog.problems.filter((x) => x.book === p.book);
  const index = siblings.findIndex((x) => x.id === p.id);
  const related = catalog.problems
    .filter(
      (x) =>
        x.id !== p.id &&
        (p.dependencies.includes(x.id) ||
          x.dependencies.includes(p.id) ||
          x.tags.some((t) => p.tags.includes(t))),
    )
    .slice(0, 4);
  return (
    <>
      <div className="problem-heading">
        <div>
          <div className="eyebrow">
            EXERCISE {p.tag} <span className="eyebrow-divider">/</span> {p.book}
          </div>
          <h1>{p.title}</h1>
          <div className="problem-meta">
            <Badge status={p.status} />
            <span>
              {p.sample ? 'Original demo exercise' : 'Textbook exercise'}
            </span>
            <span>Updated {p.updated}</span>
          </div>
        </div>
        <button className="outline-button" onClick={copyLink}>
          <LinkIcon size={15} /> Copy link
        </button>
      </div>
      <div className="problem-layout">
        <article>
          <section className="proof-panel statement-panel">
            <div className="panel-heading">
              <span className="panel-icon">
                <FileCode2 size={18} />
              </span>
              <h2>
                {p.source?.statement === 'summary'
                  ? 'Statement summary'
                  : 'Statement'}
              </h2>
              <span className="mono muted">({p.tag})</span>
            </div>
            {p.source && (
              <p className="statement-origin">
                {p.source.statement === 'summary'
                  ? 'Summarized from the solution notes; the full textbook statement is not included in the source PDF.'
                  : 'The source PDF includes this exercise heading without a statement.'}
              </p>
            )}
            <TexContent
              text={p.statement}
              book={p.book}
              catalog={catalog}
              onNavigate={navigate}
            />
            <div className="problem-tags">
              {p.tags.map((t) => (
                <button
                  className="tag"
                  key={t}
                  onClick={() => filter(`[${t}]`)}
                >
                  {t}
                </button>
              ))}
            </div>
          </section>
          <section className="proof-panel solution-panel">
            <div className="panel-heading">
              <span
                className={`panel-icon ${p.status === 'unsolved' ? 'muted' : ''}`}
              >
                {p.status === 'unsolved' ? (
                  <Circle size={18} />
                ) : (
                  <Check size={20} />
                )}
              </span>
              <h2>
                {p.coverage === 'partial'
                  ? 'Partial solution notes'
                  : p.source
                    ? 'Author’s solution'
                    : 'Solution'}
              </h2>
              {p.files.includes('proof.tex') && (
                <span className="solution-kind">
                  {p.source ? 'TRANSCRIBED NOTES' : 'NATURAL LANGUAGE PROOF'}
                </span>
              )}
            </div>
            <SourceAttribution problem={p} />
            {!p.files.includes('proof.tex') ? (
              <div className="unsolved-content">
                <p>
                  {p.source
                    ? 'No solution was included in the PDF.'
                    : 'This proof is still to be written.'}
                </p>
                <span>There is room here for a good argument.</span>
                <button className="outline-button" onClick={contribute}>
                  About contributing <ArrowUpRight size={15} />
                </button>
              </div>
            ) : proof.loading ? (
              <p className="source-message">Loading proof…</p>
            ) : proof.error ? (
              <p className="source-message error">{proof.error}</p>
            ) : (
              <>
                <TexContent
                  text={proof.text}
                  book={p.book}
                  catalog={catalog}
                  onNavigate={navigate}
                />
                {p.coverage !== 'partial' && (
                  <div className="qed" aria-label="End of proof">
                    □
                  </div>
                )}
              </>
            )}
          </section>
          {p.files.includes('proof.tex') && (
            <div className="proof-artifacts">
              <button
                className="artifact-card"
                onClick={() => sourceModal('latex')}
              >
                <div className="artifact-icon tex-icon">
                  T<span>E</span>X
                </div>
                <span>
                  <strong>LaTeX source</strong>
                  <small>
                    {p.coverage === 'partial'
                      ? 'Source for the partial notes'
                      : 'The natural proof, ready to reuse'}
                  </small>
                </span>
                <ArrowUpRight size={18} />
              </button>
              <button
                className="artifact-card"
                onClick={() => sourceModal('lean')}
                disabled={!p.files.includes('proof.lean')}
              >
                <div className="artifact-icon">
                  <Code2 size={24} />
                </div>
                <span>
                  <strong>Lean 4 & translation</strong>
                  <small>
                    {p.files.includes('proof.lean')
                      ? p.status === 'formalized'
                        ? 'Verified formal proof'
                        : 'Sample code · unverified'
                      : 'No formalization added yet'}
                  </small>
                </span>
                <ArrowUpRight size={18} />
              </button>
            </div>
          )}
          <div className="problem-pagination">
            <button
              disabled={index === 0}
              onClick={() => navigate(`/problem/${siblings[index - 1].slug}`)}
            >
              <ArrowLeft size={16} />
              <span>
                <small>PREVIOUS EXERCISE</small>
                {siblings[index - 1]?.tag || 'Beginning of book'}
              </span>
            </button>
            <button
              onClick={() => browse(p.book, p.chapter, p.section || undefined)}
            >
              <FolderOpen size={16} />
              <span>Browse chapter</span>
            </button>
            <button
              disabled={index === siblings.length - 1}
              onClick={() => navigate(`/problem/${siblings[index + 1].slug}`)}
            >
              <span>
                <small>NEXT EXERCISE</small>
                {siblings[index + 1]?.tag || 'End of notebook'}
              </span>
              <ArrowRight size={16} />
            </button>
          </div>
        </article>
        <aside className="problem-sidebar">
          <div className="aside-panel">
            <h2>
              <BookMarked size={16} /> In this book
            </h2>
            <p className="sidebar-book-title">{p.bookTitle}</p>
            <button
              className="chapter-link"
              onClick={() => browse(p.book, p.chapter, p.section || undefined)}
            >
              <span>
                {p.chapter}. {p.chapterTitle}
              </span>
              <ChevronRight size={16} />
            </button>
            {p.section && (
              <p className="sidebar-section">
                § {p.chapter}.{p.section} · {p.sectionTitle}
              </p>
            )}
            <div className="sidebar-id">
              REFERENCE <code>{p.id}</code>
            </div>
          </div>
          <div className="aside-panel">
            <h2>
              <GitBranch size={16} /> Related exercises
            </h2>
            {related.length ? (
              related.map((r) => (
                <div className="related-exercise" key={r.id}>
                  <ExerciseReference
                    problem={r}
                    currentBook={p.book}
                    onNavigate={navigate}
                  >
                    <span>{r.title}</span>
                    <small>{r.book === p.book ? r.tag : r.id}</small>
                  </ExerciseReference>
                  <NewTab
                    onClick={() => navigate(`/problem/${r.slug}`, true)}
                    label={`Open ${r.title} in a new internal tab`}
                  />
                </div>
              ))
            ) : (
              <p className="muted">No related exercises yet.</p>
            )}
          </div>
          <div className="aside-panel file-panel">
            <h2>
              <FileCode2 size={16} /> Exercise files
            </h2>
            {p.files.map((file) => (
              <a key={file} href={asset(`${p.sourcePath}/${file}`)} download>
                <span>{file}</span>
                <Download size={14} />
              </a>
            ))}
            <p>Each part lives in its own file.</p>
          </div>
        </aside>
      </div>
    </>
  );
}

function SourceAttribution({ problem: p }: { problem: Problem }) {
  if (!p.source) return null;
  return (
    <div className="source-attribution">
      <div>
        <a
          href={p.source.url + '#page=' + p.source.pages[0]}
          target="_blank"
          rel="noreferrer"
        >
          <FileCode2 size={14} />
          {p.source.label} · {p.source.pages.length > 1 ? 'pp.' : 'p.'}{' '}
          {p.source.pages.join('–')}
          <ExternalLink size={12} />
        </a>
        <span>
          {p.coverage === 'partial'
            ? 'The source provides partial notes; the exercise remains unsolved.'
            : p.coverage === 'empty'
              ? 'No solution is written under this heading in the source.'
              : 'Transcribed with the original argument preserved; not independently verified.'}
        </span>
      </div>
    </div>
  );
}
