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
  FolderOpen,
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
      kind: 'about' | 'latex' | 'lean';
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
        restoreClientWorkspace(data as Catalog);
      })
      .catch((e) => {
        if (e.name !== 'AbortError') setError(e.message);
      });
    function restoreClientWorkspace(loaded: Catalog) {
      let restored: WorkspaceState | null = null;
      try {
        restored = restoreWorkspace(localStorage.getItem(STORAGE));
      } catch {}
      const route = routeFromHash(location.hash);
      const retained = restored?.tabs.filter(
        (t) =>
          t.route === '/' ||
          loaded.problems.some((p) => t.route === `/problem/${p.slug}`),
      );
      let state = retained?.length
        ? {
            tabs: retained,
            active: retained.some((t) => t.id === restored!.active)
              ? restored!.active
              : retained[0].id,
          }
        : initial;
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
      ? `${problem.id}${problem.title ? ' · ' + problem.title : ''} — Do Your Exercise`
      : 'Do Your Exercise';
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
          <span>Do Your Exercise</span>
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
              placeholder="Search questions or references…"
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
                  Results
                  <button
                    aria-label="Close search"
                    onClick={() => setSearchOpen(false)}
                  >
                    <X size={16} />
                  </button>
                </div>
                <CommandList>
                  <CommandEmpty>No questions found.</CommandEmpty>
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
                        <strong>
                          {p.id}
                          {p.title ? ` · ${p.title}` : ''}
                        </strong>
                        <small>{p.bookTitle}</small>
                      </div>
                      <Badge status={p.status} />
                      <button
                        className="icon-button"
                        aria-label={`Open ${p.id} in a new internal tab`}
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
              </div>
            )}
          </Command>
        </div>
        <button
          className="header-help icon-button"
          onClick={() => setModal({ kind: 'about' })}
          aria-label="About"
        >
          <HelpCircle size={20} />
        </button>
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
                          ? 'Home'
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
            title="New home tab"
            aria-label="New home tab"
            onClick={() => navigate('/', true)}
          >
            <Plus size={17} />
          </button>
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
                          <p>Loading…</p>
                        </>
                      )}
                    </div>
                  ) : activeTab.route === '/' ? (
                    <section className="shelf-grid" aria-label="Textbooks">
                      {catalog.books.map((b) => (
                        <button
                          className="book-tile"
                          key={b.id}
                          onClick={() => browse(b.id)}
                        >
                          <div className="book-image-area">
                            {b.cover ? (
                              <Image
                                unoptimized
                                className="book-cover"
                                src={asset(b.cover)}
                                alt={b.title}
                                width={180}
                                height={270}
                              />
                            ) : (
                              <BookOpen size={44} />
                            )}
                          </div>
                          <div className="book-details">
                            <span className="book-id">{b.id}</span>
                            <h2>{b.title}</h2>
                            <p>{b.authors}</p>
                            <div className="book-foot">
                              {
                                catalog.problems.filter((p) => p.book === b.id)
                                  .length
                              }{' '}
                              exercises
                            </div>
                          </div>
                        </button>
                      ))}
                    </section>
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
                        sourceModal={(kind) =>
                          setModal({ kind, slug: problem.slug })
                        }
                        copyLink={() =>
                          copy(
                            `${location.origin}${BASE}/#/problem/${problem.slug}`,
                          )
                        }
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
            <DialogTitle>{selectedBook?.title}</DialogTitle>
            <DialogDescription>
              {selectedBook?.authors} · {selectedBook?.id}
            </DialogDescription>
          </DialogHeader>
          <div className="book-dialog-body">
            {selectedBook?.chapters.length ? (
              <>
                <div className="tree-toolbar">
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
              <p className="tree-empty">No exercises.</p>
            )}
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
          className={`source-dialog ${modal?.kind === 'lean' ? 'lean-dialog' : modal?.kind === 'about' ? 'about-dialog' : ''}`}
          aria-describedby={undefined}
        >
          <DialogHeader>
            <DialogTitle
              className={modal?.kind === 'about' ? 'sr-only' : undefined}
            >
              {modal?.kind === 'lean'
                ? 'Lean 4'
                : modal?.kind === 'latex'
                  ? 'LaTeX'
                  : 'About'}
            </DialogTitle>
            {modalProblem && (
              <DialogDescription>
                {modalProblem.id}
                {modalProblem.title ? ` · ${modalProblem.title}` : ''}
              </DialogDescription>
            )}
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
              <div className="lean-columns">
                <section>
                  <div className="source-toolbar">
                    <span>Lean 4</span>
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
                    <span>Translation</span>
                  </div>
                  {translation.loading ? (
                    <p className="source-message">Loading…</p>
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
              {!!modalProblem?.dependencies.length && (
                <div className="lean-dependencies">
                  <strong>References</strong>
                  {modalProblem.dependencies.map((id) => {
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
                  })}
                </div>
              )}
            </>
          ) : (
            <div className="about-content">
              <p>
                This is a repository of my solutions to exercises to textbooks
                that I used. I shall also include lean formalization when
                possible.
              </p>
              <h3>Sources</h3>
              <pre className="bibliography">
                <code>
                  {catalog?.books
                    .map((b) => b.bibtex)
                    .filter(Boolean)
                    .join('\n\n')}
                </code>
              </pre>
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
              <span>{p.title || null}</span>
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
  sourceModal,
  copyLink,
}: {
  problem: Problem;
  catalog: Catalog;
  navigate: (route: string, newTab?: boolean) => void;
  browse: (book: string, chapter?: string, section?: string) => void;
  sourceModal: (kind: 'latex' | 'lean') => void;
  copyLink: () => void;
}) {
  const proof = useSource(
    p,
    p.files.includes('proof.tex') ? 'proof.tex' : null,
  );
  const siblings = catalog.problems.filter((x) => x.book === p.book);
  const index = siblings.findIndex((x) => x.id === p.id);
  const related = catalog.problems.filter(
    (x) =>
      x.id !== p.id &&
      (p.dependencies.includes(x.id) || x.dependencies.includes(p.id)),
  );
  return (
    <>
      {p.title && <h1 className="question-title">{p.title}</h1>}
      <div className="problem-layout">
        <article>
          <section className="proof-panel statement-panel">
            <div className="panel-heading">
              <h2>
                Question <span className="mono">{p.tag}</span>
              </h2>
              <Badge status={p.status} />
              <button
                className="icon-button"
                onClick={copyLink}
                aria-label="Copy question link"
                title="Copy link"
              >
                <LinkIcon size={15} />
              </button>
            </div>
            {p.statement && (
              <TexContent
                text={p.statement}
                book={p.book}
                catalog={catalog}
                onNavigate={navigate}
              />
            )}
          </section>
          <section className="proof-panel solution-panel">
            <div className="panel-heading">
              <h2>Solution</h2>
            </div>
            {proof.loading ? (
              <p className="source-message">Loading…</p>
            ) : proof.error ? (
              <p className="source-message error">{proof.error}</p>
            ) : p.files.includes('proof.tex') ? (
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
            ) : null}
          </section>
          {p.files.includes('proof.tex') && (
            <div className="proof-artifacts">
              <button
                className="artifact-card"
                onClick={() => sourceModal('latex')}
              >
                <FileCode2 size={20} />
                <strong>LaTeX</strong>
              </button>
              <button
                className="artifact-card"
                onClick={() => sourceModal('lean')}
                disabled={!p.files.includes('proof.lean')}
              >
                <Code2 size={20} />
                <strong>Lean 4 & translation</strong>
              </button>
            </div>
          )}
          <div className="problem-pagination">
            <button
              disabled={index === 0}
              onClick={() => navigate(`/problem/${siblings[index - 1].slug}`)}
            >
              <ArrowLeft size={16} />
              <span>{siblings[index - 1]?.tag || 'Previous'}</span>
            </button>
            <button
              onClick={() => browse(p.book, p.chapter, p.section || undefined)}
            >
              <FolderOpen size={16} />
              <span>Chapter {p.chapter}</span>
            </button>
            <button
              disabled={index === siblings.length - 1}
              onClick={() => navigate(`/problem/${siblings[index + 1].slug}`)}
            >
              <span>{siblings[index + 1]?.tag || 'Next'}</span>
              <ArrowRight size={16} />
            </button>
          </div>
        </article>
        <aside className="problem-sidebar">
          {!!related.length && (
            <div className="aside-panel">
              <h2>
                <GitBranch size={16} /> References
              </h2>
              {related.map((r) => (
                <div className="related-exercise" key={r.id}>
                  <ExerciseReference
                    problem={r}
                    currentBook={p.book}
                    onNavigate={navigate}
                  />
                  <NewTab
                    onClick={() => navigate(`/problem/${r.slug}`, true)}
                    label={`Open ${r.id} in a new internal tab`}
                  />
                </div>
              ))}
            </div>
          )}
          <div className="aside-panel file-panel">
            <h2>
              <FileCode2 size={16} /> Files
            </h2>
            {p.files.map((file) => (
              <a key={file} href={asset(`${p.sourcePath}/${file}`)} download>
                <span>{file}</span>
                <Download size={14} />
              </a>
            ))}
          </div>
        </aside>
      </div>
    </>
  );
}
