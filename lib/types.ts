export type Status = 'unsolved' | 'solved' | 'formalized';
export interface Book {
  id: string;
  title: string;
  shortTitle: string;
  authors: string;
  year: number;
  description: string;
  kind: 'sample' | 'planned' | 'textbook';
  cover: string | null;
  coverCredit: string | null;
  coverSource?: string;
  chapters: {
    id: string;
    title: string;
    sections?: { id: string; title: string }[];
  }[];
}
export interface Problem {
  id: string;
  slug: string;
  book: string;
  bookTitle: string;
  tag: string;
  chapter: string;
  chapterTitle: string;
  section: string | null;
  sectionTitle: string | null;
  number: string;
  title: string;
  tags: string[];
  status: Status;
  sample: boolean;
  coverage?: 'proof' | 'partial' | 'empty';
  source?: {
    url: string;
    pages: number[];
    label: string;
    statement: 'summary' | 'missing';
  };
  updated: string;
  dependencies: string[];
  statement: string;
  files: string[];
  sourcePath: string;
  lean: { module: string; verified: boolean } | null;
}
export interface Catalog {
  version: number;
  books: Book[];
  problems: Problem[];
}
export interface WorkspaceTab {
  id: string;
  route: string;
}
export interface WorkspaceState {
  tabs: WorkspaceTab[];
  active: string;
}
