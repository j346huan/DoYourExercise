'use client';
import React, { useMemo } from 'react';
import katex from 'katex';
import {
  HoverCard,
  HoverCardTrigger,
  HoverCardContent,
} from '@/components/ui/hover-card';
import { SquarePlus, ArrowUpRight } from 'lucide-react';
import type { Catalog, Problem } from '@/lib/types';
import { resolveReference, referenceLabel } from '@/lib/core.mjs';
import { parseTex } from '@/lib/tex.mjs';
export function MathFragment({
  text,
  display = false,
}: {
  text: string;
  display?: boolean;
}) {
  const html = useMemo(() => {
    try {
      return katex.renderToString(text, {
        displayMode: display,
        throwOnError: true,
        trust: false,
        strict: 'warn',
        maxExpand: 1000,
        output: 'htmlAndMathml',
      });
    } catch {
      return null;
    }
  }, [text, display]);
  return html ? (
    <span
      className={display ? 'math-display' : 'math-inline'}
      dangerouslySetInnerHTML={{ __html: html }}
    />
  ) : (
    <code className="math-error" title="This expression could not be typeset">
      {text}
    </code>
  );
}
export function ExerciseReference({
  problem,
  currentBook,
  onNavigate,
  children,
}: {
  problem: Problem;
  currentBook: string;
  onNavigate: (route: string, newTab?: boolean) => void;
  children?: React.ReactNode;
}) {
  const route = `/problem/${problem.slug}`;
  return (
    <HoverCard>
      <HoverCardTrigger
        href={`#${route}`}
        className="exercise-reference"
        onClick={(e: React.MouseEvent) => {
          if (!e.ctrlKey && !e.metaKey && !e.shiftKey) {
            e.preventDefault();
            onNavigate(route);
          }
        }}
      >
        {children || referenceLabel(problem, currentBook)}
      </HoverCardTrigger>
      <HoverCardContent className="reference-preview" sideOffset={10}>
        <div className="preview-label">
          EXERCISE {problem.tag}{' '}
          <span className={`status ${problem.status}`}>{problem.status}</span>
        </div>
        <strong>{problem.title}</strong>
        {problem.source?.statement === 'summary' && (
          <p className="preview-summary-label">
            Statement summary from the author’s notes
          </p>
        )}
        <div className="preview-statement">
          <TexContent text={problem.statement} book={problem.book} />
        </div>
        <div className="preview-actions">
          <button onClick={() => onNavigate(route)}>
            <ArrowUpRight size={15} /> Read exercise
          </button>
          <button onClick={() => onNavigate(route, true)}>
            <SquarePlus size={15} /> New tab
          </button>
        </div>
      </HoverCardContent>
    </HoverCard>
  );
}
interface TexNode {
  kind: string;
  value?: string;
  display?: boolean;
  children?: TexNode[];
  ordered?: boolean;
  items?: TexNode[][];
}
export function TexContent({
  text,
  book,
  catalog,
  onNavigate,
}: {
  text: string;
  book: string;
  catalog?: Catalog;
  onNavigate?: (route: string, newTab?: boolean) => void;
}) {
  function render(nodes: TexNode[]): React.ReactNode[] {
    return nodes.map((node, i) => {
      if (node.kind === 'math')
        return (
          <MathFragment key={i} text={node.value!} display={node.display} />
        );
      if (node.kind === 'reference') {
        const p = catalog?.problems.find(
          (p) => p.id === resolveReference(node.value, book),
        );
        return p && onNavigate ? (
          <ExerciseReference
            key={i}
            problem={p}
            currentBook={book}
            onNavigate={onNavigate}
          />
        ) : (
          <span key={i} className="exercise-reference">
            ({node.value})
          </span>
        );
      }
      if (node.kind === 'bold')
        return <strong key={i}>{render(node.children!)}</strong>;
      if (node.kind === 'italic')
        return <em key={i}>{render(node.children!)}</em>;
      if (node.kind === 'code') return <code key={i}>{node.value}</code>;
      if (node.kind === 'paragraph')
        return <span className="paragraph-break" key={i} />;
      if (node.kind === 'break') return <br key={i} />;
      if (node.kind === 'list') {
        const items = node.items!.map((item, j) => (
          <li key={j}>{render(item)}</li>
        ));
        return node.ordered ? (
          <ol key={i}>{items}</ol>
        ) : (
          <ul key={i}>{items}</ul>
        );
      }
      return <React.Fragment key={i}>{node.value}</React.Fragment>;
    });
  }
  return (
    <div className="tex-content">
      {render(parseTex(text.trim()) as TexNode[])}
    </div>
  );
}
