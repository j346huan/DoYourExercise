import type { Metadata } from 'next';
import 'katex/dist/katex.min.css';
import './globals.css';
export const metadata: Metadata = {
  title: 'Do Your Exercise — A mathematical notebook',
  description:
    'A personal library of textbook exercises, natural-language proofs, and Lean 4 formalizations.',
};
export default function RootLayout({
  children,
}: {
  children: React.ReactNode;
}) {
  return (
    <html lang="en" className="dark">
      <body>{children}</body>
    </html>
  );
}
