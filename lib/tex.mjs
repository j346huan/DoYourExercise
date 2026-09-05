// Small, explicit TeX-fragment parser. Unknown commands remain visible as text.
export function parseTex(input, depth = 0) {
  if (depth > 32) return [{ kind: 'text', value: input }];
  const nodes = [];
  let i = 0,
    buffer = '';
  const flush = () => {
    if (buffer) {
      nodes.push({ kind: 'text', value: buffer });
      buffer = '';
    }
  };
  const group = (start) => {
    let level = 1,
      j = start + 1;
    for (; j < input.length; j++) {
      if (input[j] === '\\') {
        j++;
        continue;
      }
      if (input[j] === '{') level++;
      if (input[j] === '}' && !--level)
        return [input.slice(start + 1, j), j + 1];
    }
    return null;
  };
  const closing = (needle, start) => {
    let p = input.indexOf(needle, start);
    while (p >= 0) {
      let slashes = 0;
      for (let k = p - 1; k >= 0 && input[k] === '\\'; k--) slashes++;
      if (slashes % 2 === 0) return p;
      p = input.indexOf(needle, p + needle.length);
    }
    return -1;
  };
  while (i < input.length) {
    const rest = input.slice(i);
    if (rest.startsWith('%')) {
      const end = input.indexOf('\n', i);
      i = end < 0 ? input.length : end;
      continue;
    }
    const para = rest.match(/^\n\s*\n/);
    if (para) {
      flush();
      nodes.push({ kind: 'paragraph' });
      i += para[0].length;
      continue;
    }
    const delim = rest.startsWith('$$')
      ? ['$$', '$$', true]
      : rest.startsWith('\\[')
        ? ['\\[', '\\]', true]
        : rest.startsWith('\\(')
          ? ['\\(', '\\)', false]
          : rest.startsWith('$')
            ? ['$', '$', false]
            : null;
    if (delim) {
      const end = closing(delim[1], i + delim[0].length);
      if (end >= 0) {
        flush();
        nodes.push({
          kind: 'math',
          value: input.slice(i + delim[0].length, end),
          display: delim[2],
        });
        i = end + delim[1].length;
        continue;
      }
    }
    const environment = rest.match(
      /^\\begin\{(align\*?|equation\*?|gather\*?|enumerate|itemize)\}/,
    );
    if (environment) {
      const name = environment[1],
        end = input.indexOf(`\\end{${name}}`, i + environment[0].length);
      if (end >= 0) {
        flush();
        const body = input.slice(i + environment[0].length, end);
        if (name === 'enumerate' || name === 'itemize') {
          nodes.push({
            kind: 'list',
            ordered: name === 'enumerate',
            items: body
              .split(/\\item(?:\[[^\]]*\])?\s*/)
              .slice(1)
              .map((t) => parseTex(t.trim(), depth + 1)),
          });
        } else {
          const env = name.startsWith('align')
            ? 'aligned'
            : name.startsWith('gather')
              ? 'gathered'
              : null;
          nodes.push({
            kind: 'math',
            display: true,
            value: env ? `\\begin{${env}}${body}\\end{${env}}` : body,
          });
        }
        i = end + `\\end{${name}}`.length;
        continue;
      }
    }
    const command = rest.match(/^\\(exref|textbf|emph|textit|texttt|label)\{/);
    if (command) {
      const data = group(i + command[0].length - 1);
      if (data) {
        flush();
        const [value, end] = data;
        if (command[1] === 'exref') nodes.push({ kind: 'reference', value });
        else if (command[1] === 'texttt') nodes.push({ kind: 'code', value });
        else if (command[1] !== 'label')
          nodes.push({
            kind: command[1] === 'textbf' ? 'bold' : 'italic',
            children: parseTex(value, depth + 1),
          });
        i = end;
        continue;
      }
    }
    const wrapper = rest.match(/^\\(?:begin|end)\{(?:document|proof)\}/);
    if (wrapper) {
      i += wrapper[0].length;
      continue;
    }
    if (rest[0] === '\\' && '%&_$#{}'.includes(rest[1] || '\0')) {
      buffer += rest[1];
      i += 2;
      continue;
    }
    if (rest.startsWith('\\\\')) {
      flush();
      nodes.push({ kind: 'break' });
      i += 2;
      continue;
    }
    buffer += input[i] === '~' ? '\u00a0' : input[i];
    i++;
  }
  flush();
  return nodes;
}
