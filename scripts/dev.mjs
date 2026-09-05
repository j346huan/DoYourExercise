import { spawnSync, spawn } from 'node:child_process';
import { watch } from 'node:fs';
function index() {
  return (
    spawnSync(process.execPath, ['scripts/build-content.mjs'], {
      stdio: 'inherit',
    }).status === 0
  );
}
if (!index()) process.exit(1);
const server = spawn(
  process.execPath,
  ['node_modules/vinext/dist/cli.js', 'dev', ...process.argv.slice(2)],
  { stdio: 'inherit' },
);
let timer;
const watcher = watch('content', { recursive: true }, () => {
  clearTimeout(timer);
  timer = setTimeout(index, 200);
});
server.on('exit', (code) => {
  watcher.close();
  process.exit(code || 0);
});
for (const signal of ['SIGINT', 'SIGTERM'])
  process.on(signal, () => {
    watcher.close();
    server.kill(signal);
  });
