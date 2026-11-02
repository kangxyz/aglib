import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';

export const CAP_BYTES = 10_000_000_000;
// Evaluated in the official checkout so package import uses its locked SDK.
// Then change back to the package workspace, preserving official path/version
// semantics. No private client API, cache format or credential handling appears.
export const SDK_SAVE_PROGRAM = `
import {saveCache} from '@actions/cache';
import fs from 'node:fs';
process.chdir(process.env.GITHUB_WORKSPACE);
try {
  const id = await saveCache(['./.lake', process.env.RUNNER_TEMP + '/lake-native-cache'],
                             process.env.CACHE_SAVE_KEY);
  if (!Number.isSafeInteger(id) || id <= 0) throw Error('No finalized cache ID');
  fs.appendFileSync(process.env.GITHUB_OUTPUT, 'cache-id=' + id + '\\n');
} catch {
  console.error('Capped official cache save failed; no cache-delivery success claimed.');
  process.exitCode = 1;
}
`;

// Exported only to exercise the same spawn/cap boundary with tiny offline stubs.
// The action entry point below always supplies the fixed production cap.
export function runBoundedSave({sdkDirectory, capBytes, limiter='prlimit', env=process.env}) {
  return spawnSync(limiter, [`--fsize=${capBytes}:${capBytes}`, '--', process.execPath,
    '--input-type=module', '--eval', SDK_SAVE_PROGRAM],
    {cwd:sdkDirectory, env, stdio:'inherit'});
}

function main() {
  if (process.platform !== 'linux' || process.env.GITHUB_REPOSITORY !== 'kangxyz/aglib'
      || process.env.GITHUB_REF !== 'refs/heads/main') throw Error('Unsupported cache-save context');
  const sdkDirectory = process.env.SDK_DIRECTORY;
  const pkg = JSON.parse(fs.readFileSync(path.join(sdkDirectory,'node_modules/@actions/cache/package.json')));
  if (pkg.name !== '@actions/cache' || pkg.version !== '6.1.0') throw Error('Wrong official SDK');
  if (!process.env.CACHE_SAVE_KEY || process.env.CACHE_SAVE_KEY.length > 512) throw Error('Missing cache key');
  for (const root of [process.env.GITHUB_WORKSPACE,process.env.RUNNER_TEMP]) {
    const s=fs.statfsSync(root);
    if (Number(s.bavail)*Number(s.bsize) < CAP_BYTES+3_000_000_000 || Number(s.ffree)<100000)
      throw Error('Insufficient live room for capped compressed archive');
  }
  const result=runBoundedSave({sdkDirectory,capBytes:CAP_BYTES});
  if (result.error || result.signal || result.status !== 0) throw Error('Bounded save child failed');
}
if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try {main();} catch {console.error('Capped cache action failed; inspect phase diagnostics.');process.exitCode=1;}
}
