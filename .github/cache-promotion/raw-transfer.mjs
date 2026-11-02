// PROPOSAL ONLY; custom JavaScript action entry point, never a shell step.
// Uses the exact shipped official @actions/cache 6.1.0 internals, not a protocol clone.
import fs from 'node:fs';
import path from 'node:path';
import {pathToFileURL} from 'node:url';
import crypto from 'node:crypto';
import {createReadStream} from 'node:fs';
const key = 'lean-Linux-X64-d791b020c21edcc7e9e22797f1d59fde59e8af8f675af62dc2f1fd7521bfef93-89d6106bc6c779e9737fee10c1c69f89008822de7c0ccaf47ee2412f3aae0bb2-88bab48f8801b48464fe6cce9881c21713001009-41401104003-1-tests-1';
const expectedVersion = '60729729c15d65dc4080956c73ec44cfde33f5da3080769b8a3a093d958db6de';
const expectedSize = 6624993888;
const paths = ['./.lake', '/home/runner/work/_temp/lake-native-cache'];
async function sha256(file) {
  const h = crypto.createHash('sha256');
  for await (const chunk of createReadStream(file)) h.update(chunk);
  return h.digest('hex');
}
async function main() {
  const e = process.env;
  if (e.GITHUB_REPOSITORY !== 'kangxyz/aglib' || e.GITHUB_EVENT_NAME !== 'workflow_dispatch' ||
      !['export', 'seed'].includes(e.RAW_PHASE) || e.RUNNER_TEMP !== '/home/runner/work/_temp') throw Error('guard');
  const requiredRef = e.RAW_PHASE === 'export' ? 'refs/heads/etale-abstract' : 'refs/heads/main';
  if (e.GITHUB_REF !== requiredRef) throw Error('scope');
  // Install with actions/cache's pinned complete lockfile via npm ci --ignore-scripts
  // --omit=dev. NODE24 action runtime supplies the normal feature/main runtime auth.
  const root = path.resolve(e.OFFICIAL_CLIENT_ROOT);
  const pkg = JSON.parse(fs.readFileSync(path.join(root, 'package.json')));
  if (pkg.name !== '@actions/cache' || pkg.version !== '6.1.0') throw Error('client');
  const load = p => import(pathToFileURL(path.join(root, 'lib', p)).href);
  const utils = await load('internal/cacheUtils.js');
  const client = await load('internal/shared/cacheTwirpClient.js');
  const http = await load('internal/cacheHttpClient.js');
  const config = await load('internal/config.js');
  if (config.getCacheServiceVersion() !== 'v2') throw Error('requires official v2 client');
  const compression = await utils.getCompressionMethod();
  const version = utils.getCacheVersion(paths, compression, false);
  if (compression !== 'zstd-without-long' || version !== expectedVersion) throw Error('version');
  const archive = path.resolve(e.RAW_ARCHIVE);
  const twirp = client.internalCacheTwirpClient();
  if (e.RAW_PHASE === 'export') {
    const disk = fs.statfsSync(path.dirname(archive));
    if (Number(disk.bavail) * Number(disk.bsize) < expectedSize + 3_000_000_000 || fs.existsSync(archive)) throw Error('capacity/destination');
    const response = await twirp.GetCacheEntryDownloadURL({key, restoreKeys: [], version});
    if (!response.ok || response.matchedKey !== key) throw Error('exact cache unavailable');
    // Never print response, signed URL, runtime token or raw exception text.
    await http.downloadCache(response.signedDownloadUrl, archive, {useAzureSdk: true, downloadConcurrency: 2});
    if (fs.statSync(archive).size !== expectedSize) throw Error('archive size');
    console.log(JSON.stringify({phase: 'download-only', key, version, size: expectedSize, sha256: await sha256(archive)}));
  } else {
    if (e.TRANSPORT_VERIFIED !== 'true' || !/^[0-9a-f]{64}$/.test(e.EXPECTED_ARCHIVE_SHA256 ?? '') ||
        fs.statSync(archive).size !== expectedSize || await sha256(archive) !== e.EXPECTED_ARCHIVE_SHA256) throw Error('transport/digest');
    // Workflow must independently bind TRANSPORT_VERIFIED to the successful trusted
    // export+roundtrip run and exact artifact/manifest, not to a dispatch boolean.
    const targetKey = key + '-main-raw-' + e.GITHUB_RUN_ID + '-' + e.GITHUB_RUN_ATTEMPT;
    const response = await twirp.CreateCacheEntry({key: targetKey, version});
    if (!response.ok) throw Error('reserve');
    // Same shipped saveCacheV2 call; lower transfer concurrency bounds RAM.
    await http.saveCache(-1, archive, response.signedUploadUrl, {
      uploadChunkSize: 64 * 1024 * 1024, uploadConcurrency: 2,
      useAzureSdk: true, archiveSizeBytes: expectedSize
    });
    const done = await twirp.FinalizeCacheEntryUpload({key: targetKey, version, sizeBytes: String(expectedSize)});
    if (!done.ok || !/^[0-9]+$/.test(done.entryId)) throw Error('finalize');
    const found = await twirp.GetCacheEntryDownloadURL({key: targetKey, restoreKeys: [], version});
    if (!found.ok || found.matchedKey !== targetKey) throw Error('main lookup');
    console.log(JSON.stringify({phase: 'main-raw-seed', key: targetKey, version, id: done.entryId, size: expectedSize}));
    fs.appendFileSync(e.GITHUB_OUTPUT, `seed-key=${targetKey}\nseed-id=${done.entryId}\n`);
  }
}
try { await main(); } catch { console.error('Raw cache transfer failed; no extraction or compilation fallback. Inspect nonsecret phase diagnostics.'); process.exitCode = 1; }
