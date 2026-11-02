# Diagnose bare loader read errors before rebuilding artifacts

This is a validated diagnosis of an instrumented failure, not a successful resource repair, audit, lint or hosted CI run. It concerns the frozen source content SHA-256 `fadfd749ca286b281cae778f3b7ea7836e4adbb5df8a1129c38b6fa7fe40b0b4`, Q HEAD `05b8c4704abf0759cfdac5f5ddabe440dc73874b`, Lean 4.34.1 (`5045d00`), Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, and axiom auditor `46024e005996495c65ef609368e11ab39c4222e3`. The native profile was jobs 8, threads 4, M 12800 and RSS 65536. Later Q HEAD `7d071440653407d30fd41d8dbbafce1673a3039b` incorporates unchanged fixed paths on a newer foreign Ext/CompactSupport basis; this diagnosis does not assert an audit pass there.

## Source reconstruction

The frozen mathematical inputs can be reconstructed from Q commit `05b8c4704abf0759cfdac5f5ddabe440dc73874b` and the 11-path patch in `evidence/source-delta.patch`. That patch is the difference between `7d071440653407d30fd41d8dbbafce1673a3039b` and its parent `a856ac0fbb1d1deb8ff7dc6eb3a389dee8520639`; the parent’s foreign Ext/CompactSupport additions are disjoint from those 11 paths. The retained source guard lists the 11 resulting file SHA-256 hashes, each matched against the later commit. The native `fadfd749…` SOURCE content digest belongs to the native capture protocol; it is distinct from a Git tree hash. Its captured inputs retain their own receipt binding. Applying the patch to the old base reconstructs the recorded changed-path content, not the later foreign additions or an audit result.

## Initial failure and file evidence

In phase `remote-4de18255c0f147f6840ba94808626277`, native lint and the pinned axiom audit reported bare `failed to read file` messages. The phase exited 1; its receipt recorded 184 compiler successes, zero compiler failures, no input drift and no cgroup OOM event delta. The operator reported the implicated artifacts present and readable in mode 0444 before the phase; prior restoration records concern an earlier source. This evidence did not establish missing artifacts or a restoration gap. It superseded an initial missing-file interpretation for this phase, without changing the earlier cache-sidecar evidence. See `evidence/diagnosis.json` for file sizes, dates, original receipt and log locators and their hashes. The operator's file observation was not independently repeated.

The pinned [Lean 4.34.1 loader](https://raw.githubusercontent.com/leanprover/lean4/v4.34.1/src/library/module.cpp) distinguishes open, stat and header errors from the bare fallback error. At lines 485–503 it attempts a mapping; at 517–523, if no buffer is available, it calls `malloc`, then `readn` without checking the allocation result. A failed or short fallback read emits the bare message. The official source was inspected; the supplied local toolchain source path was unavailable in this checkout.

## Resource and terminal observations

An uninstrumented sampled audit `remote-088f37db5b0d45b0b3c0a75087bd9e90` exited 2. The auditor reached 65,492 sampled mappings, 12 file descriptors and 2,538,288 KiB RSS; `vm.max_map_count` was 65,530, `RLIMIT_NOFILE` 1,024 soft / 1,048,576 hard, and `RLIMIT_AS` unlimited. Sampling establishes proximity, not the terminal syscall or a unique cause. The exact command and samples are in `evidence/resource-observation.json`.

The corrected failures-only, process-scoped observer in `remote-e449de2e75e9497fab2aead25fc1a495` ran the same audit command and source/predicate with the original allocator, without global, source or cache changes. It exited 2. The terminal log recorded 487 `mmap` failures with `ENOMEM` and a read on fd 11 requesting 717,416 bytes with a NULL buffer, returning -1 / `EFAULT`. The named `.olean.private` file then produced the bare error. The auditor reached 65,347 sampled mappings and 2,517,868 KiB RSS. Together with the source branch, these observations identify a NULL-buffer fallback read after allocation failure in this instrumented run. Near-limit mappings support map pressure as a route; they do not establish `vm.max_map_count` as the sole or universal cause. Instrumentation can affect execution and this is not hosted CI validation. The earlier logger `073a2ca` exhausted its 64 slots before the terminal read and is not terminal-errno evidence.

The audit command was:

```sh
/root/autodl-tmp/lean-build/elan/toolchains/leanprover--lean4---v4.34.1/bin/lake env /root/autodl-tmp/lean-build/tools/axiom-audit-46024e005996/.lake/build/bin/axiom-audit --root Aglib
```

The command identifies the original remote environment, not a portable replay. `evidence/RESULT.json`, the full small observer log, logger control, source, commands, receipt and build log retain the observed invocation and binding. The observer binary hash was `342f8f6646dd1b0356e0bc91682a92eb9f167e258226904f266565eae20bfc1a`; the binary is not included in the source packet.

## Failed allocator trial and practical method

A separate process-only glibc 2.35 trial `remote-a4d489d58bdd4033b7dfb25e10383eab` set `glibc.malloc.mmap_max=0:glibc.malloc.arena_max=1` for the child. With the same audit, source, pins, predicate and global limits, it exited 2 with another bare read failure; sampled peak mappings were 62,501 and RSS 2,409,948 KiB. No terminal errno was captured in this trial. It did not validate an allocator repair. Full receipt and build log are retained in the support packet.

For a similar error, first distinguish import/loader I/O from a source or audit-predicate failure. Check the actual files and the pinned loader's error branch, then measure mappings, file descriptors and RSS against the process limits. If existing feedback cannot guide repair, a scoped failures-only syscall observation can identify the terminal event; reserve terminal failure log slots so earlier events cannot fill the log. Do not respond by blindly clearing caches, rebuilding artifacts or changing global settings. A process-only observer is a troubleshooting instrument, not a blanket CI configuration. A repair and its actual lint/audit/CI coverage remain separate obligations.

## Evidence and publication

The adjacent `evidence/` packet contains complete small captured logs and receipts, exact observer/control source and command metadata, diagnostic summaries and `SHA256SUMS`; it excludes binary artifacts and unrelated traces. The original retained captures remain at `R/migration/ci-repair-20261030/` under the paths in `evidence/diagnosis.json` and `evidence/RESULT.json`. This case and its adjacent `evidence/` directory are published together; their original captured provenance remains unchanged. Verify the packet with `shasum -a 256 -c SHA256SUMS` from the evidence directory.
