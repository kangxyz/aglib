> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#local-validation-and-shared-artifact-link-metadata) · [Context](original-context.md) · [Case index](README.md) · [Previous record](ci-cache-reuse-across-dependency-updates.md) · [Next record](test-dependency-handoff-and-native-resource-limits.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Local validation and shared-artifact link metadata

The local input guard treated every ctime change as input drift. Creating or
removing a hardlink in a peer workspace changes the shared inode's ctime without
changing its content or mtime. A completed native command could therefore be
rejected before its success was recorded, repeatedly delaying the axiom audit.
A temporary-file reproduction produced the exact `Reflective input changed
during this attempt` error with unchanged hash, size and mtime.

The unified toolkit now treats ctime-only native changes as hash-cache misses:
rehash and retain a check only when content and lookup identity still agree.
Source/configuration temporal guards remain strict; genuine native-content,
inode, mtime, mode, symlink, disappearance and shadowing changes still fail.
Native evidence follows CI's trusted-producer content-correspondence contract
at observation boundaries, without claiming continuous mutation certification.
Existing compatible native check records keep their bindings. Ordinary checker
or Test failures collect independent axiom feedback and retain successful
categories for the retry; they do not authorize a successful aggregate result.

The active source, generator, cache and build implementations from all three
libraries now live in one `lean_tools` package. Thin current callers select
that package instead of importing retired scripts or checking old helper hashes.
The bounded regressions cover link activity during hashing/lint/reuse/export,
real mutations, failed checks, cancellation and managed-profile preservation.
A real Lean 4.34.1 import with 3902 observed native files passed while a peer
performed 210 hardlink operations; the before/after content binding agreed.
Scratch-installed package invocations exercise Git-free fixtures and the actual
three-library source entries, including reuse without rerunning those checks. These are tooling
results; no full mathematical rebuild or new acceptance cycle is assigned.

