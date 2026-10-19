# Incremental CI contract

CI validates the current committed source. Its success means that every required
check has either completed on its actual inputs or has compatible, retained
success evidence. Missing, failed, partial, stale or unrecognized evidence cannot
establish success. An earlier push is not a verification baseline.

The standalone CI core owns planning, execution records and final acceptance.
The GitHub workflow supplies the checkout, pinned runtime, cache transport and
core invocations. A skipped workflow step cannot waive a core requirement.

## Planning and coverage

A baseline must be an ancestor with identifiable successful native validation.
Source-only green runs, failed runs and the former previous-push incremental
protocol cannot supply that evidence. Explicit manual comparisons can widen a
verified range, but cannot advance over unverified changes. Missing usable
history fails with a recovery diagnostic; it does not select an empty scope or
an implicit whole-library rebuild.

The core independently compares the mathematical source and configuration
snapshots. It cannot accept an empty native scope for changed mathematical
inputs. A source-only run can inherit mathematical coverage only when those
inputs match its verified baseline. Logs and final coverage identify the exact
source, baseline and supporting run.

Native completion includes validation of the current library and positive-test
root graph, in addition to the selected declaration, text-style and origin/axiom
checks. Applicable independent-client compilation and its audit remain required.
The finalizer reconstructs the required phases and checks their source-bound
completion; it does not accept a caller-supplied success flag.

## Incremental compilation

Lake owns compilation dependency and artifact identity. The CI core uses the
pinned compiler and native `--rehash` validation, retaining source, dependency,
option and toolchain checks. Python does not replace Lake's dependency hashes
with Git diffs or timestamps. Git differences help select additional checks and
bound cache recovery; they cannot certify compiled artifacts.

Matching compiled outputs from earlier partial runs remain reusable. Required
cold imports first use matching cache recovery. A missing unrelated cache is an
explicit recovery gap, not permission to rebuild an unrelated forest. Native
frontends remain serialized under the existing compiler and owned-process-group
resource limits.

## Independent check progress

A matching build trace certifies neither builtin/declaration lint nor an axiom
audit. Reusable success records must bind the actual selection, validated native
module identities and outputs, checker implementation, policy, arguments and
other consumed inputs. Text-based checks must also bind raw source inputs; a
normalized compiler text hash alone is insufficient.

Reflective checks can inspect imported private proofs that are absent from a
compiler's public dependency interface. Their keys therefore follow all explicit
imports from validated `.ilean` version 5 metadata and bind the full relevant
artifact families and checker/runtime closure. Import flags do not cut this
closure. Resolution uses the actual ordered search paths, including `Init` and
workspace shadows; the actual compiler installation is bound separately.
Unsupported metadata disables reuse and selects the actual check. This rule
assumes standard Lake setup rather than custom import overrides.

Artifact discovery and content hashing are shared within a phase. Each check
uses its relevant closure, so an unrelated repair does not invalidate a valid
success. Temporal file observations also reject mutation, including changed and
restored inputs, while keeping modification times out of cross-run content keys.

Only a completed command with a successful resource receipt can create a native
check success record. The inputs must remain compatible through completion.
Records are retained incrementally so a later failure does not erase earlier
success. Missing, corrupt, incompatible or failed records are cache misses and
require the actual check; they cannot cover it. Cheap source/style checks may run
again instead of using an inadequately bounded reuse rule.

Build and check caches retain the repository's trusted-producer boundary. Native
Lake hashes describe ordinary incremental build identity; they are not an
adversarial authentication scheme. No cache record is committed as a substitute
for source or mathematical premises.

## Final result

Partial progress can be retained after failure, but it is not a complete
validation certificate. Complete coverage is emitted only after every required
phase has passed or has justified compatible coverage, source/configuration
stability has been checked, and the native graph requirement has been met.

The result distinguishes fresh execution, reused check success and inherited
unchanged-source coverage. Ordinary code validation does not claim additional
independent kernel replay or mathematical adoption; those remain governed by the
[formalization acceptance policy](DEVELOPMENT.md#kernel-replay-at-mathematical-adoption).
