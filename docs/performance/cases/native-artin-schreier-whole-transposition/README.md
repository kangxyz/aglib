# Native Artin–Schreier: whole transposition before specialization

## Question and source basis

This case records the compiler failure and repair of
`primeFieldToAdditive_artinSchreierMap` in
`Aglib/Algebra/Category/Ring/Sheaf/ArtinSchreier.lean`, together with the two
already-refactored Scheme wrappers `Frobenius` and `Constants`. It records
source-supported implementation changes and existing compiler observations;
mathematical acceptance remains with the mathematical author and principal.

The native source basis is HEAD `54d6974ace11bf7d197aa925cb8cade86db8a24f`,
Lean 4.34.1, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The lower source sequence starts at SHA256
`6b222b8bb76624073d7c98672f9a0931eddc78e51a013c0c93ae7dbbbbe7882c`.
The [source capsule](source-capsule.json) retains one baseline and six exact
consecutive patches, their before/after hashes, wrapper source hashes and full
SOURCE archive locators. Full manifests remain at their hash-bound research
workspace locators rather than being copied into this case.

## Failed attempts and diagnostic progression

| Run prefix | Input/repair | Recorded result |
| --- | --- | --- |
| `486cfa35` | initial `6b222b8b` | Local notation quotations rejected explicit-universe and anonymous-constructor syntax; later notation errors were cascades. Repair 1 replaced them with typed aliases for the same native values. |
| `46f990d7` | repair 1 `8cf60bf9` | Alias declaration universes redeclared ambient names. Repair 2 used fresh declaration-local names, retaining independent worlds. |
| `dfdf9bea` | repair 2 `f71d888b` | Association rewriting after an eager target change encountered the constant-sheaf/sheafify carrier boundary. Repair 3 kept the original typed presheaf and sheaf, proved the whole presheaf composite zero and used native HomEquiv transport. |
| `8e5b2c8d` | repair 3 `b6757edf` | Raw `comp_zero` did not match `E 0 = 0`. Repair 4 explicitly normalized the native HomEquiv and unit composite. A separate Proper import failure in this request has another owner. |
| `64d200f1` | repair 4 `4d4bf8cf` | Declaration-level `whnf` timeout at 200,000 heartbeats; this log alone did not locate the proof phase. Repair 5 used native adjunction additivity and inverse-zero instead of the concrete unit-zero/injectivity chase. |
| `a5e3496e` | repair 5 `4f745918` | Actual lower-file `whnf` timeout at 200,000; the requested wrappers did not obtain closure from this failed dependency. |
| `9b504c76` | phase probe on repair 5 | Faithful formation completed, then every actual proof marker reached before the final transport. The final `exact` failed; see below. |
| `ca150085` | repair 6 `87ff6356` | Actual lower-file build passed: one observed frontend, request elapsed 13.083733 seconds. |
| `03a7acc9` | fixed wrappers | Both actual wrapper builds passed: two observed frontends, request elapsed 11.128496 seconds. |

The full run IDs, commands, exit codes, elapsed times and admission ceilings
are in [case.json](case.json), with raw receipts, logs and wrapper events in
`evidence/`. Reports and manifests in `repairs/` are historical fixed author
packets: their then-uncompiled/READY wording is preserved. The last two closed
receipts supply the later build results only for their matching sources.

## What the phase probe establishes

The probe puts the actual proposition in a theorem binder `(_h : P) : True`,
then instruments the original proof. Its formation header, value and named
Kernel check completed. The actual proof reached body entry, `after-hz`,
`after-left-additive-instance`, `after-native-zero` and `before-final-transport`.
The final `exact` took 19.6 seconds and hit the standard 200,000 `whnf` limit;
the actual theorem's value elaboration failed, and no named Kernel check of
that theorem appeared. The cumulative 10 ms kernel/type-checking summary
covers formation, prefix and auxiliary work, not a successful check of the
actual Artin–Schreier theorem.

This locates the observed frontier at the final concrete native-naturality,
congruence and transitivity specialization or its expected-type conversion.
The preceding ring calculation, additive dictionary and native zero law had
elaborated before the failure. Aggregate counts included 403,629 unfoldings
each of `presheafToSheaf`, `Functor.leftAdjoint` and `Classical.choose`, and
551,734 of `Classical.indefiniteDescription`. Those counts do not identify the
exact compared expression pair or time spent per constant.

The probe's receipt records zero *wrapper-observed* frontend invocations;
its `lake --no-build env lean -j4 -M12800` command and emitted compiler log show
the actual diagnostic frontend. Zero wrapper events do not mean no compiler
ran. Probe inputs and instrumentation are retained under `probe/`.

## Effective repair and retained hypotheses

Repair 6 moves the complete equation to private `transpose_comp_eq_zero`,
over variable preadditive categories and the same variable adjunction. Its
inputs are the actual arrows `i`, `k`, `g`, the whole transposition equation
`(adj.homEquiv P A) k = i`, and the original presheaf equation
`i ≫ U.map g = 0`. Its output is exactly the original `k ≫ g = 0`.
Native naturality has explicitly pinned `X`, `Y` and `Y'`; the helper uses
HomEquiv injectivity, naturality, the supplied whole equation and native
`homAddEquiv_zero`. It does not return a newly reconstructed inverse-HomEquiv
map for the caller to compare.

The actual caller pins the original `P₀`, `A₀`, `i₀`, `k₀` and `g₀`. It obtains
`hk₀` from the existing `toSheafify_primeFieldToAdditive` unit law and retains
the same `map_pow`, `ZMod.pow_card`, `sub_self` calculation for `hz`. Right
additivity is the existing native sheaf inclusion; left additivity follows
from that same adjunction. Thus the helper's equations are discharged from
the original data, rather than becoming new public desired-law premises.

The existing `HasWeakSheafify`, characteristic equation (including zero-ring
scope), independent site/ring/lift universes, selected native presheaf/sheaf
pair, original maps and unit remain. No additional point, model, realization,
record, public premise, suppression, transparency option or heartbeat increase
is introduced. The exact change is [repair 6](repairs/6/repair.patch), with
prior failed changes retained alongside it.

The fixed mathematical author's [explanation](author/explanation.md) and
[evidence index](author/evidence.json) are retained with hash bindings in the
capsule. This writeup follows that argument; it supplies no independent proof
verdict. The unchanged Scheme wrappers preserve the original section rings,
constant-sheaf coefficients, native unit, old fully qualified names and literal
Frobenius/Artin–Schreier values. No local injectivity, kernel, epimorphism or
exactness assertion is added.

## Successful coverage and limits

Final generic SHA256:
`87ff6356a978b2998455b6ea671dbfdf3cb09f65a7785282ebe8b7aba4e4b9ec`.
Frobenius SHA256:
`5be6b57f14457bda311e65781e412dd7414d43ac6c435217c4d480340a45c922`.
Constants SHA256:
`d2a7c7461e034f05b03adb49fa49b6fc6fab4eb440a45ded2cd2d0ec59ee8fca`.
Both successful SOURCE archives contain these same three hashes. The wrapper
SOURCE archive SHA256 is
`885a7b8db32f0084547af09ea4dae478d3575ee51b7634570d2ff15a3c32a1f9`.

The successful requests admitted two jobs, four threads and a 12,800 MiB
frontend cap, with a 32,768 MiB run ceiling. Earlier failures admitted eight
jobs and a 110,592 MiB run ceiling; their frontend cap and thread count were
the same. The diagnostic additionally enabled its documented scoped traces.
Standard 200,000 heartbeats and default trust were retained. These are
unmatched incremental requests with cached dependencies, not a controlled
before/after benchmark. Lake's lower-file job display was 3.9 seconds; the
wrapper displays were 3.5 and 4.2 seconds, distinct from request elapsed times.
Untouched `Injective`, `Complex`, `Surjective` and `ShortExact` modules, the
complete AS sequence and overall étale migration are outside this coverage.
No per-file RSS, matched speedup, exact reduction-pair, whole-library result,
all-proofs budget guarantee or unchanged downstream closure is asserted.
The stored build coverage does not add standalone lint, tests, axiom audits,
kernel replay or separate client certification. No new compilation or profiling
was performed to write this record.

## Reproduction and evidence use

For source reconstruction, copy `sources/initial.lean` into a disposable tree
at `Aglib/Algebra/Category/Ring/Sheaf/ArtinSchreier.lean`, then apply
`patch -p1 < <case>/repairs/1/repair.patch` through repair 6 from that tree's
root. Compare each intermediate SHA256 with `source-capsule.json`; repair 5
is the diagnostic basis and repair 6 the successful lower source. The capsule
also binds the probe and unchanged wrappers. This is source reconstruction,
not a request for another acceptance cycle.

The recorded native commands were `lake --rehash build
Aglib.Algebra.Category.Ring.Sheaf.ArtinSchreier`, then `lake --rehash build
Aglib.AlgebraicGeometry.EtaleCohomology.ArtinSchreier.Frobenius
Aglib.AlgebraicGeometry.EtaleCohomology.ArtinSchreier.Constants`, on the
matching prepared dependencies and native configuration. Exact executables,
environments and observations remain in the receipts. Current operating
guides own any future invocation.
