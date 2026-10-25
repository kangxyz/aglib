> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#picard-tangent-space-prove-additive-group-algebra-abstractly-then-specialize) · [Context](original-context.md) · [Case index](README.md) · [Previous record](hilbert-scheme-direct-images-compare-isomorphism-values-at-the-iso-level.md) · [Next record](preserve-exact-import-casing-across-native-platforms.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Picard tangent space: prove additive-group algebra abstractly, then specialize

At Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, a profiled remote build
of a pre-repair `Picard/Tangent/Thickening` (run `remote-ae44f9f482d946e99dbd5c68365a0ca5`,
source `1cc92cc3`, not retained; the receipt records a whole-cgroup average of 12.0 CPU cores,
and the author's observation of a host load of about 80 on 32 cores has no retained probe)
reported, among entries of at least 10 s, kernel type checking of 36.7 s at 188:4, 13.8 s at
199:8, 25.4 s at 206:4, 80.4 s plus 21.4 s of congruence-lemma generation at 261:0, seven
entries of 18.1–69.8 s at 276:4, 42.3 s and 24.4 s at 290:4 and 296:4, and linting of 339 s at
310:0. In that source the `AddEquiv` constructions `picardRetractionEquiv` and
`UnitsCohomologyComparison.kerEquiv` proved their fields with `abel` and `rw` directly over
`PicardGroup`; the positions cannot be checked against a retained file, so the mapping from
positions to declarations is the author's reading. An earlier pre-repair version (source
`4c1c686a`, not retained) took 487 s in run `remote-38bfcbc79b2f4fad8e40f15b57e17e46` (exit 1
on the `unnecessarySeqFocus` style linter at 141:7).

Candidate mechanism, not established: the kernel unfolds the `PicardGroup` additive structure
(tensor product, dual and the quotient by isomorphism) while checking `abel` and
structure-field proofs stated over `PicardGroup`. The profile attributes the time to kernel
checking of whole declarations, not to `abel`.

Repair: the additive-group algebra (`AddMonoidHom.retractionAddEquiv`,
`AddMonoidHom.kerAddEquivOfComm`, now in `Aglib/Algebra/Group/Subgroup/KerEquiv`) is proved
over abstract `[AddCommGroup A]`, and the Picard declarations specialize it once; the `rfl`
lemma `picardEquiv_apply_fst` was dropped. The repaired module built in 273 s
(`remote-6237c559e89345668abc9c12402a5620`), then in 247 s
(`remote-c8bf07378f894e029e5dc0ef76ac076f`) and finally 243 s
(`remote-7523f430ca654fb7a18559a29077b505`) (whole-cgroup averages 8.6, 10.4 and 11.1 CPU
cores in the receipts); after the review repairs, which moved the generic lemmas out, it built
in 244 s (`remote-9f484e84e2d34695ac803d74f5040b21`) (6.3 cores). These builds are not matched
measurements, and the repair's effect on single declarations was not measured.

Rule: prove additive-group algebra over an abstract `[AddCommGroup A]`, then specialize it once
to concrete heavy groups such as `PicardGroup`.

### Avoid self-referential coefficient simplification

In `RingTheory/IntegralClosure/RationalAdjunction`, the constant-polynomial
case has an equality `p = C (p.coeff 0)`. Supplying this equality to `simp`
also rewrites the occurrence of `p` inside its own coefficient, so the
simplifier recursively expands the same expression. Native run
`remote-d9ad38f59b5d491889b0ef3612dcb375` reports this nested recursion failure
for source `05138406d61dcba643c206696ecbabb366089ebc9156eaa8485eada66049cda9`.
The repair uses the equality once through `congrArg` and an explicit equality
composition. It preserves the original polynomial, evaluation map and kernel
statement, without changing options or budgets. Repaired source
`fc3ee6ad41878745a8d22b2b11e22fc06d1ae7790a81ab9b70fb7c8669360581`
passed the complete then-current lower module in 7.6 seconds in
`remote-7331ea0549b140b786dadc76bfcea3c0`; that parent graph failed other
modules. The later local-DVR extension has its own inputs and pending coverage.
These observations establish the repair on that source, with no controlled
timing ratio or broader performance conclusion.


### Use naturality before concrete scalar conversion

In [HomComplex/Cohomology](../../Aglib/Algebra/Homology/ModuleCat/HomComplex/Cohomology.lean),
concrete elementwise naturality and scalar conversion repeatedly exhausted
200000 heartbeats at `whnf` under Lean 4.34.1 and Mathlib `d13f23b`.
The initial `be6db054` candidate failed in `remote-33c87f3ac3c742a4b640a91089babd7a`.
Shared component constructors (`8a355`, `remote-84604fbebeea4fa5bbaaa61e55524a8d`)
and a complete natural isomorphism followed by concrete elementwise wrappers
(`bfb1`, `remote-61753936bd6e493faf8234a6e23a95a4`) still reached that limit.

The passing implementation proves the scalar law in the generic
`ModuleCat.natIsoAddEquivTransLinear`, retaining the whole functors and natural
isomorphism. It applies `F.map_smul` and `e.hom.naturality` at variable module
carriers, then specializes to `moduleHomologyFunctor` and the original
class-to-derived comparison. The two unpublished elementwise wrappers are
removed; categorical naturality and the original forward, cocycle and Ext
normalizations remain. The native module action is unchanged. Its actual
scalar supplier is documented and public so the exposed linear constructor
can use it.

Source `9e3a10f4519a8dcaada616c6664cb839a07797330801f15f1e26a744d05d68db`
passed the complete Coho module in 24 seconds in
`remote-2622eebf034a468da7c61bbba6623088`, source snapshot
`e70cfd2b09fb86cb84d5c627b1a9db3092ccd32baa60fea35da4209612532f7c`,
with standard package budgets and enabled compiler checks. The same graph
first reached `NormalCoefficient`, which failed separately. This records the
successful proof-construction boundary and removal of the observed timeout;
the runs do not isolate a compiler cause or provide a controlled timing ratio.
No extra diagnostic or benchmark run was made for this note.

### Retain the coefficient algebra in singleton-adjoin localization

The concrete `Algebra.isLocalization_adjoin_singleton` adapter in
[RationalAdjunction](../../Aglib/RingTheory/IntegralClosure/RationalAdjunction.lean)
exceeded the standard kernel heartbeat budget in `remote-ab2c32b2` and
`remote-873a3090`, after the evaluation and quotient-map presentation errors
were repaired. This is ordinary native proof checking, with Lean 4.34.1
and Mathlib `d13f23b`.

The retained proof checks the denominator criterion over variable rings,
then uses the same named `adjoinSingletonScalarExtensionAlgebra` in its
producer and concrete consumer. That class-valued definition carries the
native `instance_reducible` annotation. The actual singleton inclusion and
images of the original coefficient denominators remain unchanged. The
concrete adapter still requires a documented declaration-local
`maxHeartbeats 400000`; the generic criterion and package defaults remain
at 200000. The explaining comment follows `set_option ... in`, as required
by the native style linter.

The full lower module, source
`7f2f822b30ea2f484dbe2cb91b1cec28491a06329bc2112d37ca7480e10318e7`,
passed in 184 seconds in `remote-51cbdddab5e14ae58cf49cb3b351fc80`,
snapshot `ead84b86531b445f978a7bfb5b126f9db485b8a4b45d7fbd7ab69c595d8e43b8`.
That graph subsequently failed the newly reached upper Nagata adapter.
These observations support the retained representation and local allowance;
they do not isolate their individual costs or establish full finite-type
stability. No additional timing or diagnostic run was made for this note.


### Fix finite-subtype ranges before coefficient fields

In [FinitePureConstants](../../Aglib/FieldTheory/SeparablyGenerated/FinitePureConstants.lean),
transporting a separating basis into the original ambient field exhausted
200000 heartbeats at `whnf` in `remote-51cbddd` and `remote-b8aff27f`,
and 400000 in `remote-a00bf5e0`. Variable fields and a named proposition
alone had not resolved the dependent coefficient-field conversion.

The retained proof specializes `Subtype.range_coe` at the actual finite
source sets before forming the coefficient fields, passes the original
`N.val` inclusion explicitly, and transports native `IsSeparable` witnesses
by typed equalities such as `hbt` followed by substitution. This keeps each
original intermediate field and algebra action through the calculation.
It avoids simplifying across two dependent presentations of an adjoined
coefficient field. The variable-field and named-proposition boundaries remain.

The complete source
`459822be5cfdfca76a2c1c894b86c5ff414a0badf6127b7f7dea84de71f87545`
passed in 16 seconds in `remote-1f83a39fab694b6ea101ee70592c2726`,
snapshot `5551545e0e3e1913783d811e1aba05fc0dddbe3930dbf83669420577aca2c735`,
after restoring the standard 200000 budget. No override remains in this
module. The larger graph failed other consumers. These existing iterations
support the retained typed transport; they do not isolate a compiler cause
or provide a controlled timing comparison. No extra benchmark was run.

### Type the native homology map before its scalar law

The scalar comparison in
[FiniteSource](../../Aglib/AlgebraicGeometry/Cohomology/ClosedImmersion/RightAdjoint/FiniteSource.lean)
failed repeated apparently identical `map_smul` rewrites. The compiler's
ordinary error context exposed different ring dictionaries: the categorical
quotient-away ring and the separately selected Ore-localization ring. A
later generic square still presented the same homology through an expanded
functor object and a complex-homology alias.

The passing implementation constructs the scalar comparison over variable
`CommRingCat` objects, then supplies the original quotient-localization
square. It also binds the actual native homology arrow as a linear map with
explicit source and target module types. Typed scalar identities and the
native coinduction equation are applied directly to that map. The original
restriction, coefficient action and Ext map remain fixed. Internal aliases
stay private; only the intended interfaces and native instances required in
public statements are exposed.

Source `a0f3417ccdd3fcd592fb8bc07ef7fe25eedecbf13e2da793e1b87bf757ae5ddb`
passed the complete module in 111 seconds in the same `remote-1f83a39f`
graph at standard budgets. The preceding `bdc44de1` source had reached only
a redundant final tactic after the scalar proof closed; earlier `f58b2bf`
and `aca28117` failures retain the actual representation errors. This is
scoped producer evidence; its new stalk consumer failed separately. No
transparency change, profiling, additional diagnostic or budget increase
was used for this repair.

