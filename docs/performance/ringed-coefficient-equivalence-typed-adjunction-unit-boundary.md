> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#ringed-coefficient-equivalence-typed-adjunction-unit-boundary) · [Context](original-context.md) · [Case index](README.md) · [Previous record](normal-constants-typed-kan-extension-comparison.md) · [Next record](hilbert-scheme-naturality-rfl-value-lemmas-and-regular-components.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Ringed coefficient equivalence: typed adjunction unit boundary


On Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, directly constructing the equivalence between the full subcategory of already-abelian-sheaf module presheaves and native ringed module sheaves exhausted the standard 200000 elaborator heartbeats at `whnf`. The failed declaration specialized the final triangle identity directly to `PresheafOfModules.sheafificationAdjunction α`. Its actual premise was a locally bijective map `α : R₀ ⟶ R.obj`, with native abelian sheafification and `WEqualsLocallyBijective`; the source objects had their actual original underlying presheaves already satisfying the sheaf condition.

The retained repair keeps the actual functors and adjunction as typed parameters of `equivalenceOfSheafAdjunction`. A separately typed `adjunctionUnitIso` names both full-subcategory objects before constructing the iso from the original `adj.unit.app`. Its component equation `adjunctionUnitIso_hom_app_hom` retains exactly that original arrow. The generic triangle proof first changes to the original `L.map (adj.unit.app ...)` composite, rewrites the typed component equation, and applies the original `adj.left_triangle_components`. The concrete definition then supplies the native module-sheafification adjunction, its already-proved actual unit-isomorphism supplier, and the native invertible counit. There is no additional public premise at the concrete equivalence or final standard-site endpoint, no alternative unit/counit, and no heartbeat change.

Failed concrete assembly: `remote-8144e600971340389df971c845ce4c50`, source digest `622dac5562656cfe941797358293f71eac1c1a6e3a051fc56d7466a0048f6fa9`; the Equivalence source hash was `4f9230f36a6b6cb011ef526d570f3845c5ac661c0c9e92542100da86a8d8fda6`. That invocation accepted the separate ConstantRing/Presheaf leaves and failed Equivalence after the reported `whnf` exhaustion; its later generated placeholder diagnostics were cascading failures, not authored `sorry` proofs.

Successful complete Equivalence provider: `remote-9454bb315c834f69ac20961def3f4d17`, source digest `0dfacbbd6d04be34c8461a883dd736d68494012ae8eae9d0c9597d321361c055`, owned Equivalence hash `a2ecd5fb8d36688a9907354fd752ed90eee02a2a047c459e6c8c3508b41e50f4`, accepted in 8.7 seconds. This run still failed the final Ringed root solely for missing local installation of the already-proved ring-unit local-bijectivity instances. The provider success is not a claim that the entire invocation or then-current root succeeded.

All original module/sheaf functors, scalar RingEquiv, constant-ring maps and abelian comparisons were retained. Native compiler evidence is preserved under `/Users/kang/Documents/New project/tmp/output/etale-amitsur-20261023/remote-runs/`. These are existing failed/successful proof-iteration observations, not a controlled benchmark or compiler-defect diagnosis; no extra run was launched for this note.

The standard root subsequently exposed a separate inference boundary: installing generic local-instance attributes, and then globally typed standard unit instances, still left the generic module-sheafification equivalence unable to match its inferred ring-unit map. The failed root-only run `remote-11390e5299ef4fa1b232058eb51e3c04`, global source `ab8899fe3d3ffa47b71da232e1b7bed7e4803ded916c1ed0b351f6d62419f91f`, root hash `5a00ea7bae67754f3c0d4df6f34eb51148f88a13c3ba531ceb36dde02672117a`, reported that missing instance and a downstream associator source mismatch. The retained root instead fixes `R₀`, `R`, and `α : R₀ ⟶ R.obj` as typed local constants equal to the original constant presheaf, associated ring sheaf, and original ring unit. It installs the existing proved local-injectivity and local-surjectivity as local constants at exactly that arrow, and calls the generic equivalence and its underlying comparison with named `R₀`, `R`, and `α`, letting their universes be inferred from the actual objects. Public `moduleEquivalenceStandard` and `moduleUnderlyingIsoStandard` record this concrete boundary; the final standard equivalence and original-ab-elian comparison consume them. This does not identify a Lean defect or prove that a particular universe-instantiation mechanism was the cause; it records the narrow successful elaboration boundary.

Successful final root: `remote-20fc45647d51488e8eeb931d17a102e6`, global source `0060ec8b72e3130a7969f4b395425b6f30632c36c19e163b3130e6b06b0476fa`, exact root hash `e807bdbd01c80c1a97bb327b6bae7bcb3d39a9830e9d0ac979a3a5ae4f5fd9c2`, one actual frontend accepted in 17 seconds, exit zero, no diagnostics, process group closed, with the three exact already-compiled lower sources retained. This completed the assigned four-source root closure without any change to its public mathematical conditions or the standard heartbeat budget. No further compiler invocation was made for this note.\n

### Transport additive presheaves before specializing geometric sections

On Lean 4.34.1 with the pinned Mathlib, constructing the actual quasi-coherent
[additive sections](../../Aglib/AlgebraicGeometry/EtaleCohomology/QuasiCoherent/AdditiveSections.lean)
functor laws and forgetful sheaf proof directly across concrete
pullback/global-section carriers exhausted the standard 200000 heartbeats at
`whnf`. The earlier integrated source `22522f79b04a8d403056a0c4ad9b832d263fe985d9de809a6526a9ca1d20c853`
failed at those conversions in `remote-d4fb8ee110b84197a98f09b5b0e91954`;
subsequent unknown identifiers and generated-placeholder errors were cascading
compiler errors.

The retained repair proves additive transport and descent for a typed
presheaf, additive carriers, section equivalences and restriction maps in
[AdditiveTransport](../../Aglib/AlgebraicGeometry/EtaleCohomology/QuasiCoherent/AdditiveTransport.lean).
The geometric specialization supplies the original Hom-to-section comparison
only after the functor laws have been proved. The opaque original restriction
map remains in `sectionsAddHom`, with its transport equation exposed by a
separate typed lemma. The forgetful sheaf criterion also fixes its original
object, morphism and value universes. Section groups, restriction maps and
scalar rings are unchanged.

The repaired producer `f97f0435481a507f36b7950f6b85df5e6bb6f89756580f986572ff55d0a0fce0`
compiled in 41 seconds in `remote-7cd592aabe864e869c3646647ae1e8fb`, source
`2bd9c76b74955775989dd37c8bfaf7ea5caa84227055f906b709e8f76f035190`,
at the unchanged budget. This is a per-module success; the same larger graph
has independent failing leaves. These existing proof-iteration observations
validate the transport boundary, without a timing comparison or an additional
benchmark run.


### Separate original-cohomology transport from concrete module injectives

For genuine `ZMod n` module sheaves,
[Cohomology](../../Aglib/CategoryTheory/Sites/Torsion/ZMod/Cohomology.lean)
transports native ringed-module injective acyclicity to the original underlying
abelian sheaf. Combining the elementary subsingleton transport with concrete
Ringed-equivalence and `Sheaf.functorH.mapIso` objects exhausted 200000
heartbeats at `whnf` in `remote-03a4f5dae65b4c1a9d29d1072d512bc1`.
A broader equivalence/functor boundary still exhausted that limit in
`remote-1c16e566b50845fe8da0277353163f5c`.

The repair separates a pure typed additive-isomorphism transport,
`subsingleton_of_additiveIso`, from the original-H comparison
`cohomology_subsingleton_of_iso`, the native ringed-module acyclicity
application, and the concrete equivalence assembly. The H comparison names
its exact Ext universe and passes the actual source subsingleton witness
explicitly. The pure transport lemma has no over-category finite-products
premise; that premise remains at its genuine native acyclicity consumer.
The original coefficient equivalence, underlying-sheaf isomorphism and
cohomology maps are retained. No assumption of injectivity after forgetting
coefficients or increased search budget is introduced.

The final generic source `8720fa67ec3bfa720cd805487f6cc9a1b30fe50dde09df53e50a983b3ec8e21a`
and scheme adapter `7b77bb6787ba26f0c328df6f96094fb0ca54514e4cc9d2c007c45d903774004e`
both compiled in the isolated run `remote-c99b4ebc8371466a99c972dbb119499e`,
with two successful frontends and no diagnostics. Their native integration
frontends also succeeded in `remote-92d6f1ff4cf44a73affe4bbbccf68fba`
(35 and 14 seconds); that larger graph failed two independent scheme leaves.
These existing proof iterations validate the boundary, not a controlled
speedup or compiler-defect diagnosis. No additional run was made for this note.


### Build root-coordinate isomorphisms at variable sheaves

The concrete component construction in
[EtaleSliceRoots](../../Aglib/AlgebraicGeometry/EtaleCohomology/Kummer/EtaleSliceRoots.lean)
exhausted 200000 heartbeats at `whnf` in
`remote-92d6f1ff4cf44a73affe4bbbccf68fba`, after the explicit projection from
roots of unity to units had repaired the earlier coercion mismatch.

The retained construction first builds a sheaf isomorphism for variable
sheaves, additive coordinate groups and coordinate equivalences. Its
components are exactly `eQ.symm ∘ eP`. The original roots-section naturality
is proved separately on two arbitrary coordinates, then supplied to this
constructor. Concrete inverse-equivalence terms are not expanded inside the
naturality calculation. The roots, unit restrictions, universe ranges and
absence of a modulus restriction are unchanged.

The exposed public isomorphism also needs both its constructor and its
naturality supplier accessible in the public context. The intermediate
private-helper versions reported explicit visibility errors; making those
two helpers public, with documentation, preserved their bodies. The final
source `a33d07879ab13e903334c440e59ef3a5cf7f76a435701367cb495c811273dc76`
compiled in 15 seconds in `remote-35548bdf7c4645d1884dbef6eff0c3f3` at the
standard budget. That run later failed the linter adapter, independently of
this successful source compilation, and passed the pinned production axiom
audit. No additional compiler run was made for this note.

### Stage affine scalar conversion before concrete pullback modules

In [AffineRestriction](../../Aglib/AlgebraicGeometry/EtaleCohomology/QuasiCoherent/AffineRestriction.lean),
the actual `affineΓFunctor` functor carries a scalar action transported through
`isoSpec`; this action is not definitionally the literal top-section action.
The canonical `affineTildeΓRightIso` comparison identifies those actions
and is the identity on underlying sections. Applying this comparison inside
the concrete pullback-module tensor proof still exhausted 200000 heartbeats
at `whnf`, line 108, in `remote-5b024fda1c7a4eac86a929514b871a0e`, source
`302085fc5d909a2e179056ed01d91eac9ec2ab7971594c02cc8d9bc911699a68`.
The following unknown-constant diagnostic was cascading.

The repair moves this linear-comparison composition into
`affine_tmul_of_unit`, parameterized by an arbitrary affine scheme, source
module, target module sheaf, linear map and its unit equation. Scalar
conversion is checked before specializing to the pullback sheaf. The public
theorem then supplies the original `affinePullbackSectionsIso` and its
original `1 tensor m` equation. Separate typed function calculations retain
the original geometric unit composition and final restriction formula.
All three public statements, native scalar action, universes, affine and
quasi-coherence hypotheses remain unchanged.

The repaired source `823cefeda057714bba495b7ac7bd78ba0dc35fffce5b75abf209fdd12e44197a`
compiled in 20 seconds in `remote-b4d289d6f9e64987b48f6017cdc4e1bf`, global
source `fb3042f7b0743e75a8aca09370d3f36d3683123e8d2f0a815ce6c4425569ad51`,
at the unchanged budget. The larger graph failed only the independent roots
helper visibility. These existing iterations validate the staging repair,
without isolating a compiler cause or establishing a timing comparison.

