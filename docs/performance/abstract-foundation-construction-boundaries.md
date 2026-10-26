# Abstract foundation constructions: native parents, universes, counits and triangles

Date: 2026-10-26. This case records the fixed P3a Hom, conditional P3b
chosen-tensor coherence, P3c evaluation/adjunction/stability, P3d native
slice/Hom/binary-tensor pullback, P4 intrinsic additive global-sections and
P5 localization-triangle milestones. Their independent ordinary
mathematical reviews accepted the respective constructions and source
correspondence. The native evidence includes successful production leaves
in mixed builds and a successful final focused P3d invocation, with the
source-identity limits recorded below. Final validation of the integrated
foundation task remains separate at this cutoff.

The later user-directed retirement of an optional all-model transport
route is recorded below with its failed diagnostics, preserved sources
and the restored actual consumer's pass. That route is held research;
the fixed P3/P4/P5 results above do not assert its mathematical closure.

The new experience concerns the actual construction and elaboration
boundaries encountered while moving existing Scheme proofs to generic
owners. No matched before/after benchmark was run for these P3/P4/P5
extractions. The earlier measured three-factor pilot has its own
[complete case](right-derived-three-factor-comparisons.md); its measurements
are not measurements of the constructions below.

## Conditions and preserved constructions

The source basis is Aglib HEAD
`0ba24db0ca05a863d7d5630834316be36f03b7bf` plus coordinated foundation
changes, Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The selected native receipts
retain jobs8/threads4, a 12800 MiB frontend cap and a 110592 MiB aggregate
cap. The repairs retained the existing mathematical hypotheses, native
parents, public maps, model data, pins and package budgets. No suppression
or replay was introduced.

| Construction | Exact range at the recorded milestone |
| --- | --- |
| P3a ring-linear Hom | `C : Type uC`, `[Category.{vC} C]`, topology `J`, `R : Sheaf J CommRingCat.{uR}`, the native `HasSheafCompose` input, and module carriers in `uM`. The source may be a module presheaf; only the target must be a sheaf. The output carrier is `max uC vC uM`, independently of `uR`. This size enlargement is part of the construction. |
| P3b chosen tensor coherence | Site object and Hom universes are independent; the existing tensor sector has module carrier universe `uR`, equal to the ring carrier universe. Native sheaf composition, additive sheafification and `WEqualsLocallyBijective` hypotheses are retained. Associator/coherence/symmetry additionally require `(presheafLocalIso R).IsMonoidal`. The existing Scheme proof originally supplied that stability; P3c supplies it generically in its stated common world. |
| P3c evaluation, right-tensor adjunction and stability | `κ = max uC vC r`, with the input ring sheaf already in `CommRingCat.{κ}` and module/presheaf carriers in `κ`. Pure presheaf constructions require native `HasSheafCompose`; descended constructions also require additive sheafification and `WEqualsLocallyBijective` at `κ`. Actual evaluation has order `Hom(N,P) ⊗ N → P`, and the adjunction is `(- ⊗ N) ⊣ Hom(N,-)`. Tensor stability is proved for the actual localization class, without assuming it. |
| P3d slice and Hom comparison | Independent site object/Hom worlds, RingCat ring world `r` and module world `m`; continuous `F`, binary products in both categories, preservation of those products, relevant slice continuity, and actual global/slice module-pushforward right-adjoint instances. Hom invertibility requires the slice inputs for every `U`. The Hom theorem uses CommRingCat sheaves with their native parents and explicit sheaf-composition inputs, independent ring world `r`, and common module world `μ = max uC vC uD vD m`. No `r ≤ μ` or resize is imposed. |
| P3d binary tensor pullback | Ring sheaves and module carriers are already presented in `ρ = max uC vC uD vD r`, with both sites' native sheafification/locally-bijective inputs and the preceding product, all-slice continuity and native-adjoint conditions. The original canonical binary tensor arrow is proved invertible. This supplies neither a tensor-unit comparison nor full monoidal coherence. Native Scheme opens supply the conditions for arbitrary scheme morphisms, without a flatness or Noetherian hypothesis. |
| P4 intrinsic additive Γ and native Ext | `additiveGamma P` is actual additive Hom, in the category's Hom universe. Its native right-derived/Ext comparison requires `Abelian`, `EnoughInjectives` and independently supplied `HasExt.{e}`. Intrinsic sheaf Γ requires sheafification and uses the native constant integer sheaf; represented module Γ uses the original `liftedUnit`. A terminal evaluation view additionally takes explicit `hT : IsTerminal T`, retaining the necessary `ULift` and scalar-forgetting functors. |
| P5 localization triangles | Independent category/Hom universes, a shifted target, a genuine localization `Q`, an actual triangle-valued functor `T`, and its three vertex comparisons. Distinguishedness uses the existing distinguished source triangles. Normalization takes the specified first and second arrows and their proved whole comparison equations. Both actual étale clients retain arbitrary `Ring Λ`, their three independent derived models, and their original open/closed/complement hypotheses. |

These are constructions from the stated suppliers. In particular, P5's
geometric input is the existing complex triangle built from the genuine
localization short exact sequence; the desired finished derived triangle
is not an input field.

## Keep the native parent and actual universe at specialization

The generic Hom construction uses the exact forgotten ring sheaf

```text
S = (sheafCompose J (forget₂ CommRingCat RingCat)).obj R.
```

Its scalar action restricts a section of `R` along the slice arrow and
acts in the original target module. Scheme aliases specialize this same
constructor at `X.sheaf`; their module parent remains exactly
`X.ringCatSheaf`. Rebuilding an equivalent ring or installing a replacement
scalar action would change this boundary.

The first Scheme aliases had ordinary application/universe mismatches.
Later actual consumers exposed more local heads: the unit-source proof
needed its scalar explicitly typed as `Γ(X, V.unop.left)`, and the existing
presheaf tensor-currying proof needed
`TensorProduct.smul_tmul'` at the literal ring
`X.sheaf.obj.obj (op V.unop.left)`. These annotations retain the original
scalar and tensor; they do not add a commutation premise or a second ring
structure. The
[P3a result](../../../foundation-p3/internal-hom-result.md) and
[fixed review](../../../foundation-p3/internal-hom-independent-review.md)
record the exact original-value and coefficient-map comparisons.

The native Scheme opens category has object and Hom universes both `u`:
`Preorder.smallCategory` uses `ULift (PLift (U ≤ V))`. Consequently the
actual P3a specialization is `(uC, vC, uM) = (u, u, u)`, and its output
maximum is still `u`. An earlier report example `(u, 0, u)` was corrected;
the seven reviewed source hashes did not change. Thinness does not justify
substituting an unlifted category with a different Hom universe.

Moving the Hom construction beyond a preorder also exposed a proof
presentation that had relied on definitional equality of identity-slice
objects. The generic locality proof instead uses
`presheafHom_map_app_op_mk_id`; local coefficient-map naturality uses
associativity and `Over.w`. This retains the original restrictions on an
arbitrary category rather than adding a preorder hypothesis.

## Pin residual universes through noninjective maxima

In P3c the common carrier is `κ = max uC vC r`. Knowing that carrier does
not uniquely determine the residual universe `r`. The successful
constructors, helpers and their corollaries therefore supply
`.{uC, vC, r}` explicitly. P3d's Hom calls similarly specify their own
`.{uC, vC, uD, vD, r, m}` arguments rather than asking inference to recover
`m` through `μ`. Result-endpoint annotations alone did not resolve every
call in these families.

The annotations also retain the actual data heads. The generic presheaf
currying proof fixes the entire `RawHom R P N U.unop` equality before
extensionality and uses the original local ring in tensor lemmas. The
[sheaf tensor–Hom equivalence](../../Aglib/Algebra/Category/ModuleCat/Sheaf/InternalHom/TensorAdjunction.lean)
supplies the actual presheaf tensor and target to
`sheafificationHomEquiv`, then the native fully faithful forgetful Hom
equivalence with `X := M` and `Y := sheaf R N P`. Its type is fixed as the
complete equivalence between these original Hom sets. These are coupled
universe, carrier and parent annotations; they do not identify independent
worlds or substitute an equivalent coefficient object.

P3c constructs the genuine right-tensor adjunction and proves stability
by conjugating the native sheaf-target bijection test through the actual
currying equivalences. The test target `Hom(B,N)` lies in `κ`; the proof
imports none of the conditional descended associator/coherence files.
Thus it supplies P3b's actual stability premise in this sector without
circularity. Plain P3a Hom keeps its independent ring/module worlds, and
P3c does not silently lift a smaller ring into `κ`. The
[P3c result](../../../foundation-p3/evaluation-result.md) and
[ordinary review](../../../foundation-p3/evaluation-independent-review.md)
give the exact orientation, values and fixed eight-source scope.

## Take the whole counit isomorphism, then supply its literal dictionary

The chosen tensor remains pointwise presheaf tensor followed by the native
module sheafification `L`; write `G` for its forgetful right adjoint. The
original counit isomorphism in
[Monoidal/Objects](../../Aglib/Algebra/Category/ModuleCat/Sheaf/Tensor/Monoidal/Objects.lean)
is obtained as a component of the whole counit NatIso:

```text
(asIso (PresheafOfModules.sheafificationAdjunction
  (R := S) (𝟙 _)).counit).app M.
```

Its forward arrow is still the original counit component, with the named
`sheafifyForgetIso_hom` value law. The first attempt to synthesize
`IsIso` directly at that component failed. Taking the component of the
whole NatIso supplied the original isomorphism without replacing the map.

One further consumer still failed: `isIso_of_comp_hom_eq_id` did not find
the component dictionary through the displayed native expression. In
[Monoidal/LocalIso](../../Aglib/Algebra/Category/ModuleCat/Sheaf/Tensor/Monoidal/LocalIso.lean),
the proof binds `hε` at the literal counit component using
`inferInstanceAs (IsIso (sheafifyForgetIso R _).hom)` and passes that
already proved dictionary explicitly to `@isIso_of_comp_hom_eq_id`. The
other input is the original adjunction triangle identity. This resolves
the synthesis boundary without a new invertibility assumption, global
instance-priority change or alternative counit.

## Prove the chosen associator's typed square before tensor specialization

The generic associator keeps the original three factors: inverse image
under `L` of the right-whiskered sheafification unit, the image of the
presheaf associator, and image of the left-whiskered unit. Their
invertibility is proved from the stated `W.IsMonoidal` input and native
sheafification detection.

The failed proof tried to simplify the three-isomorphism conjugation
directly, then rewrite `map_comp` across the concrete `tensorProduct` and
`L.obj` endpoint presentations. The native diagnostic reported an
unsolved cancellation goal followed by a rewrite/type mismatch. The
successful
[Associator](../../Aglib/Algebra/Category/ModuleCat/Sheaf/Tensor/Monoidal/Associator.lean)
first proves two finite categorical equations over variables:

- `a.hom ≫ (a.symm ≪≫ b ≪≫ c).hom = b.hom ≫ c.hom` for the three typed
  isomorphisms;
- for variable functors `L`, `G` and unit-shaped transformation `η`, the
  map-square equation `L.map u ≫ m = L.map a ≫ L.map v` implies
  `u ≫ η.app Q ≫ G.map m = a ≫ v ≫ η.app S` by naturality and functoriality.

The actual tensor factors are supplied to those completed equations.
Only then are the whole unit-value law and nested pure-tensor component
formulas obtained. Coherence is proved for this same chosen tensor,
structure-module unit, associator, original unitors and sheafified
braiding through the faithful identity into native `LocalizedMonoidal`.
The actual unchanged Scheme `Monoidal/Sections` consumer also compiled.
The
[P3b review](../../../foundation-p3/tensor-coherence-independent-review.md)
checks both the conditional generic construction and the unconditional
Scheme realization, including its existing stability supplier.

## Retain general slice naturality and the canonical binary tensor arrow

P3d's
[Hom comparison](../../Aglib/Algebra/Category/ModuleCat/Sheaf/Pullback/Hom.lean)
first constructs the map induced by the original global adjunction unit.
Over a general category, `F(W.hom ≫ i)` and
`F(W.hom) ≫ F(i)` need their actual `F.map_comp` equation. An over-morphism
with identity underlying arrow compares those slice objects; naturality
of the supplied Hom section along that morphism gives the needed value
equality. The analogous product-square proof uses `F.map_id` and native
product-comparison naturality. Preorder reflexivity is not a general
replacement for those equations.

The slice construction uses the actual RingCat structural map, native
chosen global/slice adjunctions and product-preservation square. Its
partial mate is computed and identified with the direct-image
restriction map, whose section values are identities. The Hom map is
identified with the actual slice Hom equivalence as a whole, before
invertibility is deduced. Slice continuity remains an explicit input;
its separate supplier requires source pullbacks, their preservation and
base continuity.

The
[binary tensor comparison](../../Aglib/Algebra/Category/ModuleCat/Sheaf/Pullback/Tensor.lean)
then keeps the original arrow built from tensor-of-units and the native
lax tensor pushforward. At world `ρ`, its source P3c call uses residual
universe `max uD vD r`, and its target call uses `max uC vC r`, so both
actual carriers are `ρ`. The proved whole Hom-equivalence formula is
precomposition with that canonical arrow; applying its inverse to the
identity supplies the inverse of the same arrow. This is a map-value
comparison, not just an isomorphism between its endpoints.

The original Scheme `OpenRestriction` constructor and canonical
`pullbackTensorMap` remain literal. A whole section-equivalence law
compares the old geometric calculation with the generic one; no equality
of separately chosen slice isomorphisms after `overEquiv` transport is
assumed. The
[P3d result](../../../foundation-p3/slice-result.md),
[evidence](../../../foundation-p3/slice-evidence.json) and
[ordinary review](../../../foundation-p3/pullback-independent-review.md)
record the six-source boundary. Continuity or module-valued exactness
alone supplies none of the omitted product/adjoint hypotheses. This
milestone proves the binary comparison under its actual conditions and
does not assert strong monoidal unit/coherence or derived pullback laws.

## Keep intrinsic comparisons whole and retain original-value views

The P4 lower
[represented constructor](../../Aglib/Algebra/Homology/RightDerived/Represented.lean)
is actual `preadditiveCoyoneda.obj (op P)` and the native chosen-resolution
Ext comparison. The intrinsic
[Global/Comparison](../../Aglib/CategoryTheory/Sites/SheafCohomology/Global/Comparison.lean)
does not introduce a terminal object. The optional
[Terminal/Comparison](../../Aglib/CategoryTheory/Sites/SheafCohomology/Terminal/Comparison.lean)
supplies the actual evaluation comparison when `IsTerminal T` is given.
The intrinsic sheaf target is `AddCommGrpCat.{max u a}`; represented
module Γ has additive target `max u r w` for module values in `max r w`.
The site Hom universe and native Ext universe remain independent.
The categorical terminal view retains the actual universe lift; the ringed view
retains the original ring, lifted unit and exact scalar forgetting.
Scalar forgetting uses its native homology-preservation input, rather
than an assertion that it preserves injectives or is strong monoidal.

The old public Ext comparison now delegates to the lower constructor.
Its known cocycle consumer had unfolded the previous full composite.
Unfolding only the new alias left that calculation at the wrong head.
The proved whole
`extRightDerivedRepresentedAddEquiv_eq_original` equality restores the
original Hom-complex/extension-by-zero composite before the old cocycle
calculation. Native coefficient naturality, augmentation and the
degree-zero unit therefore remain equations for the original maps.
The first terminal consumer also required the actual evaluation
functor's additive instance; its successful repair supplies that
structure at the native expression. Full conditions, source values and
consumer coverage are in the
[P4 state](../../../foundation-p4/global-state.md),
[evidence](../../../foundation-p4/global-evidence.json) and
[ordinary review](../../../foundation-p4/global-independent-review.md).

The P5
[triangle factory](../../Aglib/CategoryTheory/Triangulated/LocalizationTriangle.lean)
similarly shares the actual native localization lift and factorization.
It descends each original vertex isomorphism using `liftNatIso`, proves
the whole factorization equation, then takes its component. The shared
normalizer uses the specified literal first arrow `a` and second arrow
`b`; its third arrow is the original connecting arrow transported by the
third and shifted first vertex isomorphisms. The same whole triangle
isomorphism transports distinguishedness.

Both
[D+](../../Aglib/AlgebraicGeometry/EtaleCohomology/Localization/Derived.lean)
and
[unbounded](../../Aglib/AlgebraicGeometry/EtaleCohomology/Localization/Unbounded.lean)
clients supply their existing complex vertex comparisons and whole
counit/unit equations. Named native-lift `_eq_original` and conjugated-map
views retain the previous reduction interface. A remaining middle-vertex
component proof was normalized at the literal native factorization
`fac.hom₂ ≫ (𝟙 _ ≫ 𝟙 _)` before simplifying identities. No triangle arrow,
derived model or geometric short-exactness premise changed. The
[P5 review](../../../foundations/localization-independent-review.md)
records the construction, declaration repair and final component-proof
continuation at their distinct source hashes.

## Failed revisions retained with their actual outcomes

Run identifiers below name directories under the sibling research
dossier's `foundations/remote-runs/`. Each contains `build.log`,
`receipt.json` and `compiler-events.jsonl`.

| Run / recorded failure | Repair whose later coverage is retained |
| --- | --- |
| `remote-051d6e1225aa4e2e8130228ab49c01c6`: Scheme Hom aliases had application/universe mismatches; tensor Objects could not synthesize the counit-component `IsIso`, with later value errors. | Specialize at the native site/category/parents; construct the component from the whole counit NatIso. |
| `remote-98ceb92c03264361a665e316af10b988`: local tensor-scalar synthesis and LocalIso counit/localization synthesis failed. `remote-b83e72eba8d64cb4acb6d99abdb2957b` still failed at the LocalIso dictionary and the original Hom unit-source scalar head. | Keep literal scalar/tensor heads; use the original native localization theorem and explicitly pass the proved component dictionary. The failed revisions are not the later passing hashes. |
| `remote-b48870dfdd254c1490877fbc23589b26`: associator cancellation and `map_comp` rewriting across tensor endpoints failed. | Typed three-iso cancellation and the variable-functor map-square law, followed by actual specialization. |
| `remote-a9707cdb31f24eae87e05a252df0dc14`: the revised associator failed solely on its enabled unused-`Category.assoc` simp-argument diagnostic. | Remove that unused argument; the actual constructor, proof route, options and premises remain unchanged. The corrected hash passed in 5dd. |
| `remote-75733990d6694ca59c332731ece4752e`: the first P4 lower represented comparison failed in its resolution-lift zero equation. In b488, Terminal lacked the actual additive evaluation instance and the normalization consumer still unfolded only the new alias. | Use the native resolution-lift equation, supply actual evaluation additivity and rewrite by the proved full original-value equality. Producer passes are from b488; repaired consumer passes are from a970. |
| P5's initial callers retained `where obj :=` before an entire functor value; later b83 caller proofs failed at the middle component. | Define the actual functor value and normalize the literal native middle-vertex factorization. The final caller hashes are those in the P5 review and 757 receipt. |
| 5dd's initial P3c presheaf-currying source had stuck universe constraints; `remote-84b3f83d14004b1d8af026690b2b475b` passed its replacement but failed Evaluation on native tensor-structure synthesis and unresolved sheafification inputs. | Explicit residual universe calls, the original tensor/scalar parent, whole `RawHom` carriers and actual sheafification `P`/`F` arguments. The later Evaluation pass is d499. |
| `remote-d49983faaff84542821ba21b9e2ba2e0`: TensorAdjunction's fully faithful Hom equivalence retained unresolved object arguments, followed by failed value/inverse proofs. | Specify its actual `X`/`Y` and complete Hom-equivalence type, with the explicit residual universes. The accepted TensorAdjunction/Stability and original Dual/prefix passes are from 233fb. |
| `remote-f14f084e2e05458fa14eb3fab5ee53fb`: the first P3d Hom candidate had stuck residual-`max` universe constraints and unresolved later declarations. | Specify the helper/constructor universe arguments throughout; retain actual general over-category naturality. Hom `2057435f…` passed in 2542. |
| `remote-2542f9329b3248179599d2de4ddc73d0`: Tensor attempted to use an equivalence as a simp proposition. | Use the proved whole application/precomposition equation for the actual canonical arrow. Final Tensor `de962dc1…` and Scheme Isomorphism `ad820122…` passed in b6b4. |

The
[tensor progress record](../../../foundation-p3/tensor-progress.json)
retains each failed revision's source hashes. The P4 evidence and P5
review retain their initial, repaired and final identities. These are
ordinary elaboration, synthesis, tactic or enabled-diagnostic failures.
They provide no profiler-based compiler attribution or OOM diagnosis.

## Native leaf coverage and evidence identity

The following table records individual successful production frontends.
Every initial invocation in this table returned exit 1 because another
target failed; successful leaves are retained only at their actual input
basis. Reported seconds are rounded native module-build observations,
which can overlap in a parallel graph. They are neither paired timing
comparisons nor summable whole-graph durations.

| Run and log | Successful scope used by this case |
| --- | --- |
| [b241](../../../foundations/remote-runs/remote-b24112c8e9da45debbec62bc722da6ea/build.log) | Generic P3a `InternalHom.PresheafSource` and `InternalHom.Basic`. |
| [98](../../../foundations/remote-runs/remote-98ceb92c03264361a665e316af10b988/build.log) | Scheme `InternalHom.PresheafSource`; tensor `Monoidal.Objects` and original Scheme `Tensor.Basic`. |
| [b83](../../../foundations/remote-runs/remote-b83e72eba8d64cb4acb6d99abdb2957b/build.log) | Generic P3a `InternalHom.Functor` and original Scheme `InternalHom.PresheafTensor`. |
| [757](../../../foundations/remote-runs/remote-75733990d6694ca59c332731ece4752e/build.log) | Original Scheme `InternalHom`, `HomSection`, `HomFunctor`; final P5 `Localization.Derived` (62 s) and `Localization.Unbounded` (45 s). |
| [b488](../../../foundations/remote-runs/remote-b48870dfdd254c1490877fbc23589b26/build.log) | Generic and Scheme tensor `Monoidal.LocalIso`; P4 lower `RightDerived.Represented`, `DerivedExt`, `DerivedComparisonFactory` and `Global.Comparison`. |
| [a970](../../../foundations/remote-runs/remote-a9707cdb31f24eae87e05a252df0dc14/build.log) | P4 Terminal, RepresentedSections, Ext normalization/naturality/zero, Γ and scalar/zero/postcomposition consumers, including actual `DerivedTerminalZero`. |
| [5dd](../../../foundations/remote-runs/remote-5ddbe76ea5e04715890c51315946d795/build.log) | Final generic Associator (7.5 s), Basic, Symmetric; Scheme Associator, Basic, Symmetric; unchanged actual `Monoidal.Sections`. |
| [5f2](../../../foundations/remote-runs/remote-5f2e1521cc554f2994f258e63b80cc15/build.log) | Generic `Triangulated.LocalizationTriangle` (2.9 s). No P5 caller success is inferred from this run. |

The receipts retain the exact native build commands and runtime profile;
compiler start/finish events identify the individual frontends. The
following full manifests are available, with no input drift reported in
their matching receipts:

| Manifest | Source-content SHA-256 | Manifest-file SHA-256 |
| --- | --- | --- |
| [b488 source.json](../../../foundations/remote-runs/remote-b48870dfdd254c1490877fbc23589b26/source.json) | `3a0b787c8bb71cf9ff6923e28a3e6b8273ad2b8724d5aa8cfcf0f448815b9e50` | `c353d99b8ad0ddae0d63a396cbac74571ecde4abf33a917ca2efe351099d4e93` |
| [a970 source.json](../../../foundations/remote-runs/remote-a9707cdb31f24eae87e05a252df0dc14/source.json) | `3377655a1811429cafc559833a3717208d0ef6502a2af95dfc8597b72eb7fc63` | `1b6f728d9aa67df64883c94e6e4c6250fb83803584b532999008b78abdd4b8b4` |
| [5dd retained source manifest](../../../foundations/source-manifests/remote-5ddbe76ea5e04715890c51315946d795.json) | `856266a2f1ac52c9057c6e8e734447f08508e5d6541a613ee8c68c1769f37251` | `a897a5d6fd700d2ebaad0fb4af0c49d780f9ef388d84a58a04a7fbdcc62fd304` |

The P4 review matches the current reviewed 26-file Aglib closure to a970.
Relative to b488, only the later repaired Terminal and Ext-normalization
files differ, and neither is a dependency of its retained producer
passes. The P3b review matches all ten scoped files and inspected
immediate dependencies to the retained 5dd manifest.

The older P3a four-run record did not retain each historical full
`SOURCE.json`. Its receipts and events establish the reported historical
leaf outcomes, and requested-root hashes bind some consumers, but an
aggregate source hash does not reconstruct every dependency's old bytes.
The P3a review is on its fixed seven source hashes; it does not claim a
new complete seven-file hash-to-old-run certificate. Likewise, 5f2's
receipt does not separately hash the generic triangle dependency: its
frozen hash is identified by the principal and accepted P5 review.
The 757 receipt directly records both final P5 caller hashes. No missing
manifest was reconstructed and no additional certification chain was run.

### P3c/P3d extension on its own captured sources

The later P3c/P3d runs retain full per-file source inventories. Their
manifest hashes agree with the matching receipts, and the recorded input
drift lists are empty. The P3c review's queued-execution paragraphs predate
the later f14f084 coverage: its mathematical acceptance at `8759fe57…`
is combined here with that source's actual later frontend and Sections
passes. Its `72b1a6ee…` predecessor failed in e8cf95 on three invalid
qualified topology names; the corrected native namespace changes no
mathematical premise. The P3d result/evidence packet's pending-review
wording is superseded by the later accepted ordinary P3d review.

| Run, log and captured input | Successful P3c/P3d scope |
| --- | --- |
| [84b3](../../../foundations/remote-runs/remote-84b3f83d14004b1d8af026690b2b475b/build.log), [manifest](../../../foundations/source-manifests/remote-84b3f83d14004b1d8af026690b2b475b.json) | Generic PresheafTensor `85ca90d4…`; failed mixed invocation. |
| [d499](../../../foundations/remote-runs/remote-d49983faaff84542821ba21b9e2ba2e0/build.log), [manifest](../../../foundations/remote-runs/remote-d49983faaff84542821ba21b9e2ba2e0/source.json) | Generic Evaluation `28f8f0bd…`; failed mixed invocation. |
| [233fb](../../../foundations/remote-runs/remote-233fb99648944d2d98d75a2d914dda47/build.log), [manifest](../../../foundations/remote-runs/remote-233fb99648944d2d98d75a2d914dda47/source.json) | Generic TensorAdjunction `ed81104b…`, Stability `10e59eae…`, original Dual `4a262718…`, full original Isomorphism snapshot `51dfaa58…` and Scheme OpenRestriction `7a516489…`; failed mixed invocation. |
| [e8cf](../../../foundations/remote-runs/remote-e8cf95da31ab4ee39d1f2d2075a04bcd/build.log), [manifest](../../../foundations/remote-runs/remote-e8cf95da31ab4ee39d1f2d2075a04bcd/source.json) | Original PresheafTensor `afe79f36…` and generic Restriction `0a72ed83…`; failed mixed invocation, including the old LocalIso name errors. |
| [f14f](../../../foundations/remote-runs/remote-f14f084e2e05458fa14eb3fab5ee53fb/build.log), [manifest](../../../foundations/remote-runs/remote-f14f084e2e05458fa14eb3fab5ee53fb/source.json) | Repaired Scheme LocalIso `8759fe57…`, original Monoidal.Sections and actual dependent Scheme Associator/Basic/Symmetric; failed mixed invocation on the separate Hom candidate. |
| [e143](../../../foundations/remote-runs/remote-e143ff85da89480aa9cd1b4e74fc9fc1/build.log), [manifest](../../../foundations/remote-runs/remote-e143ff85da89480aa9cd1b4e74fc9fc1/source.json) | Generic AdjunctionSquare `352f8947…`; failed mixed invocation. |
| [2542](../../../foundations/remote-runs/remote-2542f9329b3248179599d2de4ddc73d0/build.log), [manifest](../../../foundations/remote-runs/remote-2542f9329b3248179599d2de4ddc73d0/source.json) | Generic Hom `2057435f…`; invocation failed at the next Tensor leaf. |
| [b6b4](../../../foundations/remote-runs/remote-b6b4c859461443f1a9ed0c74d3c88e16/build.log), [manifest](../../../foundations/remote-runs/remote-b6b4c859461443f1a9ed0c74d3c88e16/source.json), [receipt](../../../foundations/remote-runs/remote-b6b4c859461443f1a9ed0c74d3c88e16/receipt.json) | Final generic Tensor `de962dc1…` and actual Scheme Isomorphism `ad820122…`; successful focused invocation, exit 0, process group closed. The other four P3d sources retain compatible earlier coverage. |

The final b6b4 manifest has file SHA-256
`e073078641eacaf7e41c5d5a54ba0139d055060a5b872a57220b091b838fa476`
and source-content identity
`9ba06aa6a787ba87e146e20b5d403ec807c3e3a95f36c1e8c3a490e1f3e88437`.
Its actual recorded command is:

```text
lake --rehash build Aglib.Algebra.Category.ModuleCat.Sheaf.Pullback.Tensor Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Isomorphism
```

That successful invocation compiled two fresh leaves, not six. The P3c
review/result and P3d evidence ledger give the other per-run full hashes,
exact commands and leaf identities. Each run directory retains its native
compiler events and receipt. No paired timing experiment was conducted
for P3c/P3d; elapsed module observations establish execution scope only.

## Fixed reviewed source locators

The linked reviews contain the complete per-file source sets. The
following hashes fix the constructors and changed value-law consumers
discussed above; links open the source owner, while hashes identify the
accepted milestone even if later work changes that path.
The first table retains the initial P3a/P3b and P4/P5 identities. P3c's
changed Scheme PresheafTensor and stability supplier are recorded in the
later table; their older passes remain historical observations.

| Source, relative to `Aglib/` | SHA-256 |
| --- | --- |
| `Algebra/Category/ModuleCat/Sheaf/InternalHom/PresheafSource.lean` | `1a333567d5fb5122976550bfbedecffd87a747b1f28cd3f1f6de8a2f1cc85e9d` |
| `Algebra/Category/ModuleCat/Sheaf/InternalHom/Basic.lean` | `d27846320e5aa8804eaafcf2c1893baf737f29b2f3cb936d05ebb13e00cba50a` |
| `Algebra/Category/ModuleCat/Sheaf/InternalHom/Functor.lean` | `d72a2be34485602ab8a3b26e0eb02b4970ed418a398d9b45cd3f92ac5c7fed91` |
| `AlgebraicGeometry/Modules/InternalHom.lean` | `dec38d3d40b4dc5c42810b1e93e54ac4cd9cfded824e2f99f234b8963d19b3a6` |
| `AlgebraicGeometry/Modules/InternalHom/PresheafTensor.lean` | `624e9d4bb1d8e10516257c82bec3480b85bab5196b3514eb2617fa8c42a1d001` |
| `Algebra/Category/ModuleCat/Sheaf/Tensor/Monoidal/Objects.lean` | `6beae278f59a350a51d7cf9416ff38de0ab5d67c8ac541b4106cbc9dec582471` |
| `Algebra/Category/ModuleCat/Sheaf/Tensor/Monoidal/LocalIso.lean` | `f27fdea49a5b75c2778243d9aaf19f7086ae1ecc95592b8ecce5004f696d3e45` |
| `Algebra/Category/ModuleCat/Sheaf/Tensor/Monoidal/Associator.lean` | `d35b430348724a875db9c2aab99bbb72bd7876bb1d8981980debee8e04368529` |
| `Algebra/Category/ModuleCat/Sheaf/Tensor/Monoidal/Basic.lean` | `d3b8ac24c5263e7774e2c780f7d79a86c163e98bd48e4164c7142c8798be2754` |
| `Algebra/Category/ModuleCat/Sheaf/Tensor/Monoidal/Symmetric.lean` | `bbd94ae3550f7d4f4312164f39c48c75630b0c197637aa57982cd013f44f9bc1` |
| `Algebra/Homology/RightDerived/Represented.lean` | `e52b483e53b78682493ba107180300d511558c713726a8e7274aa0946f0eb920` |
| `CategoryTheory/Sites/SheafCohomology/Global/Comparison.lean` | `f95f84e999fbcafd949dfa230fba5c7c7991ad7a1ed3b7cc2bfb0f99c92e2e09` |
| `CategoryTheory/Sites/SheafCohomology/Terminal/Comparison.lean` | `5355c5b4c0e2dbb586520872f7c322397f42f42ff39a52794debfac9257d41ea` |
| `CategoryTheory/Sites/SheafCohomology/ModuleCoefficients/DerivedExtNormalization.lean` | `6b6b5b07179b02899af16bb763e0d030931b199cbad85593dce10977086ad369` |
| `CategoryTheory/Triangulated/LocalizationTriangle.lean` | `adfb82698c382b17ac4a2153d7e4b8fa7ac2f3fd728fdf323dd7813fc7dc510a` |
| `AlgebraicGeometry/EtaleCohomology/Localization/Derived.lean` | `2e9e733053e476e16c5372f7d06d7240b36ffd5b66773759a12dfb614ca2707b` |
| `AlgebraicGeometry/EtaleCohomology/Localization/Unbounded.lean` | `ad595174480ffca5a732aad194800fe100eb2929e5246c7f649336644a9d7b85` |

### P3c fixed eight-source milestone

Paths are relative to `Aglib/`, except for the linked preserved snapshot.
P3c mathematical coverage of that snapshot is its eight curry/uncurry/
equivalence declarations and their comparisons before
`preimageOverFunctor`. The later P3d geometric tail has its own source and
execution identity.

| Source | SHA-256 |
| --- | --- |
| `Algebra/Category/ModuleCat/Sheaf/InternalHom/PresheafTensor.lean` | `85ca90d43873d8c829c5ee23aab83734efca06a45850431f2a15a565b0aa69f3` |
| `Algebra/Category/ModuleCat/Sheaf/InternalHom/Evaluation.lean` | `28f8f0bdecd48de7ee6f241a4e43e94dbb2cfcbf1d45cbda04357d8451252e78` |
| `Algebra/Category/ModuleCat/Sheaf/InternalHom/TensorAdjunction.lean` | `ed81104ba2e6849b9a7c474d9260778f9123f5203ce16c7e8319af27f29016ba` |
| `Algebra/Category/ModuleCat/Sheaf/Tensor/Monoidal/Stability.lean` | `10e59eae125d32d6c11ae4a99b3f639f01aad19866a58a15bd59bb2434893733` |
| `AlgebraicGeometry/Modules/Invertible/Dual.lean` | `4a2627184aad76df79fff373e84bf9eaac8c1fd8068dd1cee0f6bb091c0616a3` |
| `AlgebraicGeometry/Modules/InternalHom/PresheafTensor.lean` | `afe79f369a693fe0ca55c29138c5bf8fbf4054e22e72b66db68828fc06f5e615` |
| [Preserved Isomorphism snapshot](../../../foundation-p3/evaluation-p3c-isomorphism.lean) | `51dfaa58a24c74c8c10f3dbb00db49cc0046ff6f94e191b01d843f5d8f542411` |
| `AlgebraicGeometry/Modules/Tensor/Monoidal/LocalIso.lean` | `8759fe5797a3a0b32096cc890c3269acfecf51bddfbaa0048789b4420a21632d` |

### P3d fixed six-source milestone

Paths are relative to `Aglib/`. The accepted P3c prefix remains unchanged
in the final Scheme Isomorphism after removing its authorized new generic
Tensor import. Its later full-file pass is the b6b4 observation above.

| Source | SHA-256 |
| --- | --- |
| `Algebra/Category/ModuleCat/Sheaf/Pullback/AdjunctionSquare.lean` | `352f89476fa7ee5cd3cb3f68df4c7cf9d0455e48986514fe937fb1c9815dd759` |
| `Algebra/Category/ModuleCat/Sheaf/Pullback/Restriction.lean` | `0a72ed835bf949dcad6fd2484a7a9c81ff1884e43ed971e768a8debd4a3c4b4c` |
| `Algebra/Category/ModuleCat/Sheaf/Pullback/Hom.lean` | `2057435ff452740c16d06911d4bebdab43a7c4bc54435ccd2e1b7d67169a9d26` |
| `Algebra/Category/ModuleCat/Sheaf/Pullback/Tensor.lean` | `de962dc1f001eb3f7d7471531ffb02cf125131ec8c0ccccc4fa73ffb024e6862` |
| `AlgebraicGeometry/Modules/Pullback/OpenRestriction.lean` | `7a51648912f255b742e9f0cb955a3a72229c96c8c401308cc338804ef7147f61` |
| `AlgebraicGeometry/Modules/Pullback/Tensor/Isomorphism.lean` | `ad82012276725987a6c84046ca189ba5f6419da0b2f06bb67ccb902f561c50f1` |

## Retire optional implementation transport at the actual consumer

The user required every proof to use as few models and implementation
choices as its mathematical content needs. The native
[interface rule](../INTERFACES.md#minimal-implementation-choices) and shared
[formalization rule](../../../../../../infra/contracts/FORMALIZATION.md#models-and-implementation-choices)
select one realization per mathematical object/category, prefer intrinsic
Ext and natural-degree right-derived interfaces when sufficient, and
place genuinely needed comparison or independence proofs at their actual
consumer boundary. This is a design rule, not a theorem about optimal
model counts or the cost of every multi-model comparison.

The actual consumer is
[Proper/Universal/ModelTransport](../../Aglib/AlgebraicGeometry/EtaleCohomology/Proper/Universal/ModelTransport.lean).
Its public theorem retains the four independently supplied abelian-sheaf
output models and universes for a commuting square. Its conclusion remains
the original higher exchange on every coefficient killed by `n`:

```lean
(hf : boundedExchange n f f' g g' h)
(F : AbelianSheaf.{u, u + 1} X)
(hF : n • 𝟙 F = 0) (q : ℕ) :
  IsIso ((higherBaseChangeMap f f' g g' h q).app F)
```

The restored proof uses the ordinary degree-zero exchange comparison.
For positive degrees, the existing vanishing result on underlying genuine
`ZMod`-module injectives makes the source zero; standard-model exchange
then gives target zero in the actual sheaf category. These invariant tests
feed the existing genuine injective reduction for killed coefficients.
Standard-model test extraction is isolated from the arbitrary-output
section. The auxiliary canonical model used for the `ZModSheaf X n`
category belongs to a different coefficient category. This consumer needs
no simultaneous cube of four output and four reference models, and it
does not assume that scalar forgetting preserves injectives.

### Failed transport route and diagnostic boundaries

Before the route was retired, the optional generic comparison leaves had
individual compiler passes, but the actual consumer did not close through
that route. The following versions remain distinct:

| Consumer version and evidence | Actual outcome |
| --- | --- |
| Original prototype `43c2bf6df570b3fa0e5838fb3208d4b4ac73ac5276c48fcd489627b6f3da18d2`, preserved as [original43c](../../../foundations/model-profile-original43c.lean); [ordinary d1f67 log](../../../foundations/remote-runs/remote-d1f67e324f494b0c835f63dd6dffe77a/build.log) | Public `higherBaseChangeMap_isIso_of_boundedExchange` failed its kernel check. The exact same source was used by the corrected diagnostic below. |
| Native-map normalization version `7cf5576d0ea49db7e1591ee77b5f64eb9261e2e4e4583c2fdc7e52b84672b4be`; [9c913 log](../../../foundations/remote-runs/remote-9c91302acbf24d87a59609a51dbc7610/build.log) | Generic `NativeMap` at `5dd3c65e…` passed. Replacing unfolding boundaries by proved whole native-map equations still left the actual consumer at a kernel timeout, reported as 99 s. This was insufficient consumer repair. |
| Split-helper version `af33306d7c81a2d58ee8583faeebdecda6850296bd02afc8d69fd70cfbda77bc`; [execution record](../../../foundations/validation-execution-model-af333.json) | A helper conclusion selected reference-model records while its proof returned output-model exchange. Type mismatches accompanied the public kernel timeout; that timeout does not isolate the cost of a correctly typed assembly. |
| Corrected helper version `ff9b736f7bc999d57af912956ea03bed00de0dca5e0f022076841c84338f1b85`, preserved as [exact ff9b](../../../held-model-comparison/versions/ModelTransport-ff9b736f.lean); [execution record](../../../foundations/validation-execution-model-ff9b.json) | Explicit output-model records removed those type errors. The only reported diagnostic remained the public theorem's kernel timeout. No independently compiled helper artifacts or optional all-model mathematical closure are inferred. |
| Final held candidate `84062644d168cdfd5c06b0ec927d23bc015117ed2858cf3624d02c2fa09d05d2`; [inventory](../../../held-model-comparison/inventory.json) | The user stopped this route before a native invocation. It has no compiler result. |

The corrected scoped diagnostic was
`remote-9b8a555ea4e54935a9270c43cc6a9d8f`, using byte-identical `43c2…`
source, its native production setup and CLI profiler/diagnostic flags.
The native setup was obtained by `lake --no-build setup-file` at the
actual production source; diagnostic outputs stayed in scratch. The
[command receipts](../../../foundations/model-profile-native-command-receipts.json)
retain the exact setup and compiler arguments, unchanged `-M12800 -j4`
and package options. This was a compiler diagnostic, not validation or a
benchmark.

The target's named frames were header 0.122180 s, value elaboration
6.528896 s and kernel checking 101.046756 s, ending in a kernel
deterministic timeout. Those frames are inclusive/nested and must not be
summed. The
[target counters](../../../foundations/model-profile-target-counters.json)
retain all 139 projected counter lines and exact raw-log line locators;
reduction visits are not per-constant timings or a unique cause. The full
95,775,071-byte raw
[build.log](../../../foundations/remote-runs/remote-9b8a555ea4e54935a9270c43cc6a9d8f/build.log)
remains beside the
[run receipt](../../../foundations/remote-runs/remote-9b8a555ea4e54935a9270c43cc6a9d8f/receipt.json),
identified with its source/setup/resource records by
[profile execution](../../../foundations/model-profile-execution.json).
It is not copied into this case.

Two earlier diagnostics supply different evidence. `remote-ab30…`
failed preparation because the required setup file was absent and
launched no compiler. `remote-570d…` used the `b4099e46…` source with
declaration-local instrumentation and had parser/style errors; it is not
target-counter evidence for the unmodified theorem. The corrected
exact-source/CLI invocation supersedes neither failure's history.
The valid profile records no OOM event, forced kill or input drift.

### Preservation, restored source and active native pass

The principal preserved the seven untracked generic ModelComparison
sources, the uncompiled `840626…` consumer and the recovered exact
`ff9b…` source before removing the optional generic files from active
production. The
[held inventory](../../../held-model-comparison/inventory.json) records
their individual hashes, earlier leaf passes and evidence locators. The
[restoration record](../../../held-model-comparison/RESTORATION.json)
records the exact removed paths and the final choice: ModelTransport is
byte-identical to baseline HEAD, SHA-256
`363d12fefaaf986786f36294ba7d4405c5e05185e2ca09d553c5df8995c9938e`,
including its original `Universal.Basic` import. The inventory's proposed
import-only refinement was not the final active source.

The restoration record's earlier pending-execution field is superseded
by the actual post-migration
[ef5c log](../../../foundations/remote-runs/remote-ef5c095f029a485da33f86606ce56fc7/build.log)
and [receipt](../../../foundations/remote-runs/remote-ef5c095f029a485da33f86606ce56fc7/receipt.json).
That ordinary production build succeeded with one frontend and no failed
frontend: 13.513096 s execution, 13.928471 s wall and peak RSS
3,161,419,776 bytes. It recorded no OOM event, forced kill or input drift,
and the process group closed. Its
[source.json](../../../foundations/remote-runs/remote-ef5c095f029a485da33f86606ce56fc7/source.json)
has SHA-256
`3c68fc8a632c31c964fe98cace01edfcfff09a9b42c5e376189e78284aef6bb0`,
matching the receipt, with source-content identity
`3de47d2b74e7ed14d8c717a8fedeab7b19df7844cb2e1161b98c63c9708a2616`.
This is current execution evidence for the restored source, rather than
reuse of baseline compilation as a post-migration pass.

The
[minimal-implementation inspection](../../../foundations/minimal-implementation-audit.json)
covers the final 91 active changed origins and records the absence of the exact
optional namespace/import references in its stated scope. It does not
prove globally optimal implementation counts throughout the library.
The failed stronger intermediate route and the restored direct proof
have different proof/dependency closures; profiling also changes the
observation. No before/after timing ratio follows. The retained result is
the user-directed route choice, unchanged public conclusion and actual
restored-consumer pass. Optional all-model transport remains held and
unadopted; task-wide final checks are recorded below.

## Remaining limits

The active foundation integration is complete on the source-bound scope in
[the final report](../../../foundations/final-integration-report.md) and
[its result](../../../foundations/final-integration-result.json). Production
coverage and three existing tests passed. Native text style passed on 91
origins; all 15 declaration predicates passed on 990 ordinary and 482 generated
declarations; 21 builtin bindings passed with 20 compatible reuses and one
affected terminal performed; AX3 audited 14,854 declarations with only the
three approved foundations and zero violations. Reported builtin environment
registries were empty. Source policy covered 7,234 Lean files and native entry
generation checked the 6,688-import root. These observations are neither a
whole-library build nor a performance ratio.

Final declaration lint required two identity-value statements in Restriction
to name their actual nested module parents explicitly, normalizing implicit
`Functor.comp_obj` arguments. Both simp attributes, binders and reflexivity
proofs were retained. The verified old/current source delta is preserved in
[the normalization certificate](../../../foundation-p3/simpNF-statement-normalization.json),
with ordinary review reconciled to current source `36834cdc…`. The corrected
producer and existing tensor-pullback consumer compiled; no new models,
premises, suppression or larger budget was introduced. Final input binding,
group closure and guarded temporary-transport cleanup all completed.
The accepted milestones and earlier leaf observations retain their own
source versions; later changes do not inherit their historical timings.

P3a does not give arbitrary same-universe closedness. P3c now constructs
actual evaluation/right-tensor adjunction and proves the P3b stability
supplier in the stated `κ` sector; arbitrary smaller-world closure and a
smaller-ring lift/comparison remain separate. P3d proves its native slice,
Hom and binary tensor comparisons under the recorded conditions, without
a tensor-unit/coherence package or arbitrary-site adjoint-existence
theorem. P4 supplies additive Γ and optional terminal views, with no new
arbitrary-site global scalar-module action or injective/Ext existence
theorem. P5 preserves the existing localization triangles and supplies no
new geometric exactness theorem. Derived tensor/RHom, full six operations
and higher descent remain separate obligations.

The evolving P2 underlying extraction remains outside this case. The
optional derived-model route is now held rather than repaired or adopted;
its failed experiments and the restored active consumer are recorded
above on distinct source bases. Later passes or repairs must be recorded
on their actual source basis. This case adds
reusable construction methods and retained ordinary compiler evidence;
it supplies no broader speedup, compiler-cause or whole-library claim.
