# Completed local rings after base completion

Import `Aglib.AlgebraicGeometry.Spec.CompletionLocalRing`.

Let A be a Noetherian commutative local ring, m its maximal ideal, and
Â = `AdicCompletion m A`. Let `f : X → Spec A` be an arbitrary scheme
morphism, and write

```text
X̂ = pullback f (completionSpecMap A)
β = pullback.fst f (completionSpecMap A) : X̂ → X.
```

`exists_completionBaseChangeStalkEquiv A f z hz` constructs an actual ring
equivalence between the maximal-adic completions of the original stalks
`X.presheaf.stalk (β z)` and `X̂.presheaf.stalk z`. Here `z` is an actual
point of the literal pullback and

```text
hz : maximalIdeal A ≤ (f (β z)).asIdeal
```

is exactly its closed-fibre condition. For every original stalk element s,
the equivalence E satisfies

```text
E (maximalCompletionMap _ s)
  = maximalCompletionMap _ (β.stalkMap z s).
```

`maximalCompletionMap` is the native completion `algebraMap`; thus this
equation retains the original projection stalk map. The theorem accepts
no completion equivalence, image-algebra identity, or flatness premise.
It requires no finite-type, normality, excellence, or finite-module
hypothesis on X. In particular it applies to the locally finite-type
surface consumer over its original Noetherian local base.

The equation is presented uniformly as the regular proposition
`CompletionImageEq e sourceMap targetMap originalMap s`, whose definition
is exactly `e (sourceMap s) = targetMap (originalMap s)`.
Both the generic construction and the concrete tensor/global comparison
use this same proposition. After obtaining the existential equivalence e,
`CompletionImageEq.eq (he s)` exposes the literal equality while retaining
the original map arguments. This is a presentation boundary, not a new premise.

For an actual point y of the literal completed residue fibre

```text
pullback (pullback.snd f (completionSpecMap A)) (residueSpecMap Â),
```

let z be its original first projection to X̂.
`completionResidueFiberPoint_projection A f y` proves the actual point
equation

```text
β z = pullback.fst f (residueSpecMap A)
        ((completionResidueFiberIso f).hom y).
```

`completionResidueFiberPoint_closed` derives the required condition hz
from this equation and the original residue quotient of A.
`exists_completionResidueFiberStalkEquiv A f y` therefore gives the
completed original stalk comparison without an additional closed-fibre
premise. The point and residue-field correspondence are the existing
canonical `completionResidueFiberIso`, rather than a chosen residue marking.

The proof chooses an actual affine open chart `uB : Spec B → X` covering
β z. Its A-algebra is the original ring map
`(Spec.preimage (uB ≫ f)).hom`, and its structural equation is
`Spec.map_preimage`. Put `T = Â ⊗[A] B`. The canonical
`completionAffineChartMap` maps `Spec T` to the literal X̂, with both
original projection equations. `completionAffineChartMap_isPullback`
proves that its square with uB and β is a pullback, by the actual tensor
pushout and pullback cancellation. Base change of the original open
immersion and its exact range equation lift z to an actual q in `Spec T`.

The native `Scheme.stalkMapIsoOfIsPullback` at q, with the explicit point
equality `t q = z`, identifies the arrow of the original β.stalkMap with
the arrow of the original tensor-coefficient spectrum stalk map. Complete
its two canonical local-ring isomorphisms using `completionCongr`, insert
`tensorStalkCompletionsEquiv`, and compose with the inverse target
comparison. Their typed original-element equations and the native arrow
square prove the displayed formula for E. No substitution into a chart
chosen from z and no equality of arbitrary completed image algebras is used.
`completionAffineChartSourceStalkIso` and
`completionAffineChartTargetStalkIso` expose those components on the
original native stalk ring objects, rather than asking instance inference
to recover them from an `Arrow` projection. `completionComposite` is the
shared typed three-equivalence construction used by both the affine and
global comparison and by their original-element equations.

For `f` locally of finite type,
`isRegularLocalRing_completionBaseChange_iff A f z hz` identifies regularity
of the two original stalks. The proof first derives local Noetherianity of
X from f over `Spec A`. The explicit completion Noetherianity theorem makes
`Spec Â` locally Noetherian, and local finite type of the actual
`pullback.snd f c` makes the literal pullback locally Noetherian. The native
stalk instances then supply both original stalks' Noetherianity. Applying
`AdicCompletion.isRegularLocalRing_iff_maximalCompletion` on each side and
transporting regularity along the actual C1 equivalence proves the result.
`isRegularLocalRing_completionResidueFiber_iff` derives the closed-fibre
condition at the actual y. Properness supplies local finite type for the
intended proper modification; no arbitrary-base-change preservation of
Noetherianity is assumed.

For the original proper `f : X → Spec A`,
`regularStalks_completionBaseChange_iff A f` gives

```text
RegularStalks X ↔ RegularStalks (pullback f (completionSpecMap A)).
```

It applies the existing `Scheme.regularStalks_of_regular_closedFibre`
criterion on both original proper schemes. In the forward direction,
the original pullback triangle and the actual completion map's
closed-point equation give the closed-fibre condition, and the pointwise
regularity comparison applies. In the reverse direction, the literal
residue-fibre projection lifts each original closed-fibre point;
`completionResidueFiberIso.inv` gives its corresponding actual completed
fibre point. The proved original projection equation identifies its image
with the original point, and pointwise regularity transfers back. The
existing criterion handles all generizations by the original stalk maps.
No openness of the regular locus, excellence, field or trait model is used.

The affine tensor-stalk supplier works more generally for every finitely
generated ideal I in a commutative ring A, every commutative A-algebra B,
and every actual prime q of `AdicCompletion I A ⊗[A] B` containing the
image of I. `tensorStalkCompletionsEquiv` completes the canonical
`Spec.stalkIso` comparisons and the proved actual
`AdicCompletion.tensorLocalCompletionsEquiv`; its `_algebraMap` theorem
uses the original `tensorCompletionSpecMap` stalk map. That spectrum map
is `Spec.map` of the original `includeRight`, using the shared
`AdicCompletion.tensorComparisonRingHom` presentation.

`completionTensorSpecIso` records the canonical affine presentation of the
literal completion pullback, with both original projections. The affine
`completionResidueFiberTensorMap` retains the same original residue-fibre
correspondence. These are explicit named suppliers for the general proof.

The full arbitrary-scheme C1 and pointwise regularity source at SHA256
`c8512946a69b5cad1b256cef8f274eae2f0a1edf293280ca38811abfbc39a894`
passed native `remote-0fb712` (source `42b0e59d`, 20 seconds) at the
standard budgets. Its exact source and paired document are preserved in
the author's scratch evidence. The current increment adds only the proper
global regularity adapter and its original point/map equations, reusing
the existing closed-fibre criterion. That increment has not yet been
compiled; the older pass does not cover it.

The regularity helper at SHA256
`3fa9ff9ddbf4ac120b6fe4f8ea79c42aace147e6333001e4ec1b06bb66285a0c`
passed `remote-da4109b3125a4c29a549760218865ba3`
(source `ce4f0ea1`, 4.3 seconds).
The lower ring provider remains frozen at
`7a4fe34d6e7640543f4c7b92c5fac0bfa3a6a056103bebc684e0c3b9aceba311`,
which passed `remote-81be4395af534548bf61a664032c024b`
(source `df2b110d`, 19 seconds).

The source basis is Aglib HEAD
`8b93cc5940dc93f39a2eaf05e6985af28250a578`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and Lean 4.34.1. No local
build, test, replay, diagnostic probe, or Git operation was run for this
continuation. No normality preservation is asserted. The current proper
global regularity adapter is a source candidate, with native compilation
and any coupled repairs still pending.
