/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.IdealTwist.Family
public import Aglib.AlgebraicGeometry.HilbertScheme.FieldCohomology
public import Aglib.AlgebraicGeometry.HilbertScheme.QuotientDirectImage
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Relative
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Isomorphism

/-!
# The geometric fibers of the twisted ideal sheaf of a Hilbert family

Let `Z` be a point of `Hilb^Φ(T)` (`IsHilbertFamily ι Φ g Z`) and `r ≥ hilbertRegularityBound n Φ`
a natural number. Over a field `k`, for a closed subscheme `W ⊆ P^n_k` with Hilbert polynomial
`Φ`, the ideal sheaf `I_W` is `m`-regular (Mumford's bound, `isProjectiveRegular_idealModule`), so
`H^q(I_W(r)) = H^q(𝒪_W(r)) = 0` for `q ≥ 1` (the vanishing half of Nitsure, *Construction of
Hilbert and Quot schemes*, arXiv:math/0504590v1, Lemma 2.1 (c), p. 10, with the sequence
`0 → I_W → 𝒪 → 𝒪_W → 0`) and the Euler characteristics give
`h^0(𝒪_W(r)) = Φ(r)` and `h^0(I_W(r)) = C(n + r, r) - Φ(r)`
(`projectiveCohomologyDim_quotientTwist_zero_cast`, `projectiveCohomologyDim_idealTwist_zero`, in
`HilbertScheme/FieldCohomology`).

At a point `t : Spec K ⟶ T`, the fiber of `X_T ⟶ T` is `P^n_K` through `pointMap ι g t`
(`isPullback_pointMap`), and the pullback of `I_Z(r)` to it is `I_{Z_t}(r)`
(`pointMapIdealTwistIso`, using flatness of `Z`). Hence
`IsHilbertFamily.fibreCohomologyConcentrated_familyIdealTwist`: `I_Z(r)` is fiberwise concentrated
in degree zero, of rank `(n + r).choose r - ⌊Φ(r)⌋₊`, in the form `FibreCohomologyConcentrated`
consumed by `Cohomology/BaseChange/NoetherianPushforward` (Nitsure, §5, p. 25, "Use of
m-Regularity").
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Polynomial

universe u

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Cohomology Scheme.Modules.QuasiCoherent

variable (ι : Type u) {A : Type u} [CommRing A] {Φ : ℚ[X]} {T : Scheme.{u}}
  {g : T ⟶ Spec (CommRingCat.of A)} {Z : (pullback (toSpec A ι) g).IdealSheafData}
  (n : ℕ) (e : ι ≃ Fin (n + 1))

include e in
/-- **The geometric fibers of `I_Z(r)`** (Nitsure, arXiv:math/0504590v1, Lemma 2.1 (c), p. 10,
and §5, p. 25): for a point `Z` of `Hilb^Φ(T)` and a natural `r ≥ hilbertRegularityBound n Φ`, at
every point `t : Spec K ⟶ T` with `K` algebraically closed, the higher cohomology of `I_Z(r)` on
the fiber of `X_T ⟶ T` vanishes and its `H^0` has dimension `(n + r).choose r - ⌊Φ(r)⌋₊`. -/
theorem IsHilbertFamily.fibreCohomologyConcentrated_familyIdealTwist
    (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) :
    FibreCohomologyConcentrated (pullback.snd (toSpec A ι) g) (familyIdealTwist ι g Z r)
      ((n + r).choose r - ⌊Φ.eval (r : ℚ)⌋₊) := by
  have := hZ.flat
  intro K _ _ t
  have hp := isPullback_pointMap ι g t
  let M := (Scheme.Modules.pullback (pullback.fst (pullback.snd (toSpec A ι) g) t)).obj
    (familyIdealTwist ι g Z r)
  let C : (Scheme.Modules.pullback hp.isoPullback.hom).obj M ≅
      idealTwist ι (Z.comap (pointMap ι g t)) r :=
    (Scheme.Modules.pullbackComp hp.isoPullback.hom _).app _ ≪≫
      (Scheme.Modules.pullbackCongr hp.isoPullback_hom_fst).app _ ≪≫
        pointMapIdealTwistIso ι Z t r
  refine ⟨?_, fun q hq => ?_⟩
  · refine (finrank_moduleCohomology_eq_of_isIso hp.isoPullback.hom
      (pullback.snd (pullback.snd (toSpec A ι) g) t) (toSpec K ι) hp.isoPullback_hom_snd M C
        0).trans ?_
    exact projectiveCohomologyDim_idealTwist_zero ι n e _
      (hZ.subschemeHilbertPolynomial_fiber K t) r hr
  · have h := hZ.subsingleton_moduleCohomology_idealTwist ι n e t r hr q hq.ne'
    have h' := moduleCohomology_subsingleton_of_iso C.symm q h
    exact (moduleCohomologyPullback_bijective hp.isoPullback.hom M q).injective.subsingleton

end AlgebraicGeometry.ProjectiveSpace
