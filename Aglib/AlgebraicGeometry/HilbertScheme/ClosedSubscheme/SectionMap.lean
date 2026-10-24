/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.DirectImageSheafQuotient

/-!
# Sections of `𝒪(r)` restricted to a family and pushed to the base

Let `A` be a ring, `P = P^n_A`, `T` a scheme over `Spec A`, and `X_T = P ×_{Spec A} T` with
projections `p` (`pullback.fst`) and `π` (`pullback.snd`). Fix `r : ℕ` and a map
`φ : 𝒪_P^J ⟶ 𝒪(r)` on `P` out of a free sheaf, that is, a family of global sections of `𝒪(r)`
indexed by `J`. For a closed subscheme `Z ⊆ X_T`:

* `familySectionMap ι g r φ Z : 𝒪^J ⟶ 𝒪_Z(r)` is the pulled-back map `p^* φ` followed by the
  restriction `𝒪(r) ⟶ 𝒪(r) ⊗ 𝒪_Z`;
* `directImageSectionMap ι g r φ Z : 𝒪_T^J ⟶ π_* 𝒪_Z(r)` is its adjoint: the images of the
  sections of `φ` in `Γ(Z, 𝒪_Z(r))`, as sections of the direct image.

For `φ = monomialMap ι A r` these are `familyQuotientMonomialMap` and `directImageQuotientMap`
(`HilbertScheme/DirectImageSheafQuotient`), by definition (`familySectionMap_monomialMap`,
`directImageSectionMap_monomialMap`); the base-change statements below are the same, for a
general `φ`.

* `directImageSectionMap_eq_zero_iff`: the adjoint vanishes iff `familySectionMap` does.
* `directImageSectionMap_baseChange`: for `f : T' ⟶ T` over `Spec A`, the pullback along `f` of
  `directImageSectionMap` of `Z`, followed by the base-change mate of `isPullback_baseChangeMap`
  and `b^* 𝒪_Z(r) ≅ 𝒪_{Z.comap b}(r)`, is `directImageSectionMap` of `Z.comap b`.
* `IsHilbertFamily.pullback_map_directImageSectionMap_eq_zero_iff`: for a point `Z` of
  `Hilb^Φ(T)`, `T` locally Noetherian and `r ≥ hilbertRegularityBound n Φ`, the mate is invertible
  (Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 25, via
  Theorem 3.7), so `f^*` of `directImageSectionMap` vanishes iff `directImageSectionMap` of the
  pulled-back family does.

Consumer: the closed subfunctor `Hilb^Φ_C` of the Hilbert functor for a closed `C ⊆ P^n_A`
(`HilbertScheme/ClosedSubscheme/Representability`), where `φ` generates the ideal of `C` in degree
`r`.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpace

section Family

variable (ι : Type u) {A : Type u} [CommRing A] {T : Scheme.{u}}
  (g : T ⟶ Spec (CommRingCat.of A)) (r : ℕ) {J : Type u}
  (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
    twistingSheaf A ι (r : ℤ))

/-- The sections of `φ` on `P^n_A ×_{Spec A} T`, restricted to `Z`: the pullback of `φ` along the
first projection followed by the restriction `𝒪(r) ⟶ 𝒪(r) ⊗ 𝒪_Z`. -/
def familySectionMap (Z : (pullback (toSpec A ι) g).IdealSheafData) :
    SheafOfModules.free J ⟶ familyQuotientTwist ι g Z r :=
  pullbackFreeMap (pullback.fst (toSpec A ι) g) φ ≫ Z.twistedRestriction (familyTwistingSheaf ι g r)

theorem familySectionMap_def (Z : (pullback (toSpec A ι) g).IdealSheafData) :
    familySectionMap ι g r φ Z =
      pullbackFreeMap (pullback.fst (toSpec A ι) g) φ ≫
        Z.twistedRestriction (familyTwistingSheaf ι g r) :=
  rfl

/-- **The images of the sections of `φ` in the direct image** `𝒪_T^J ⟶ π_* 𝒪_Z(r)`: the adjoint
of `familySectionMap`. -/
def directImageSectionMap (Z : (pullback (toSpec A ι) g).IdealSheafData) :
    SheafOfModules.free (R := T.ringCatSheaf) J ⟶ directImageSheaf ι g Z r :=
  pushforwardFreeMap (pullback.snd (toSpec A ι) g) (familySectionMap ι g r φ Z)

/-- The adjoint vanishes exactly when the restricted sections do. -/
theorem directImageSectionMap_eq_zero_iff (Z : (pullback (toSpec A ι) g).IdealSheafData) :
    directImageSectionMap ι g r φ Z = 0 ↔ familySectionMap ι g r φ Z = 0 := by
  have h := comp_pushforwardFreeMap_eq_zero_iff (pullback.snd (toSpec A ι) g)
    (familySectionMap ι g r φ Z) (𝟙 (SheafOfModules.free (R := T.ringCatSheaf) J))
  rw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp] at h
  rw [directImageSectionMap, h]
  exact Preadditive.IsIso.comp_left_eq_zero _ _

/-- For the monomial map, `familySectionMap` is `familyQuotientMonomialMap`. -/
theorem familySectionMap_monomialMap (Z : (pullback (toSpec A ι) g).IdealSheafData) :
    familySectionMap ι g r (monomialMap ι A r) Z = familyQuotientMonomialMap ι g Z r :=
  rfl

/-- For the monomial map, `directImageSectionMap` is the evaluation map `directImageQuotientMap`. -/
theorem directImageSectionMap_monomialMap (Z : (pullback (toSpec A ι) g).IdealSheafData) :
    directImageSectionMap ι g r (monomialMap ι A r) Z = directImageQuotientMap ι g Z r :=
  rfl

/-- **The restricted sections under pullback**: for `p : Y ⟶ P^n_A ×_{Spec A} T` and an
identification `d` of the pullback of `𝒪(r)` along `p ≫ fst`, the pullback of `familySectionMap`
is the pulled-back map `φ` restricted to `Z.comap p`. -/
theorem pullbackFreeMap_familySectionMap {Y : Scheme.{u}}
    (p : Y ⟶ pullback (toSpec A ι) g) (Z : (pullback (toSpec A ι) g).IdealSheafData)
    {L' : Y.Modules}
    (d : (Scheme.Modules.pullback (p ≫ pullback.fst (toSpec A ι) g)).obj
      (twistingSheaf A ι (r : ℤ)) ≅ L') :
    pullbackFreeMap p (familySectionMap ι g r φ Z) ≫
        (Z.pullbackTensorQuotientIso p
          ((Scheme.Modules.pullbackComp p (pullback.fst (toSpec A ι) g)).app _ ≪≫ d)).hom =
      pullbackFreeMap (p ≫ pullback.fst (toSpec A ι) g) φ ≫ d.hom ≫
        (Z.comap p).twistedRestriction L' := by
  rw [familySectionMap, pullbackFreeMap_comp_right, Category.assoc,
    Z.pullback_map_twistedRestriction, Iso.trans_hom, Iso.app_hom, Category.assoc,
    pullbackFreeMap_comp_assoc]

/-- `pullbackFreeMap_familySectionMap` when `p ≫ fst = q`. -/
theorem pullbackFreeMap_familySectionMap_of_comp_fst {Y : Scheme.{u}}
    (p : Y ⟶ pullback (toSpec A ι) g) (q : Y ⟶ ProjectiveSpace A ι)
    (hq : p ≫ pullback.fst (toSpec A ι) g = q) (Z : (pullback (toSpec A ι) g).IdealSheafData) :
    pullbackFreeMap p (familySectionMap ι g r φ Z) ≫
        (Z.pullbackTensorQuotientIso p
          ((Scheme.Modules.pullbackComp p (pullback.fst (toSpec A ι) g)).app _ ≪≫
            (Scheme.Modules.pullbackCongr hq).app (twistingSheaf A ι (r : ℤ)))).hom =
      pullbackFreeMap q φ ≫
        (Z.comap p).twistedRestriction
          ((Scheme.Modules.pullback q).obj (twistingSheaf A ι (r : ℤ))) := by
  rw [pullbackFreeMap_familySectionMap, Iso.app_hom, ← Category.assoc, pullbackFreeMap_congr]

variable {T' : Scheme.{u}} (g' : T' ⟶ Spec (CommRingCat.of A)) (f : T' ⟶ T) (h : f ≫ g = g')

/-- **The restricted sections are natural**: along the base-changed map
`b = baseChangeMap ι g g' f h`, `familySectionMap` pulls back to that of `Z.comap b`. -/
theorem pullbackFreeMap_familySectionMap_baseChangeMap
    (Z : (pullback (toSpec A ι) g).IdealSheafData) :
    pullbackFreeMap (baseChangeMap ι g g' f h) (familySectionMap ι g r φ Z) ≫
        (familyQuotientTwistBaseChangeIso ι g g' f h Z r).hom =
      familySectionMap ι g' r φ (Z.comap (baseChangeMap ι g g' f h)) :=
  ((congrArg (fun i => pullbackFreeMap (baseChangeMap ι g g' f h)
      (familySectionMap ι g r φ Z) ≫ i.hom)
    (familyQuotientTwistBaseChangeIso_eq ι g g' f h Z r)).trans
      (pullbackFreeMap_familySectionMap_of_comp_fst ι g r φ (baseChangeMap ι g g' f h)
        (pullback.fst (toSpec A ι) g') (baseChangeMap_fst ι g g' f h) Z)).trans
    (familySectionMap_def ι g' r φ (Z.comap (baseChangeMap ι g g' f h))).symm

/-- **The images of the sections in the direct image are natural**: for `f : T' ⟶ T` over
`Spec A` and `b = baseChangeMap ι g g' f h`, the pullback along `f` of `directImageSectionMap`
of `Z`, followed by the base-change mate of `isPullback_baseChangeMap` and
`π'_* (b^* 𝒪_Z(r) ≅ 𝒪_{Z.comap b}(r))`, is `directImageSectionMap` of `Z.comap b`. -/
theorem directImageSectionMap_baseChange (Z : (pullback (toSpec A ι) g).IdealSheafData) :
    pullbackFreeMap f (directImageSectionMap ι g r φ Z) ≫
        (cartesianBaseChangeMap (baseChangeMap ι g g' f h) (pullback.snd (toSpec A ι) g')
          (pullback.snd (toSpec A ι) g) f (isPullback_baseChangeMap ι g g' f h)).app
            (familyQuotientTwist ι g Z r) ≫
          (Scheme.Modules.pushforward (pullback.snd (toSpec A ι) g')).map
            (familyQuotientTwistBaseChangeIso ι g g' f h Z r).hom =
      directImageSectionMap ι g' r φ (Z.comap (baseChangeMap ι g g' f h)) :=
  pushforwardFreeMap_baseChange _ _ _ _ _ _ _ _
    (pullbackFreeMap_familySectionMap_baseChangeMap ι g r φ g' f h Z)

end Family

section LocallyNoetherian

variable (ι : Type u) {A : Type u} [CommRing A] (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]}
  {T : Scheme.{u}} [IsLocallyNoetherian T] {g : T ⟶ Spec (CommRingCat.of A)}
  {Z : (pullback (toSpec A ι) g).IdealSheafData}

include e in
/-- **Vanishing of the sections in the direct image is stable under base change**: for a point
`Z` of `Hilb^Φ(T)`, `T` locally Noetherian, a natural `r ≥ hilbertRegularityBound n Φ` and
`f : T' ⟶ T` over `Spec A`, `f^*` of `directImageSectionMap` of `Z` vanishes if and only if
`directImageSectionMap` of the pulled-back family `Z.comap b` does, since the base-change mate is
invertible (`IsHilbertFamily.isIso_cartesianBaseChangeMap_baseChangeMap`). -/
theorem IsHilbertFamily.pullback_map_directImageSectionMap_eq_zero_iff
    (hZ : IsHilbertFamily ι Φ g Z) (r : ℕ) (hr : hilbertRegularityBound n Φ ≤ r) {J : Type u}
    (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
      twistingSheaf A ι (r : ℤ))
    {T' : Scheme.{u}} (g' : T' ⟶ Spec (CommRingCat.of A)) (f : T' ⟶ T) (h : f ≫ g = g') :
    (Scheme.Modules.pullback f).map (directImageSectionMap ι g r φ Z) = 0 ↔
      directImageSectionMap ι g' r φ (Z.comap (baseChangeMap ι g g' f h)) = 0 := by
  have := hZ.isIso_cartesianBaseChangeMap_baseChangeMap ι n e r hr g' f h
  rw [← directImageSectionMap_baseChange ι g r φ g' f h Z, pullbackFreeMap_def]
  simp only [Category.assoc, Preadditive.IsIso.comp_left_eq_zero]
  rw [← Category.assoc, Preadditive.IsIso.comp_right_eq_zero,
    Preadditive.IsIso.comp_right_eq_zero]

end LocallyNoetherian

end ProjectiveSpace

end AlgebraicGeometry
