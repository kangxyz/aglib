/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.UniversalSubschemePullback
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.EqualRank
public import Aglib.AlgebraicGeometry.Grassmannian.Quotient.UniversalQuotientPullback
public import Aglib.CategoryTheory.Monoidal.UntwistVanishing

/-!
# The Grassmannian point of a pulled-back universal family

Let `T` be a locally Noetherian scheme over `Spec A`, `ι ≃ Fin (n + 1)`,
`r ≥ hilbertRegularityBound n Φ` a natural number, `k = ⌊Φ(r)⌋₊`, `N = (n + r).choose r`, and
`φ : T ⟶ G` over `Spec A`, for the Grassmannian `G` of rank-`k` quotients of `𝒪^N`. If the
pullback `Z_T` of the universal subscheme along `P^n_φ` is a point of `Hilb^Φ(T)`, then its
Grassmannian point is `φ` (`IsHilbertFamily.grassmannianMap_eq_of_comap_universalHilbertSubscheme`):
the "⇐" half of
Nitsure's proof of Theorem 5.2 (*Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1,
§5, pp. 26–27), for `E = 𝒪`, up to the flattening step.

Nitsure (§5, p. 27) states that the stratum represents the functor "by its construction"; the
following equal-rank argument supplies that step:

* **The kernel generates the ideal in degree `r`.** For `ιK : K ⟶ 𝒪_T^{monomials}`
  (`K` quasi-coherent) the monomial evaluation `π^* K ⟶ 𝒪(r)` vanishes on `𝒪_{Z(K)}(r)`
  (`monomialEvaluation_comp_twistedRestriction_evaluationIdeal`): its twist by `-r` lands in the
  image ideal (`Scheme.Modules.Hom.comp_toQuotientModule_imageIdealData_eq_zero`), and untwisting
  is faithful (`MonoidalCategory.comp_rightUnitor_inv_whiskerLeft_eq_zero`). By adjunction,
  `K ⊆ ker q_{Z(K)}` (`comp_directImageQuotientMap_evaluationIdeal`).
* **Equal rank.** For `φ`, `K_φ = φ^* K_univ` is the kernel of the quotient `𝒪^N ⟶ φ^* Q_univ`
  classified by `φ`, and `Z_T = Z(K_φ)` (`universalHilbertSubscheme_comap_classifyingMap`). Both
  `φ^* Q_univ` and `π_* 𝒪_{Z_T}(r)` have rank `k`, so the induced surjection between them is an
  isomorphism (`Scheme.Modules.exists_iso_of_kernel_ι_comp_eq_zero_of_sheafHasRank`, from
  `isIso_of_epi_of_sheafHasRank`), and the two quotients have the same classifying map
  (`Grassmannian.classifyingMap_eq_of_isoUnder`).
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open scoped Polynomial

universe u

namespace AlgebraicGeometry

namespace ProjectiveSpace

section Vanishing

variable (ι : Type u) {A : Type u} [CommRing A] {T : Scheme.{u}}
  (g : T ⟶ Spec (CommRingCat.of A))

/-- **The monomial evaluation of `K` vanishes on `𝒪_{Z(K)}(r)`** (Nitsure, arXiv:math/0504590v1,
§5, p. 26: `K_Y` generates the ideal of `Z(K_Y)` in degree `r`): for quasi-coherent `K` and
`ιK : K ⟶ 𝒪_T^{monomials}`, the monomial evaluation `π^* K ⟶ 𝒪(r)` followed by the restriction to
`Z(K)` is zero. -/
theorem monomialEvaluation_comp_twistedRestriction_evaluationIdeal (r : ℕ) {K : T.Modules}
    [K.IsQuasicoherent]
    (ιK : K ⟶ SheafOfModules.free (R := T.ringCatSheaf) (Monomials ι r)) :
    monomialEvaluation ι g r ιK ≫
        (evaluationIdeal ι g r (monomialFamily (A := A) ι r) ιK).twistedRestriction
          (familyTwistingSheaf ι g r) = 0 := by
  have := isQuasicoherent_twistedEvaluationSource ι g r (K := K)
  have h : twistedEvaluationMap ι g r (monomialFamily (A := A) ι r) ιK ≫
      (evaluationIdeal ι g r (monomialFamily (A := A) ι r) ιK).toQuotientModule = 0 :=
    Scheme.Modules.Hom.comp_toQuotientModule_imageIdealData_eq_zero _
  generalize evaluationIdeal ι g r (monomialFamily (A := A) ι r) ιK = W at h ⊢
  rw [twistedEvaluationMap_eq, freeTransfer_comp_homogeneousEvaluation_monomialFamily,
    Category.assoc] at h
  rw [Scheme.IdealSheafData.twistedRestriction_def]
  exact MonoidalCategory.comp_rightUnitor_inv_whiskerLeft_eq_zero (familyTwistPairingIso ι g r)
    _ _ h

/-- **`K ⊆ ker q_{Z(K)}`**: for quasi-coherent `K` and `ιK : K ⟶ 𝒪_T^{monomials}`, the evaluation
map of `Z(K)` vanishes on `K`. -/
theorem comp_directImageQuotientMap_evaluationIdeal (r : ℕ) {K : T.Modules} [K.IsQuasicoherent]
    (ιK : K ⟶ SheafOfModules.free (R := T.ringCatSheaf) (Monomials ι r)) :
    ιK ≫ directImageQuotientMap ι g (evaluationIdeal ι g r (monomialFamily (A := A) ι r) ιK) r =
      0 :=
  (monomialEvaluation_comp_twistedRestriction_eq_zero_iff ι g r ιK _).mp
    (monomialEvaluation_comp_twistedRestriction_evaluationIdeal ι g r ιK)

end Vanishing

section GrassmannianPoint

variable (ι : Type u) {A : Type u} [CommRing A] (n : ℕ) (e : ι ≃ Fin (n + 1)) {Φ : ℚ[X]}
  {T : Scheme.{u}} [IsLocallyNoetherian T] {g : T ⟶ Spec (CommRingCat.of A)}

include e in
/-- **"⇐": the Grassmannian point of a pulled-back universal family is the given map** (Nitsure,
arXiv:math/0504590v1, §5, pp. 26–27, proof of Theorem 5.2 for `E = 𝒪`): for a locally Noetherian
`T` over `Spec A`, a natural `r ≥ hilbertRegularityBound n Φ` and a morphism `φ` over `Spec A`
from `T` to the Grassmannian of rank-`⌊Φ(r)⌋₊` quotients of `𝒪^N`, `N = (n + r).choose r`, if
the pullback of the universal subscheme along `P^n_φ` is a point of `Hilb^Φ(T)`, then its
Grassmannian point is `φ`. -/
theorem IsHilbertFamily.grassmannianMap_eq_of_comap_universalHilbertSubscheme (r : ℕ)
    (hr : hilbertRegularityBound n Φ ≤ r)
    (φ : Over.mk g ⟶
      Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r))
    (hZ : IsHilbertFamily ι Φ g ((universalHilbertSubscheme ι r ⌊Φ.eval (r : ℚ)⌋₊ n e).comap
      (baseChangeMap ι
        (Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r)).hom g
        φ.left (Over.w φ)))) :
    hZ.grassmannianMap ι n e r hr = φ := by
  set W := (universalHilbertSubscheme ι r ⌊Φ.eval (r : ℚ)⌋₊ n e).comap
    (baseChangeMap ι
      (Grassmannian.schemeOver (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊ ((n + r).choose r)).hom g
      φ.left (Over.w φ)) with hWdef
  let P := (Grassmannian.universalQuotientRep (CommRingCat.of A) ⌊Φ.eval (r : ℚ)⌋₊
    ((n + r).choose r)).pullback φ.left
  have hP : Grassmannian.classifyingMap (T := Over.mk g) P = φ :=
    Grassmannian.classifyingMap_pullback_universalQuotientRep φ
  let q' := P.toFree (monomialsEquiv ι n e r)
  have hofFree : Grassmannian.LocallyFreeQuotient.ofFree (monomialsEquiv ι n e r) q' P.hasRank =
      P :=
    Grassmannian.LocallyFreeQuotient.ofFree_toFree _ P
  have hW₀ := universalHilbertSubscheme_comap_classifyingMap ι r ⌊Φ.eval (r : ℚ)⌋₊ n e
    (T := Over.mk g) q' P.hasRank
  rw [hofFree, hP] at hW₀
  have hW : W = evaluationIdeal ι g r (monomialFamily (A := A) ι r) (Limits.kernel.ι q') := hW₀
  have : (Limits.kernel q').IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso
      (Grassmannian.LocallyFreeQuotient.ofFreeKernelIso (monomialsEquiv ι n e r) q' P.hasRank)
      inferInstance
  have := hZ.epi_directImageQuotientMap ι n e r hr
  have hvan : Limits.kernel.ι q' ≫ directImageQuotientMap ι g W r = 0 := by
    rw [hW]
    exact comp_directImageQuotientMap_evaluationIdeal ι g r (Limits.kernel.ι q')
  obtain ⟨i, hi⟩ := Scheme.Modules.exists_iso_of_kernel_ι_comp_eq_zero_of_sheafHasRank q'
    (directImageQuotientMap ι g W r) P.hasRank (hZ.sheafHasRank_directImageSheaf ι n e r hr) hvan
  calc hZ.grassmannianMap ι n e r hr
      = Grassmannian.classifyingMap (T := Over.mk g)
          (Grassmannian.LocallyFreeQuotient.ofFree (monomialsEquiv ι n e r)
            (directImageQuotientMap ι g W r) (hZ.sheafHasRank_directImageSheaf ι n e r hr)) :=
        rfl
    _ = Grassmannian.classifyingMap (T := Over.mk g)
          (Grassmannian.LocallyFreeQuotient.ofFree (monomialsEquiv ι n e r) q' P.hasRank) :=
        (Grassmannian.classifyingMap_eq_of_isoUnder
          (Grassmannian.LocallyFreeQuotient.isoUnderOfFree _ P.hasRank
            (hZ.sheafHasRank_directImageSheaf ι n e r hr) i hi)).symm
    _ = Grassmannian.classifyingMap (T := Over.mk g) P := by rw [hofFree]
    _ = φ := hP

end GrassmannianPoint

end ProjectiveSpace

end AlgebraicGeometry
