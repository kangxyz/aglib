/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.ClosedSubscheme.SectionMap
public import Aglib.AlgebraicGeometry.HilbertScheme.IdealTwist.Evaluation
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Uniqueness
public import Aglib.AlgebraicGeometry.Modules.ZeroLocus.Order
public import Aglib.AlgebraicGeometry.Modules.ZeroLocus.Pullback
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.PairingComp
public import Aglib.CategoryTheory.Monoidal.UntwistVanishing

/-!
# Containment in a closed subscheme cut out in degree `r`

Let `A` be a ring, `P = P^n_A`, `r : ℕ` and `φ : 𝒪_P^J ⟶ 𝒪(r)` a family of global sections of
`𝒪(r)`. Its **section pairing** `sectionPairing ι r φ : 𝒪_P^J ⊗ 𝒪(-r) ⟶ 𝒪(r) ⊗ 𝒪(-r) ≅ 𝒪`
untwists it; when the image ideal of the section pairing is the ideal of a closed subscheme
`C ⊆ P`, the sections of `φ` generate `I_C(r)` (`HilbertScheme/ClosedSubscheme/Generation` produces
such `φ` for `r ≫ 0`).

For a scheme `T` over `Spec A`, `X_T = P ×_{Spec A} T` with `p = pullback.fst`, and a closed
subscheme `V ⊆ X_T`:

* `imageIdealData_familySectionPairing`: the pulled-back pairing
  `familySectionPairing ι g r φ : 𝒪^J ⊗ 𝒪(-r) ⟶ 𝒪(r) ⊗ 𝒪(-r) ≅ 𝒪` on `X_T` has image ideal
  `I(sectionPairing).comap p`. The image ideal commutes with every pullback
  (`Scheme.Modules.Hom.imageIdealData_pullback`; the ideal of a pulled-back closed subscheme is the
  image of the pulled-back ideal, Stacks Project, Tag 01JU (1)), so if `C` is cut out by `φ`, then
  `C_T = C.comap p` is cut out by the pulled-back sections, even though `C` need not be flat over
  `A`.
* `comap_le_iff_familySectionMap_eq_zero`: if `C` is the image ideal of the section pairing,
  then `C_T ≤ V` (that is, `V ⊆ C_T` as subschemes) if and only if the pulled-back sections of
  `φ` vanish on `V`: `p^* φ ⟶ 𝒪(r) ⊗ 𝒪_V` is zero. "⇒": the pairing then lands in the ideal of
  `V`, and untwisting is faithful (`MonoidalCategory.comp_rightUnitor_inv_whiskerLeft_eq_zero`).
  "⇐": the sections lift to `I_V(r)` (`familyIdealTwistLift`), and the untwisted inclusion
  `I_V(r) ⊗ 𝒪(-r) ⟶ 𝒪` has image ideal `V` (`imageIdealData_twistPairing_of_epi`).
* `comap_le_iff_directImageSectionMap_eq_zero`: the same with the images of the sections in
  `π_* 𝒪_V(r)` (`directImageSectionMap`), by adjunction.

No flatness, Noetherian or finiteness hypothesis is used. This is the closed-subfunctor step for
`Hilb^Φ_C` (Picard plan, row F13; Nitsure, *Construction of Hilbert and Quot schemes*,
arXiv:math/0504590v1, Lemma 5.4 (ii), p. 25, for `𝒪_{P^n_A} ↠ 𝒪_C`, used for Theorem 6.1, p. 28,
with closed `X = C`): `V ⊆ C_T` is the vanishing of `p^* I_C ⟶ 𝒪 ⟶ 𝒪_V`. Expressing this
vanishing through the images of the sections of `φ` in `π_* 𝒪_V(r)` replaces Nitsure's vanishing
scheme (Remark 3.6, p. 17) and is not in the source.
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

section Pairing

variable (ι : Type u) {A : Type u} [CommRing A] (r : ℕ) {J : Type u}
  (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
    twistingSheaf A ι (r : ℤ))

/-- **The section pairing** `𝒪_P^J ⊗ 𝒪(-r) ⟶ 𝒪(r) ⊗ 𝒪(-r) ≅ 𝒪` of `φ : 𝒪_P^J ⟶ 𝒪(r)`, through
`twistingTensorNegIso`. For `φ = homogeneousEvaluation ι r s` this is
`homogeneousEvaluationPairing ι r s`. -/
def sectionPairing :
    (show (ProjectiveSpace A ι).Modules from
      Scheme.Modules.tensorSheaf (ProjectiveSpace A ι)
        (SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J)
        (twistingSheaf A ι (-(r : ℤ)))) ⟶
      (show (ProjectiveSpace A ι).Modules from
        SheafOfModules.unit (ProjectiveSpace A ι).ringCatSheaf) :=
  Scheme.Modules.tensorSheafMap (ProjectiveSpace A ι) φ (𝟙 _) ≫
    (twistingTensorNegIso (R := A) (ι := ι) (r : ℤ)).hom

theorem sectionPairing_def :
    sectionPairing ι r φ =
      Scheme.Modules.tensorSheafMap (ProjectiveSpace A ι) φ (𝟙 _) ≫
        (twistingTensorNegIso (R := A) (ι := ι) (r : ℤ)).hom :=
  rfl

/-- For a family of homogeneous polynomials, the section pairing of its evaluation is
`homogeneousEvaluationPairing`. -/
theorem sectionPairing_homogeneousEvaluation {I : Type u}
    (s : I → MvPolynomial.homogeneousSubmodule ι A r) :
    sectionPairing ι r (homogeneousEvaluation ι r s) = homogeneousEvaluationPairing ι r s :=
  rfl

/-- The source of the section pairing is quasi-coherent. -/
theorem isQuasicoherent_sectionPairingSource :
    (Scheme.Modules.tensorSheaf (ProjectiveSpace A ι)
        (SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J)
        (twistingSheaf A ι (-(r : ℤ)))).IsQuasicoherent :=
  Scheme.Modules.isQuasicoherent_moduleTensorLeftFunctor _ _

end Pairing

section Family

variable (ι : Type u) {A : Type u} [CommRing A] {T : Scheme.{u}}
  (g : T ⟶ Spec (CommRingCat.of A)) (r : ℕ) {J : Type u}
  (φ : SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J ⟶
    twistingSheaf A ι (r : ℤ))

/-- **The section pairing on `X_T = P^n_A ×_{Spec A} T`**: `p^* φ ⊗ 𝒪(-r)` followed by the
pairing `𝒪(r) ⊗ 𝒪(-r) ≅ 𝒪` (`familyTwistPairingIso`). -/
def familySectionPairing :
    (show (pullback (toSpec A ι) g).Modules from
      Scheme.Modules.tensorSheaf (pullback (toSpec A ι) g)
        (SheafOfModules.free (R := (pullback (toSpec A ι) g).ringCatSheaf) J)
        (familyTwistingSheaf ι g (-(r : ℤ)))) ⟶
      (show (pullback (toSpec A ι) g).Modules from
        SheafOfModules.unit (pullback (toSpec A ι) g).ringCatSheaf) :=
  Scheme.Modules.tensorSheafMap _ (pullbackFreeMap (pullback.fst (toSpec A ι) g) φ) (𝟙 _) ≫
    (familyTwistPairingIso ι g r).hom

theorem familySectionPairing_def :
    familySectionPairing ι g r φ =
      Scheme.Modules.tensorSheafMap _ (pullbackFreeMap (pullback.fst (toSpec A ι) g) φ) (𝟙 _) ≫
        (familyTwistPairingIso ι g r).hom :=
  rfl

/-- The source of the pulled-back section pairing is quasi-coherent. -/
theorem isQuasicoherent_familySectionPairingSource :
    (Scheme.Modules.tensorSheaf (pullback (toSpec A ι) g)
        (SheafOfModules.free (R := (pullback (toSpec A ι) g).ringCatSheaf) J)
        (familyTwistingSheaf ι g (-(r : ℤ)))).IsQuasicoherent :=
  Scheme.Modules.isQuasicoherent_moduleTensorLeftFunctor _ _

/-- The pulled-back section pairing is the pullback of the section pairing, after the
identification `𝒪^J ⊗ p^* 𝒪(-r) ≅ p^* 𝒪_P^J ⊗ p^* 𝒪(-r)`. -/
theorem familySectionPairing_eq :
    familySectionPairing ι g r φ =
      Scheme.Modules.tensorSheafMap _ (pullbackFreeIso (pullback.fst (toSpec A ι) g) J).inv
          (𝟙 _) ≫
        Scheme.Modules.pullbackPairing (pullback.fst (toSpec A ι) g) (sectionPairing ι r φ) := by
  rw [familySectionPairing_def, familyTwistPairingIso_hom, sectionPairing_def,
    pullbackPairing_tensorSheafMap_comp, tensorSheafMap_comp_assoc, Category.id_comp,
    ← pullbackFreeMap_def]

/-- **The pulled-back section pairing cuts out the pulled-back closed subscheme**: its image
ideal is the pullback along `p` of the image ideal of the section pairing. -/
theorem imageIdealData_familySectionPairing :
    Scheme.Modules.Hom.imageIdealData (familySectionPairing ι g r φ) =
      (Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ)).comap
        (pullback.fst (toSpec A ι) g) := by
  have := isQuasicoherent_sectionPairingSource ι r (A := A) (J := J)
  let E := Scheme.Modules.tensorSheafIso _
      (pullbackFreeIso (pullback.fst (toSpec A ι) g) J).symm (Iso.refl _) ≪≫
    (pullbackTensorMapIso (pullback.fst (toSpec A ι) g)
      (SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) J)
      (twistingSheaf A ι (-(r : ℤ)))).symm
  have hE : familySectionPairing ι g r φ =
      E.hom ≫ Scheme.Modules.Hom.pullbackToUnit (pullback.fst (toSpec A ι) g)
        (sectionPairing ι r φ) := by
    rw [familySectionPairing_eq]
    simp only [E, Iso.trans_hom, Iso.symm_hom, tensorSheafIso_hom, Iso.refl_hom, Category.assoc,
      Scheme.Modules.pullbackPairing, Scheme.Modules.Hom.pullbackToUnit]
  rw [hE, Scheme.Modules.Hom.imageIdealData_precomp_iso,
    Scheme.Modules.Hom.imageIdealData_pullback]

/-- **Containment in a pulled-back closed subscheme cut out in degree `r`**: if the closed
subscheme `C ⊆ P^n_A` is the image ideal of the section pairing of `φ`, then for every closed
subscheme `V` of `X_T = P^n_A ×_{Spec A} T`, `C_T = C.comap p ≤ V` (`V ⊆ C_T` as subschemes) if
and only if the pulled-back sections `p^* φ` vanish on `V`. -/
theorem comap_le_iff_familySectionMap_eq_zero {C : (ProjectiveSpace A ι).IdealSheafData}
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = C)
    (V : (pullback (toSpec A ι) g).IdealSheafData) :
    C.comap (pullback.fst (toSpec A ι) g) ≤ V ↔ familySectionMap ι g r φ V = 0 := by
  rw [← hC, ← imageIdealData_familySectionPairing]
  have := isQuasicoherent_familySectionPairingSource ι g r (J := J)
  constructor
  · intro hle
    have h := Scheme.Modules.Hom.comp_toQuotientModule_eq_zero_of_imageIdealData_le _ hle
    rw [familySectionPairing_def, Category.assoc] at h
    rw [familySectionMap_def, Scheme.IdealSheafData.twistedRestriction_def]
    exact MonoidalCategory.comp_rightUnitor_inv_whiskerLeft_eq_zero
      (familyTwistPairingIso ι g r) _ _ h
  · intro h0
    have hj : pullbackFreeMap (pullback.fst (toSpec A ι) g) φ ≫
        (ρ_ (familyTwistingSheaf ι g r)).inv ≫ (familyTwistedShortComplex ι g V r).g = 0 := by
      rw [← V.twistedRestriction_eq_shortComplex_map_g]
      exact h0
    have : (Scheme.Hom.idealModule V.subschemeι).IsQuasicoherent :=
      V.idealModule_isQuasicoherent
    have : (familyIdealTwist ι g V r).IsQuasicoherent :=
      Scheme.Modules.isQuasicoherent_moduleTensorLeftFunctor _ _
    have hV := imageIdealData_twistPairing_of_epi ι V r (𝟙 (familyIdealTwist ι g V r))
    rw [Category.id_comp] at hV
    calc Scheme.Modules.Hom.imageIdealData (familySectionPairing ι g r φ)
        = Scheme.Modules.Hom.imageIdealData
            (Scheme.Modules.tensorSheafMap _ (familyIdealTwistLift ι V r _ hj) (𝟙 _) ≫
              Scheme.Modules.tensorSheafMap _ (familyIdealTwistInclusion ι V r) (𝟙 _) ≫
                (familyTwistPairingIso ι g r).hom) := by
          congr 1
          rw [familySectionPairing_def, tensorSheafMap_comp_assoc, familyIdealTwistLift_inclusion,
            Category.comp_id]
      _ ≤ Scheme.Modules.Hom.imageIdealData
            (Scheme.Modules.tensorSheafMap _ (familyIdealTwistInclusion ι V r) (𝟙 _) ≫
              (familyTwistPairingIso ι g r).hom) :=
          Scheme.Modules.Hom.imageIdealData_comp_le _ _
      _ = V := hV

/-- **Containment through the direct image**: under the hypothesis of
`comap_le_iff_familySectionMap_eq_zero`, `C_T ≤ V` if and only if the images of the sections of
`φ` in `π_* 𝒪_V(r)` vanish (`directImageSectionMap`). -/
theorem comap_le_iff_directImageSectionMap_eq_zero {C : (ProjectiveSpace A ι).IdealSheafData}
    (hC : Scheme.Modules.Hom.imageIdealData (sectionPairing ι r φ) = C)
    (V : (pullback (toSpec A ι) g).IdealSheafData) :
    C.comap (pullback.fst (toSpec A ι) g) ≤ V ↔ directImageSectionMap ι g r φ V = 0 :=
  (comap_le_iff_familySectionMap_eq_zero ι g r φ hC V).trans
    (directImageSectionMap_eq_zero_iff ι g r φ V).symm

end Family

end ProjectiveSpace

end AlgebraicGeometry
