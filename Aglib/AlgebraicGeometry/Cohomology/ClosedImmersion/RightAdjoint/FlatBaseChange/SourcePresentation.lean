/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Quotient
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalModel.OpenTopClass.Source

/-!
# The original localized quotient source presentation

The original quotient-localization ring equivalence identifies the actual
source arrow, its module comparison, and its fixed-resolution homology map.
No alternate source equivalence or Ext transport is constructed here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings

universe u w

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} (I : Ideal R) (t : R)

local notation "A" => CommRingCat.of (Localization.Away t)
local notation "B" => CommRingCat.of (Localization.Away (Ideal.Quotient.mk I t))
local notation "C" => CommRingCat.of
  (Localization.Away t ⧸ I.map (algebraMap R (Localization.Away t)))
local notation "σ" => (CommRingCat.ofHom
  (IsLocalization.Away.map (Localization.Away t)
    (Localization.Away (Ideal.Quotient.mk I t)) (Ideal.Quotient.mk I) t) : A ⟶ B)
local notation "τ" => (CommRingCat.ofHom
  (Ideal.Quotient.mk (I.map (algebraMap R (Localization.Away t)))) : A ⟶ C)
local notation "e" => quotientAwayRingEquiv I t

/-- The original ring equivalence preserves the actual localized quotient arrow. -/
theorem quotientAwaySourceRingTriangle : τ ≫ (e).toCommRingCatIso.hom = σ := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact quotientAwayRingEquiv_mk I t a

/-- The actual source-isomorphism square, with unchanged identity ambient map. -/
theorem quotientAwaySourceSquare :
    IsPullback (Spec.map (e).toCommRingCatIso.inv) (Spec.map τ) (Spec.map σ) (𝟙 (Spec A)) := by
  apply IsPullback.of_horiz_isIso
  constructor
  rw [Category.comp_id]
  have h : σ ≫ (e).toCommRingCatIso.inv = τ := by
    rw [← quotientAwaySourceRingTriangle I t, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  exact (Spec.map_comp σ (e).toCommRingCatIso.inv).symm.trans (congrArg Spec.map h)

public instance quotientAwaySource_closed : IsClosedImmersion (Spec.map σ) :=
  IsClosedImmersion.spec_of_surjective σ
    (IsLocalization.map_surjective_of_surjective (Submonoid.powers t)
      (Localization.Away t) (Localization.Away (Ideal.Quotient.mk I t))
      Ideal.Quotient.mk_surjective)

public instance quotientAwayCanonicalSource_closed : IsClosedImmersion (Spec.map τ) :=
  IsClosedImmersion.spec_of_surjective τ Ideal.Quotient.mk_surjective

/-- The canonical quotient tensor comparison followed by the original source
module isomorphism is the original geometric localization source map. -/
theorem quotientAwaySourceModuleIso_comp :
    (ModuleCat.extendScalarsAlgebraObjIso R (Localization.Away t)
        (ModuleCat.of R (R ⧸ I)) ≪≫
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
        (Localization.Away t) I).symm.toLinearEquiv.toModuleIso).hom ≫
        (closedImmersionSourceModuleIso σ τ e (quotientAwaySourceSquare I t)).hom =
      (closedImmersionQuotientLocalizationSourceIso I t).hom := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  let q := ModuleCat.extendScalarsAlgebraObjIso R (Localization.Away t)
      (ModuleCat.of R (R ⧸ I)) ≪≫
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
      (Localization.Away t) I).symm.toLinearEquiv.toModuleIso
  let g := (closedImmersionSourceModuleIso σ τ e (quotientAwaySourceSquare I t)).hom
  have hc := ModuleCat.comp_apply q.hom g
    ((1 : Localization.Away t) ⊗ₜ[R,algebraMap R (Localization.Away t)]
      (Ideal.Quotient.mk I r))
  have hq := ModuleCat.quotientScalarExtensionIso_one_tmul
    (S := Localization.Away t) I r
  have hg := closedImmersionSourceModuleIso_hom_apply σ τ e
    (quotientAwaySourceSquare I t)
    (Ideal.Quotient.mk (I.map (algebraMap R (Localization.Away t)))
      (algebraMap R (Localization.Away t) r))
  have he := quotientAwayRingEquiv_mk I t (algebraMap R (Localization.Away t) r)
  have hl := closedImmersionQuotientLocalizationSourceIso_one_tmul I t r
  have hm := IsLocalization.map_eq (M := Submonoid.powers t)
    (T := Submonoid.powers (Ideal.Quotient.mk I t)) (S := Localization.Away t)
    (Q := Localization.Away (Ideal.Quotient.mk I t)) (g := Ideal.Quotient.mk I)
    (by rintro x ⟨n, rfl⟩; exact ⟨n, (map_pow (Ideal.Quotient.mk I) t n).symm⟩) r
  exact hc.trans ((congrArg (fun x : C => g x) hq).trans
    (hg.trans (he.trans (hm.trans hl.symm))))

/-- The actual source-presentation homology arrow on the same supplied resolution
is original Yoneda precomposition, not an independently chosen transport. -/
theorem quotientAwaySourceHomologyMap_ext
    {L : (Spec A).Modules} (J : InjectiveResolution L) [L.IsQuasicoherent]
    [HasExt.{w} (ModuleCat.{u} A)] (n : ℕ)
    (x : (show CochainComplex (ModuleCat.{u} B) ℤ from
      closedImmersionSourceResolutionComplex («A» := A) («B» := B) (L := L) J σ).homology (n : ℤ)) :
    affineClosedRightAdjointResolutionExtAddEquiv τ J n
        (closedImmersionSourceHomologyMap σ τ e (quotientAwaySourceSquare I t) J
          (n : ℤ) x) =
      (Ext.mk₀ (closedImmersionSourceModuleIso σ τ e
        (quotientAwaySourceSquare I t)).hom).comp
          (affineClosedRightAdjointResolutionExtAddEquiv σ J n x) (zero_add n) :=
  closedImmersionSourceHomologyMap_ext σ τ e (quotientAwaySourceSquare I t) J n x

/-- The same original source map cancels its inverse source factor in Ext. -/
theorem quotientAwaySourceHomologyMap_ext_cancel
    {L : (Spec A).Modules} (J : InjectiveResolution L) [L.IsQuasicoherent]
    [HasExt.{w} (ModuleCat.{u} A)] (n : ℕ)
    (ξ : Ext.{w} («C» := ModuleCat.{u} A)
      ((ModuleCat.restrictScalars (τ).hom).obj (ModuleCat.of C C))
      ((moduleSpecΓFunctor (R := A)).obj L) n) :
    affineClosedRightAdjointResolutionExtAddEquiv τ J n
      (closedImmersionSourceHomologyMap σ τ e (quotientAwaySourceSquare I t) J (n : ℤ)
        ((affineClosedRightAdjointResolutionExtAddEquiv σ J n).symm
          ((Ext.mk₀ (closedImmersionSourceModuleIso σ τ e
            (quotientAwaySourceSquare I t)).inv).comp ξ (zero_add n)))) = ξ :=
  closedImmersionSourceHomologyMap_ext_cancel σ τ e (quotientAwaySourceSquare I t) J n ξ

/-- On every open the original sheaf-homology source map has exactly the same
value as the original section-homology map, through the unchanged affine counits. -/
theorem quotientAwaySourceSheafHomologyMap_counit_section
    {L : (Spec A).Modules} (J : InjectiveResolution L) (n : ℤ)
    (x : (show CochainComplex (ModuleCat.{u} B) ℤ from
      closedImmersionSourceResolutionComplex («A» := A) («B» := B) (L := L) J σ).homology n)
    (V : (Spec C).Opens) :
    (canonicalSourceSheafHomologyMap σ τ e (quotientAwaySourceSquare I t) J n).val.app (op V)
        ((canonicalTildeHomologyCounitMap (canonicalSourceSheafComplex σ J) n).val.app
          (op ((Spec.map (e).toCommRingCatIso.inv) ''ᵁ V))
          (tilde.toOpen
            ((closedImmersionSourceResolutionComplex («A» := A) («B» := B) (L := L) J σ).homology n)
            ((Spec.map (e).toCommRingCatIso.inv) ''ᵁ V) x)) =
      (canonicalTildeHomologyCounitMap (canonicalSourceSheafComplex τ J) n).val.app (op V)
        (tilde.toOpen
          ((closedImmersionSourceResolutionComplex («A» := A) («B» := C) (L := L) J τ).homology n) V
          (closedImmersionSourceHomologyMap σ τ e (quotientAwaySourceSquare I t) J n x)) :=
  canonicalSourceSheafHomologyMap_counit_section σ τ e (quotientAwaySourceSquare I t) J n x V

/-- The actual quotient localization arrow is the original principal arrow followed
by the inverse of the original quotient-away equivalence. -/
theorem quotientAwaySourceLocalizationRingTriangle :
    (CommRingCat.ofHom (algebraMap (R ⧸ I)
      (Localization.Away t ⧸ I.map (algebraMap R (Localization.Away t)))) :
        CommRingCat.of (R ⧸ I) ⟶ C) ≫
        (e).toCommRingCatIso.hom =
      (CommRingCat.ofHom
        (algebraMap (R ⧸ I) (Localization.Away (Ideal.Quotient.mk I t)))) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hq := Ideal.Quotient.algebraMap_quotient_map_quotient
    (S := Localization.Away t) (p := I) r
  have he := quotientAwayRingEquiv_mk I t (algebraMap R (Localization.Away t) r)
  have hm := IsLocalization.map_eq (M := Submonoid.powers t)
    (T := Submonoid.powers (Ideal.Quotient.mk I t)) (S := Localization.Away t)
    (Q := Localization.Away (Ideal.Quotient.mk I t)) (g := Ideal.Quotient.mk I)
    (by rintro x ⟨n, rfl⟩; exact ⟨n, (map_pow (Ideal.Quotient.mk I) t n).symm⟩) r
  exact (congrArg (fun x : C => (e) x) hq).trans (he.trans hm)

/-- Identify the literal canonical quotient-localization source arrow without
changing the original quotient-away equivalence. -/
theorem quotientAwaySourceLocalizationSpecMap :
    Spec.map (CommRingCat.ofHom (algebraMap (R ⧸ I)
      (Localization.Away t ⧸ I.map (algebraMap R (Localization.Away t))))) =
      Spec.map (e).toCommRingCatIso.inv ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (R ⧸ I) (Localization.Away (Ideal.Quotient.mk I t)))) := by
  have h := quotientAwaySourceLocalizationRingTriangle I t
  have h' := congrArg (fun f : CommRingCat.of (R ⧸ I) ⟶ B => f ≫ (e).toCommRingCatIso.inv) h
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h'
  exact (congrArg Spec.map h').trans (Spec.map_comp
    (CommRingCat.ofHom
      (algebraMap (R ⧸ I) (Localization.Away (Ideal.Quotient.mk I t))))
    (e).toCommRingCatIso.inv)

end AlgebraicGeometry.Scheme.Modules
