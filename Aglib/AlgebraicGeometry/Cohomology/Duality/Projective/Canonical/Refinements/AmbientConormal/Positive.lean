/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.AmbientConormal.Maps

/-!
# Original positive conormal columns as unit morphisms

The original ideal section is the original affine cotangent class after
the native comparison. Its first conormal arrow is the positive unit
tensor of the same differential; the second arrow is the differential of
the original quotient element.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules.Differentials
open scoped TensorProduct ChangeOfRings

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The actual normal unit morphism is the original cotangent class under the original
affine ideal-pullback comparison. -/
theorem canonicalAffineNormalSectionHom_affineClass
    {R A B : CommRingCat.{u}} (α : R ⟶ A) (σ : A ⟶ B)
    (hσ : Function.Surjective σ) (x : RingHom.ker σ.hom) :
    canonicalAffineNormalSectionHom σ x ≫
        (relativeConormalAffineIdealPullbackIso α σ hσ).hom =
      canonicalAffineUnitSection (relativeConormalAffineModule α σ hσ)
        (relativeConormalAffineClass α σ hσ x) := by
  let E := relativeConormalAffineModule α σ hσ
  let e := relativeConormalAffineIdealPullbackIso α σ hσ
  let v := relativeConormalAffineClass α σ hσ x
  apply (unitHomGlobalSectionsEquiv (Spec B) (tilde E)).injective
  change e.hom.val.app (op ⊤)
      ((canonicalAffineNormalSectionHom σ x).val.app (op ⊤) (1 : Γ(Spec B, ⊤))) =
    (canonicalAffineUnitSection E v).val.app (op ⊤) (1 : Γ(Spec B, ⊤))
  rw [canonicalAffineNormalSectionHom_app, canonicalAffineUnitSection_app]
  have hx := relativeConormalIdealClass_intrinsic α σ hσ x ⊤
  have hc := congrArg (fun f => f.val.app (op ⊤) (tilde.toOpen E ⊤ v)) e.inv_hom_id
  exact (congrArg (e.hom.val.app (op ⊤)) hx.symm).trans hc

/-- The first original conormal column retains the positive differential and the original
unit tensor, as an equality of actual unit-section morphisms. -/
theorem canonicalAffineConormal_f_unit
    {R A B : CommRingCat.{u}} (α : R ⟶ A) (σ : A ⟶ B)
    (hσ : Function.Surjective σ) (x : RingHom.ker σ.hom) :
    canonicalAffineNormalSectionHom σ x ≫
        (relativeConormalAffineIdealPullbackIso α σ hσ).hom ≫
        (tilde.functor B).map (relativeConormalAffineLinearF α σ hσ) =
      canonicalAffineUnitSection
        ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α))
        ((1 : B) ⊗ₜ[A,σ.hom] CommRingCat.KaehlerDifferential.d (f := α) (x : A)) := by
  let E := relativeConormalAffineModule α σ hσ
  let M := (ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α)
  let F := relativeConormalAffineLinearF α σ hσ
  let v := relativeConormalAffineClass α σ hσ x
  have hn := congrArg (fun f => f.val.app (op ⊤) (1 : Γ(Spec B, ⊤)))
    (canonicalAffineNormalSectionHom_affineClass α σ hσ x)
  have hF : F v = ((1 : B) ⊗ₜ[A,σ.hom]
      CommRingCat.KaehlerDifferential.d (f := α) (x : A)) :=
    relativeConormalAffineLinearF_class α σ hσ x
  apply (unitHomGlobalSectionsEquiv (Spec B) (tilde M)).injective
  change ((tilde.functor B).map F).val.app (op ⊤)
      (((relativeConormalAffineIdealPullbackIso α σ hσ).hom).val.app (op ⊤)
        ((canonicalAffineNormalSectionHom σ x).val.app (op ⊤) (1 : Γ(Spec B, ⊤)))) =
    (canonicalAffineUnitSection M ((1 : B) ⊗ₜ[A,σ.hom]
      CommRingCat.KaehlerDifferential.d (f := α) (x : A))).val.app
        (op ⊤) (1 : Γ(Spec B, ⊤))
  have hm := ConcreteCategory.congr_hom (tilde.toOpen_map_app F ⊤) v
  rw [canonicalAffineUnitSection_app] at hn ⊢
  exact (congrArg (((tilde.functor B).map F).val.app (op ⊤)) hn).trans
    (hm.trans (congrArg (tilde.toOpen M ⊤) hF))

/-- The second original conormal arrow carries the unit differential tensor to the
original differential of its quotient image. -/
theorem canonicalAffineConormal_g_unit
    {R A B : CommRingCat.{u}} (α : R ⟶ A) (σ : A ⟶ B)
    (hσ : Function.Surjective σ) (a : A) :
    canonicalAffineUnitSection
        ((ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α))
        ((1 : B) ⊗ₜ[A,σ.hom] CommRingCat.KaehlerDifferential.d (f := α) a) ≫
        (tilde.functor B).map (relativeConormalAffineLinearG α σ hσ) =
      canonicalAffineUnitSection (CommRingCat.KaehlerDifferential (α ≫ σ))
        (CommRingCat.KaehlerDifferential.d (f := α ≫ σ) (σ a)) := by
  let M := (ModuleCat.extendScalars σ.hom).obj (CommRingCat.KaehlerDifferential α)
  let Q := CommRingCat.KaehlerDifferential (α ≫ σ)
  let G := relativeConormalAffineLinearG α σ hσ
  let v : M := ((1 : B) ⊗ₜ[A,σ.hom] CommRingCat.KaehlerDifferential.d (f := α) a)
  have hG : G v = CommRingCat.KaehlerDifferential.d (f := α ≫ σ) (σ a) := by
    simpa only [one_smul] using relativeConormalAffineLinearG_tmul α σ hσ 1 a
  apply (unitHomGlobalSectionsEquiv (Spec B) (tilde Q)).injective
  change ((tilde.functor B).map G).val.app (op ⊤)
      ((canonicalAffineUnitSection M v).val.app (op ⊤) (1 : Γ(Spec B, ⊤))) =
    (canonicalAffineUnitSection Q
      (CommRingCat.KaehlerDifferential.d (f := α ≫ σ) (σ a))).val.app
        (op ⊤) (1 : Γ(Spec B, ⊤))
  rw [canonicalAffineUnitSection_app, canonicalAffineUnitSection_app]
  exact (ConcreteCategory.congr_hom (tilde.toOpen_map_app G ⊤) v).trans
    (congrArg (tilde.toOpen Q ⊤) hG)

end AlgebraicGeometry.Scheme.Modules
