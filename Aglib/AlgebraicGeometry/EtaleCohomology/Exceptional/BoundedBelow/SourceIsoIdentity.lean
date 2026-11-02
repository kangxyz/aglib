/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.SourceIsoIdentity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.SourceIsoRefinement
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.FamilyModelDiagram

/-! # Canonical reflexive source transport with independent middle-model families -/
@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

private theorem source_identity_follow
    {A B : Type*} [Category* A] [Category* B]
    (U : A ⥤ A) (d : U ≅ 𝟭 A) {F G : A ⥤ B}
    (s : F ≅ U ⋙ F) (m : F ≅ G)
    (h : s ≪≫ Functor.isoWhiskerRight d F ≪≫ Functor.leftUnitor F = Iso.refl F) :
    (s ≪≫ Functor.isoWhiskerLeft U m) ≪≫
      Functor.isoWhiskerRight d G ≪≫ Functor.leftUnitor G = m := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  have hk := congrArg (fun z => z.hom.app K) h
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Iso.refl_hom, NatTrans.id_app] at hk
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Category.assoc]
  erw [Category.comp_id] at hk
  erw [Category.comp_id, ← m.hom.naturality, ← Category.assoc, hk, Category.id_comp]
  rfl

private theorem source_identity_denormalize
    {A B : Type*} [Category* A] [Category* B]
    (U : A ⥤ A) (d : U ≅ 𝟭 A) {F G : A ⥤ B}
    (s : F ≅ U ⋙ G) (m : F ≅ G)
    (h : s ≪≫ Functor.isoWhiskerRight d G ≪≫ Functor.leftUnitor G = m) :
    s = m ≪≫ (Functor.leftUnitor G).symm ≪≫ Functor.isoWhiskerRight d.symm G := by
  have hh := congrArg (fun z => z ≪≫ (Functor.leftUnitor G).symm ≪≫
    (Functor.isoWhiskerRight d G).symm) h
  simp only [Iso.trans_assoc, Iso.self_symm_id_assoc,
    Iso.self_symm_id, Iso.trans_refl] at hh
  simpa only [Functor.isoWhiskerRight_symm] using hh

universe u dX dS dM₀ dM₁
variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{dX} (ModuleSheaf X Λ))
  (hS : HasDerivedCategory.{dS} (ModuleSheaf S Λ))
  (models₀ : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{dM₀} (ModuleSheaf C.Xbar Λ))
  (models₁ : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{dM₁} (ModuleSheaf C.Xbar Λ))

omit [QuasiCompact f] in
private theorem sourceIdentity_object (C : Hom.DenseCompactification f) :
    (Hom.DenseCompactification.sourceIso f (Iso.refl X) (Category.id_comp f)).obj C = C := by
  cases C
  simp only [Hom.DenseCompactification.sourceIso, Hom.DenseCompactification.ofSourceIso,
    Hom.Compactification.ofSourceIso, Iso.refl_hom, Category.id_comp]

/-- The chosen comparison at one original compactification is the mixed-family identity map. -/
theorem moduleCompactificationSourceIsoTo_refl (C : Hom.DenseCompactification f) :
    @moduleCompactificationSourceIsoTo X X S f f _ (Iso.refl X) (Category.id_comp f)
        Λ _ hX hX hS models₀ models₁ C C ≪≫
      Functor.isoWhiskerRight (@moduleDerivedInverseImageTorsionIdIso Λ _ X hX)
        ((@moduleCompactificationFunctor X S f Λ _ hX hS C (models₁ C))) ≪≫
      Functor.leftUnitor _ =
    moduleCompactificationFamilyComparison f Λ hX hS models₀ models₁ C := by
  let := hX
  let := hS
  let := models₀ C
  let F₀ := (@moduleCompactificationFunctor X S f Λ _ hX hS C (models₀ C))
  let F₁ := (@moduleCompactificationFunctor X S f Λ _ hX hS C (models₁ C))
  let U := @moduleDerivedInverseImageTorsion X X (𝟙 X) Λ _ hX hX
  let d := @moduleDerivedInverseImageTorsionIdIso Λ _ X hX
  let s : F₀ ≅ U ⋙ F₀ :=
    moduleRawCompactificationSourceIso (Iso.refl X) Λ f (Category.id_comp f)
      C.toCompactification
  let m : F₀ ≅ F₁ := moduleCompactificationFamilyComparison f Λ hX hS models₀ models₁ C
  have h := moduleRawCompactificationSourceIso_refl Λ C.toCompactification
  change s ≪≫ Functor.isoWhiskerRight d F₀ ≪≫ Functor.leftUnitor F₀ ≪≫
    Iso.refl F₀ = Iso.refl F₀ at h
  rw [Iso.trans_refl] at h
  change ((s ≪≫ Functor.isoWhiskerLeft U m) ≪≫
    Functor.isoWhiskerLeft U (@moduleCompactificationComparison X S f _ Λ _ hX hS
      models₁ C C)) ≪≫ Functor.isoWhiskerRight d F₁ ≪≫ Functor.leftUnitor F₁ = m
  rw [moduleCompactificationComparison_self, Functor.isoWhiskerLeft_refl, Iso.trans_refl]
  exact source_identity_follow U d s m h

variable [Nonempty (Hom.DenseCompactification f)]

/-- The original mixed-family identity comparison at the supplied chosen compactification. -/
def moduleExceptionalDirectImagePlusFamilyComparisonOfNonempty :
    (@moduleExceptionalDirectImagePlusOfNonempty X S f _ Λ _ hX hS (models₀
      (moduleExceptionalSuppliedCompactification f))) ≅
      (@moduleExceptionalDirectImagePlusOfNonempty X S f _ Λ _ hX hS (models₁
        (moduleExceptionalSuppliedCompactification f))) :=
  moduleCompactificationFamilyComparison f Λ hX hS models₀ models₁
    (moduleExceptionalSuppliedCompactification f)

/-- The actual chosen reflexive source comparison retains the native inverse-image identity
and the original independent-family comparison. -/
theorem moduleExceptionalDirectImagePlusSourceIsoOfNonempty_refl_normalized :
    @moduleExceptionalDirectImagePlusSourceIsoOfNonempty X X S f f _
        (Iso.refl X) (Category.id_comp f) Λ _ hX hX hS models₀ models₁ _ _ ≪≫
      Functor.isoWhiskerRight (@moduleDerivedInverseImageTorsionIdIso Λ _ X hX)
        ((@moduleExceptionalDirectImagePlusOfNonempty X S f _ Λ _ hX hS (models₁
          (moduleExceptionalSuppliedCompactification f)))) ≪≫
      Functor.leftUnitor _ =
    moduleExceptionalDirectImagePlusFamilyComparisonOfNonempty f Λ hX hS models₀ models₁ :=
  moduleCompactificationSourceIsoTo_refl f Λ hX hS models₀ models₁
    (moduleExceptionalSuppliedCompactification f)

/-- Without identifying independent families, source reflexivity is exactly the original
family comparison followed by the inverse native source-identity normalization. -/
theorem moduleExceptionalDirectImagePlusSourceIsoOfNonempty_refl :
    @moduleExceptionalDirectImagePlusSourceIsoOfNonempty X X S f f _
        (Iso.refl X) (Category.id_comp f) Λ _ hX hX hS models₀ models₁ _ _ =
      moduleExceptionalDirectImagePlusFamilyComparisonOfNonempty f Λ hX hS models₀ models₁ ≪≫
        (Functor.leftUnitor _).symm ≪≫
        Functor.isoWhiskerRight (@moduleDerivedInverseImageTorsionIdIso Λ _ X hX).symm
          ((@moduleExceptionalDirectImagePlusOfNonempty X S f _ Λ _ hX hS (models₁
            (moduleExceptionalSuppliedCompactification f)))) := by
  exact source_identity_denormalize _ _ _ _
    (moduleExceptionalDirectImagePlusSourceIsoOfNonempty_refl_normalized
      f Λ hX hS models₀ models₁)

/-- For the explicitly same middle family the actual comparison is the native identity
normalization alone; no independent model parameters have been identified silently. -/
theorem moduleExceptionalDirectImagePlusSourceIsoOfNonempty_refl_self :
    @moduleExceptionalDirectImagePlusSourceIsoOfNonempty X X S f f _
        (Iso.refl X) (Category.id_comp f) Λ _ hX hX hS models₀ models₀ _ _ =
      (Functor.leftUnitor _).symm ≪≫
        Functor.isoWhiskerRight (@moduleDerivedInverseImageTorsionIdIso Λ _ X hX).symm
          ((@moduleExceptionalDirectImagePlusOfNonempty X S f _ Λ _ hX hS (models₀
            (moduleExceptionalSuppliedCompactification f)))) := by
  have h := moduleExceptionalDirectImagePlusSourceIsoOfNonempty_refl f Λ hX hS models₀ models₀
  simp only [moduleExceptionalDirectImagePlusFamilyComparisonOfNonempty,
    moduleCompactificationFamilyComparison_self] at h
  erw [Iso.refl_trans] at h
  exact h

end AlgebraicGeometry.Scheme.EtaleCohomology
