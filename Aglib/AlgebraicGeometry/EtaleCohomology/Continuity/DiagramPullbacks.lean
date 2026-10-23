/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramInjectives
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.InverseTransitions

/-! # Native inverse-image transitions on a specified inverse scheme diagram

The identity and composition comparisons retain the indexing functor's equality
transports and the original étale inverse-image isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u uI vI
attribute [local instance] hasSheafifyLarge

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)

/-- The original identity inverse-image comparison with the indexing functor transport. -/
def diagramInverseImageId (i : I) :
    inverseImage (X.map (𝟙 i)).unop ≅ 𝟭 (AbelianSheaf.{u, u + 1} (X.obj i).unop) := by
  let e : inverseImage (X.map (𝟙 i)).unop ≅ inverseImage (𝟙 (X.obj i).unop) :=
    eqToIso (congrArg
      (fun f : X.obj i ⟶ X.obj i => inverseImage f.unop) (X.map_id i))
  exact e ≪≫ inverseImageId (X.obj i).unop

/-- The original composition inverse-image comparison with the indexing functor transport. -/
def diagramInverseImageComp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    inverseImage (X.map (a ≫ b)).unop ≅
      inverseImage (X.map a).unop ⋙ inverseImage (X.map b).unop := by
  let e : inverseImage (X.map (a ≫ b)).unop ≅
      inverseImage ((X.map b).unop ≫ (X.map a).unop) :=
    eqToIso (congrArg
      (fun f : X.obj i ⟶ X.obj k => inverseImage f.unop) (X.map_comp a b))
  exact e ≪≫ inverseImageComp (X.map a).unop (X.map b).unop

/-- The specified identity comparison is the mate of the actual right comparison. -/
lemma diagramInverseImageId_mate (i : I) :
    conjugateEquiv Adjunction.id (inverseImageAdjunction (X.map (𝟙 i)).unop)
      (diagramInverseImageId X i).hom =
        ((diagramAdjunctionData X).idIso i).inv := by
  dsimp only [diagramInverseImageId, Iso.trans_hom]
  rw [← conjugateEquiv_comp Adjunction.id
    (inverseImageAdjunction (𝟙 (X.obj i).unop))
    (inverseImageAdjunction (X.map (𝟙 i)).unop), conjugateEquiv_inverseImageId_hom]
  exact congrArg
    (fun τ : directImage (𝟙 (X.obj i).unop) ⟶ directImage (X.map (𝟙 i)).unop =>
      (directImageIdIso (X.obj i).unop).inv ≫ τ)
    (conjugateEquiv_inverseImage_eqToHom
      (congrArg (fun f : X.obj i ⟶ X.obj i => f.unop) (X.map_id i)))

/-- The specified composition comparison is the mate of the actual right comparison. -/
lemma diagramInverseImageComp_mate {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    conjugateEquiv ((inverseImageAdjunction (X.map a).unop).comp
      (inverseImageAdjunction (X.map b).unop))
      (inverseImageAdjunction (X.map (a ≫ b)).unop)
      (diagramInverseImageComp X a b).hom =
        ((diagramAdjunctionData X).compIso a b).inv := by
  dsimp only [diagramInverseImageComp, Iso.trans_hom]
  rw [← conjugateEquiv_comp
    ((inverseImageAdjunction (X.map a).unop).comp (inverseImageAdjunction (X.map b).unop))
    (inverseImageAdjunction ((X.map b).unop ≫ (X.map a).unop))
    (inverseImageAdjunction (X.map (a ≫ b)).unop), conjugateEquiv_inverseImageComp_hom]
  exact congrArg
    (fun τ : directImage ((X.map b).unop ≫ (X.map a).unop) ⟶
        directImage (X.map (a ≫ b)).unop =>
      (directImageCompIso (X.map a).unop (X.map b).unop).hom ≫ τ)
    (conjugateEquiv_inverseImage_eqToHom
      (congrArg (fun f : X.obj i ⟶ X.obj k => f.unop) (X.map_comp a b)))

/-- Canonical adjunction comparison equals the specified original identity comparison. -/
lemma leftIdIso_eq_diagramInverseImageId (i : I) :
    (diagramAdjunctionData X).leftIdIso i = diagramInverseImageId X i := by
  apply Iso.ext
  apply (conjugateEquiv Adjunction.id
    (inverseImageAdjunction (X.map (𝟙 i)).unop)).injective
  exact (Adjunction.conjugateEquiv_leftAdjointIdIso_hom _ _).trans
    (diagramInverseImageId_mate X i).symm

/-- Canonical adjunction comparison equals the specified original composition comparison. -/
lemma leftCompIso_eq_diagramInverseImageComp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    (diagramAdjunctionData X).leftCompIso a b = diagramInverseImageComp X a b := by
  apply Iso.ext
  apply (conjugateEquiv ((inverseImageAdjunction (X.map a).unop).comp
      (inverseImageAdjunction (X.map b).unop))
    (inverseImageAdjunction (X.map (a ≫ b)).unop)).injective
  exact (Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _).trans
    (diagramInverseImageComp_mate X a b).symm

/-- The given compatible system obeys the original inverse-image identity law. -/
lemma diagramInverseTransition_id (F : DiagramCoefficientSystem X) (i : I) :
    diagramInverseTransition X F (𝟙 i) = (diagramInverseImageId X i).hom.app (F.obj i) := by
  change F.leftMap (diagramAdjunctionData X) (𝟙 i) = _
  rw [InjectiveSystem.System.leftMap_id, leftIdIso_eq_diagramInverseImageId]

/-- The given compatible system obeys the original inverse-image composition law. -/
lemma diagramInverseTransition_comp (F : DiagramCoefficientSystem X)
    {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    diagramInverseTransition X F (a ≫ b) =
      (diagramInverseImageComp X a b).hom.app (F.obj i) ≫
        (inverseImage (X.map b).unop).map (diagramInverseTransition X F a) ≫
          diagramInverseTransition X F b := by
  change F.leftMap (diagramAdjunctionData X) (a ≫ b) = _
  rw [InjectiveSystem.System.leftMap_comp, leftCompIso_eq_diagramInverseImageComp]
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
