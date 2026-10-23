/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramSectionTransfers
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.InverseNaturality

/-! # Original section naturality for morphisms of compatible systems -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge

lemma sectionTransfer_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    {F F' : AbelianSheaf.{u, u + 1} X} {G G' : AbelianSheaf.{u, u + 1} Y}
    (φ : (inverseImage f).obj F ⟶ G) (ψ : (inverseImage f).obj F' ⟶ G')
    (a : F ⟶ F') (b : G ⟶ G') (h : (inverseImage f).map a ≫ ψ = φ ≫ b) :
    sectionTransfer f φ ≫ (globalSections Y).map b =
      (globalSections X).map a ≫ sectionTransfer f ψ := by
  dsimp only [sectionTransfer]
  rw [Category.assoc, ← Functor.map_comp, ← h, Functor.map_comp,
    ← Category.assoc, ← globalSectionsPullback_naturality, Category.assoc]

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  {F G : DiagramCoefficientSystem X}
  (η : InjectiveSystem.System.Hom (diagramAdjunctionData X) F G)

/-- The actual component maps on the original source section diagrams. -/
def diagramSectionsNatTrans : diagramSectionsFunctor X F ⟶ diagramSectionsFunctor X G where
  app i := (globalSections (X.obj i).unop).map (η.app i)
  naturality _ _ a := sectionTransfer_naturality (X.map a).unop
    (diagramInverseTransition X F a) (diagramInverseTransition X G a)
    (η.app _) (η.app _) (diagramInverseTransition_naturality X η a)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
