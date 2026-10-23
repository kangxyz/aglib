/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.InjectiveSystem
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.Reindex

/-! # Compatible injectives over a specified inverse scheme diagram

A coefficient system is defined only over the specified diagram. No extension
to all schemes is assumed. The unrestricted index version exposes precisely
the necessary products; the coefficient-universe-small version obtains them
from the original abelian-sheaf category. The inverse-image transitions and
embedding squares are the mates under the original étale-image adjunctions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u uI vI

attribute [local instance] hasSheafifyLarge

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)

/-- Actual étale adjunctions restricted to the specified inverse scheme diagram. -/
abbrev diagramAdjunctionData := schemeAdjunctionData.reindex X

/-- The original comparisons remain coherent along the specified diagram. -/
theorem diagramAdjunctionData_coherent : (diagramAdjunctionData X).Coherent :=
  InjectiveSystem.AdjunctionData.Coherent.reindex _ X schemeAdjunctionData_coherent

/-- Coefficient systems on the specified diagram, with original direct-image
transition maps and their actual functor-law comparisons. -/
abbrev DiagramCoefficientSystem := InjectiveSystem.System (diagramAdjunctionData X)

/-- The actual inverse-image form of a system's transition. -/
def diagramInverseTransition (F : DiagramCoefficientSystem X) {i j : I} (a : i ⟶ j) :
    (inverseImage (X.map a).unop).obj (F.obj i) ⟶ F.obj j :=
  ((inverseImageAdjunction (X.map a).unop).homEquiv _ _).symm (F.map a)

/-- A morphism of systems also commutes with the original inverse-image
transitions, by the original adjunction rather than an unrelated comparison. -/
theorem diagramInverseTransition_naturality {F G : DiagramCoefficientSystem X}
    (η : InjectiveSystem.System.Hom (diagramAdjunctionData X) F G)
    {i j : I} (a : i ⟶ j) :
    (inverseImage (X.map a).unop).map (η.app i) ≫ diagramInverseTransition X G a =
      diagramInverseTransition X F a ≫ η.app j :=
  (inverseImageAdjunction (X.map a).unop).homEquiv_naturality_right_square
    (η.app i) (G.map a) (F.map a) (η.app j) (η.naturality a)

section Products

variable [∀ i j : I, HasProductsOfShape (InjectiveSystem.Outgoing j)
  (AbelianSheaf.{u, u + 1} (X.obj i).unop)]

/-- The compatible objectwise injective replacement on the specified diagram. -/
def diagramInjectiveReplacement (F : DiagramCoefficientSystem X) : DiagramCoefficientSystem X :=
  InjectiveSystem.replacement (diagramAdjunctionData X) (diagramAdjunctionData_coherent X) F

/-- The actual embedding into the compatible injective replacement. -/
def diagramInjectiveEmbedding (F : DiagramCoefficientSystem X) :
    InjectiveSystem.System.Hom (diagramAdjunctionData X) F (diagramInjectiveReplacement X F) :=
  InjectiveSystem.replacementEmbedding (diagramAdjunctionData X)
    (diagramAdjunctionData_coherent X) F

instance diagramInjectiveReplacement_injective (F : DiagramCoefficientSystem X) (i : I) :
    Injective ((diagramInjectiveReplacement X F).obj i) :=
  InjectiveSystem.replacement_obj_injective _ _ _ _

instance diagramInjectiveEmbedding_mono (F : DiagramCoefficientSystem X) (i : I) :
    Mono ((diagramInjectiveEmbedding X F).app i) :=
  InjectiveSystem.replacementEmbedding_mono _ _ _ _

end Products

section CoefficientSmall

variable {J : Type (u + 1)} [Category.{u + 1} J] (Y : J ⥤ Scheme.{u}ᵒᵖ)

/-- Coefficient-universe-small inverse diagrams require no extra product or
injectivity hypotheses: those are supplied by the original sheaf categories. -/
theorem exists_diagram_injective_system (F : DiagramCoefficientSystem Y) :
    ∃ (Q : DiagramCoefficientSystem Y)
      (η : InjectiveSystem.System.Hom (diagramAdjunctionData Y) F Q),
      (∀ j, Mono (η.app j)) ∧ (∀ j, Injective (Q.obj j)) :=
  ⟨diagramInjectiveReplacement Y F, diagramInjectiveEmbedding Y F,
    fun _ => inferInstance, fun _ => inferInstance⟩

end CoefficientSmall

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
