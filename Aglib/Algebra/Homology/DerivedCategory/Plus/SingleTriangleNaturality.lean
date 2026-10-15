/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.SingleTriangle

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/ProjectiveLine/DiagonalGenerationNaturality.lean` at
LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: cut_general;
source ranges [[34, 78], [88, 95]]. Actual objects, maps and hypotheses are preserved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
    {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂)

/-- The map of bounded-below single triangles induced by a morphism of short exact sequences. -/
def singleTrianglePlusMap : h₁.singleTrianglePlus ⟶ h₂.singleTrianglePlus :=
  DerivedCategory.Plus.ι.mapTriangle.preimage
    (h₁.singleTrianglePlusιIso.hom ≫ singleTriangle.map h₁ h₂ f ≫
      h₂.singleTrianglePlusιIso.inv)

@[simp] theorem singleTrianglePlusMap_hom₁ :
    (singleTrianglePlusMap h₁ h₂ f).hom₁ =
      (DerivedCategory.Plus.singleFunctor C 0).map f.τ₁ := by
  apply DerivedCategory.Plus.ι.map_injective
  have h := congrArg TriangleMorphism.hom₁
    (DerivedCategory.Plus.ι.mapTriangle.map_preimage
      (h₁.singleTrianglePlusιIso.hom ≫ singleTriangle.map h₁ h₂ f ≫
        h₂.singleTrianglePlusιIso.inv))
  refine h.trans ?_
  dsimp [singleTrianglePlusιIso]
  simp only [Category.id_comp]
  change (DerivedCategory.singleFunctor C 0).map f.τ₁ ≫ 𝟙 _ = (DerivedCategory.singleFunctor
      C 0).map f.τ₁
  exact Category.comp_id _

@[simp] theorem singleTrianglePlusMap_hom₂ :
    (singleTrianglePlusMap h₁ h₂ f).hom₂ =
      (DerivedCategory.Plus.singleFunctor C 0).map f.τ₂ := by
  apply DerivedCategory.Plus.ι.map_injective
  have h := congrArg TriangleMorphism.hom₂
    (DerivedCategory.Plus.ι.mapTriangle.map_preimage
      (h₁.singleTrianglePlusιIso.hom ≫ singleTriangle.map h₁ h₂ f ≫
        h₂.singleTrianglePlusιIso.inv))
  refine h.trans ?_
  dsimp [singleTrianglePlusιIso]
  simp only [Category.id_comp]
  change (DerivedCategory.singleFunctor C 0).map f.τ₂ ≫ 𝟙 _ = (DerivedCategory.singleFunctor
      C 0).map f.τ₂
  exact Category.comp_id _

@[simp] theorem singleTrianglePlusMap_hom₃ :
    (singleTrianglePlusMap h₁ h₂ f).hom₃ =
      (DerivedCategory.Plus.singleFunctor C 0).map f.τ₃ := by
  apply DerivedCategory.Plus.ι.map_injective
  have h := congrArg TriangleMorphism.hom₃
    (DerivedCategory.Plus.ι.mapTriangle.map_preimage
      (h₁.singleTrianglePlusιIso.hom ≫ singleTriangle.map h₁ h₂ f ≫
        h₂.singleTrianglePlusιIso.inv))
  refine h.trans ?_
  dsimp [singleTrianglePlusιIso]
  simp only [Category.id_comp]
  change (DerivedCategory.singleFunctor C 0).map f.τ₃ ≫ 𝟙 _ = (DerivedCategory.singleFunctor
      C 0).map f.τ₃
  exact Category.comp_id _

end CategoryTheory.ShortComplex.ShortExact
