/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramSquareSections

/-! # Equality transport for the original coefficient square -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u
attribute [local instance] hasSheafifyLarge

/-- Reindexing both horizontal arrows retains the original coefficient-square map. -/
lemma squareCoefficientMap_transport {X₀ S₀ X₁ S₁ : Scheme.{u}}
    (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (g g' : S₁ ⟶ S₀) (h h' : X₁ ⟶ X₀)
    (eg : g' = g) (eh : h' = h)
    (e : f₁ ≫ g = h ≫ f₀) (e' : f₁ ≫ g' = h' ≫ f₀)
    {F : AbelianSheaf.{u, u + 1} S₀} {G : AbelianSheaf.{u, u + 1} S₁}
    (φ : (inverseImage g).obj F ⟶ G) :
    squareCoefficientMap f₀ f₁ g' h' e'
      (eqToHom (congrArg (fun k : S₁ ⟶ S₀ => (inverseImage k).obj F) eg) ≫ φ) =
        eqToHom (congrArg
          (fun k : X₁ ⟶ X₀ => (inverseImage k).obj ((inverseImage f₀).obj F)) eh) ≫
          squareCoefficientMap f₀ f₁ g h e φ := by
  simpa only [schemeSquareCoefficientMap_eq_squareCoefficientMap, schemeLeft_eq_inverseImage,
    Quiver.Hom.unop_op] using
    schemeAdjunctionData.squareCoefficientMap_transport f₀.op f₁.op g.op g'.op h.op h'.op
      (congrArg Quiver.Hom.op eg) (congrArg Quiver.Hom.op eh)
      (congrArg Quiver.Hom.op e) (congrArg Quiver.Hom.op e') φ

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
