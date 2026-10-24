/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleComparisons
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Native module pullback along a scheme isomorphism -/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable (Λ : Type (u + 1)) [Ring Λ] {X Y : Scheme.{u}} (e : X ≅ Y)

/-- Native pullback along an actual scheme isomorphism is an equivalence. -/
def moduleInverseImageEquivalence : ModuleSheaf Y Λ ≌ ModuleSheaf X Λ :=
  CategoryTheory.Equivalence.mk (moduleInverseImage e.hom Λ) (moduleInverseImage e.inv Λ)
    ((moduleInverseImageIdIso Λ Y).symm ≪≫
      eqToIso (congrArg (fun a => moduleInverseImage a Λ) e.inv_hom_id.symm) ≪≫
      moduleInverseImageCompIso Λ e.hom e.inv)
    ((moduleInverseImageCompIso Λ e.inv e.hom).symm ≪≫
      eqToIso (congrArg (fun a => moduleInverseImage a Λ) e.hom_inv_id) ≪≫
      moduleInverseImageIdIso Λ X)

instance moduleInverseImage_isEquivalence_of_iso :
    (moduleInverseImage e.hom Λ).IsEquivalence :=
  (moduleInverseImageEquivalence Λ e).isEquivalence_functor

/-- The original native pullback unit is invertible along a scheme isomorphism. -/
def moduleInverseImageUnitIsoOfIso :
    𝟭 (ModuleSheaf Y Λ) ≅ moduleInverseImage e.hom Λ ⋙ moduleDirectImage e.hom Λ :=
  asIso (moduleInverseImageAdjunction e.hom Λ).unit

end AlgebraicGeometry.Scheme.EtaleCohomology
