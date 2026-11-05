/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Pullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleBaseChange

/-! # Original ringed inverse image preserves native constructibility -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- Original ringed inverse image preserves the native constructible predicate. -/
theorem moduleIsConstructible_inverseImage
    (Λ : Type (u + 1)) [Ring Λ] {Y X : Scheme.{u}} (p : Y ⟶ X)
    (F : ModuleSheaf X Λ)
    (hF : Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence X Λ).inverse.obj F)) :
    Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence Y Λ).inverse.obj ((moduleInverseImage p Λ).obj F)) := by
  exact (Constructible.Modules.isConstructible_iff_of_iso
    ((moduleInverseImageValuedIso Λ p).app F)).mpr
      (Constructible.Modules.isConstructible_pullback (R := Λ) p hF)

end AlgebraicGeometry.Scheme.EtaleCohomology
