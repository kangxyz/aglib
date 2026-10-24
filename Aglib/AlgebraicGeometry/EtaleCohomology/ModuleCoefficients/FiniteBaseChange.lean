/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.ModuleCoefficients.BaseChangeMap
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.OrdinaryBaseChange

/-! # Original finite base change for constant-ring module sheaves

The literal native module exchange becomes the original abelian exchange under
scalar forgetting. Reflecting its invertibility proves ordinary finite base
change, without finite presentation, torsion or Noetherian hypotheses.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

private theorem isIso_of_underlying_comparison
    {C D : Type*} [Category* C] [Category* D]
    (U : C ⥤ D) [U.ReflectsIsomorphisms]
    {A B : C} {A' B' : D} (f : A ⟶ B) (g : A' ⟶ B') [IsIso g]
    (s : U.obj A ≅ A') (t : U.obj B ≅ B')
    (h : U.map f ≫ t.hom = s.hom ≫ g) : IsIso f := by
  have hi : IsIso (U.map f ≫ t.hom) := by
    rw [h]
    infer_instance
  have : IsIso (U.map f) := (isIso_comp_right_iff (U.map f) t.hom).mp hi
  exact isIso_of_reflects_iso f U

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

open Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R] {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  [IsFinite f] (h : IsPullback g' f' f g)

/-- Finite ordinary base change for the original module exchange and arbitrary
constant-ring module coefficients on arbitrary base schemes. -/
theorem finiteModuleBaseChange_app_isIso (F : ModuleSheaf R X) :
    IsIso ((moduleBaseChangeMap R f f' g g' h.w.symm).app F) := by
  have := finiteBaseChange_app_isIso f f' g g' h ((moduleUnderlying R X).obj F)
  exact isIso_of_underlying_comparison (moduleUnderlying R S')
    ((moduleBaseChangeMap R f f' g g' h.w.symm).app F)
    ((baseChangeMap f f' g g' h.w.symm).app ((moduleUnderlying R X).obj F))
    ((moduleBaseChangeSourceUnderlyingIso R f g).app F)
    ((moduleBaseChangeTargetUnderlyingIso R f' g').app F)
    (moduleBaseChangeMap_underlying_app R f f' g g' h.w.symm F)

/-- The entire original module exchange is invertible for every finite morphism. -/
theorem finiteModuleBaseChange_isIso :
    IsIso (moduleBaseChangeMap R f f' g g' h.w.symm) := by
  have (F : ModuleSheaf R X) :
      IsIso ((moduleBaseChangeMap R f f' g g' h.w.symm).app F) :=
    finiteModuleBaseChange_app_isIso R f f' g g' h F
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
