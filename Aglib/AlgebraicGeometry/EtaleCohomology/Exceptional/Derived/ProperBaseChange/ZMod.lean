/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.ProperBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.TorsionRange

/-! Proper base change for the original finite-coefficient derived module categories. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

open Coefficients

universe u wX wS wX' wS'

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable (n : ℕ) (hn : 0 < n) {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wS} (ModuleSheaf S (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' (ULift.{u + 1} (ZMod n)))]
  [HasDerivedCategory.{wS'} (ModuleSheaf S' (ULift.{u + 1} (ZMod n)))]
  (f : X ⟶ S) [IsProper f] (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (sq : IsPullback g' f' f g)

include hn

/-- Proper base change for any original bounded-below complex of finite-level modules. -/
theorem properModuleDerivedBaseChange_isIso_zmod
    (K : DerivedCategory.Plus (ModuleSheaf X (ULift.{u + 1} (ZMod n)))) :
    IsIso ((moduleDerivedBaseChangeMap (ULift.{u + 1} (ZMod n)) f f' g g' sq.w.symm).app K) := by
  let Λ := ULift.{u + 1} (ZMod n)
  have hΛ : n • (1 : Λ) = 0 := by
    apply ULift.ext
    exact ZModModule.char_nsmul_eq_zero n (1 : ZMod n)
  exact properModuleDerivedBaseChange_isIso_of_torsion_homology Λ f f' g g' sq K
    (moduleTorsionCohomology_of_nsmul_one_eq_zero X Λ n hn hΛ (DerivedCategory.Plus.ι.obj K))

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
