/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.ModuleInjectiveTests
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.SingleHigher
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.ZModRetract
public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.AllModuleCoefficients

/-! # Original all-coefficient exchange from genuine module injective vanishing

The complete exact-coefficient construction consumes degree-zero exchange and
positive target vanishing on genuine ringed injectives. It retains the original
canonical derived exchange and its original higher components, using the
existing all-module-coefficient comparison. No forgotten injectivity or new
coefficient resolution is assumed. The geometric vanishing input is explicit.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients Proper.Reduction
section TypedTests
variable {A B C M : Type*} [Category* A] [Category* B] [Category* C] [Category* M]
  {L R : B ⥤ C}

private theorem comparison_of_original_single_tests
    (single : A ⥤ B) (U : M ⥤ A) (Z : M ⥤ B) (e : Z = U ⋙ single)
    (β : L ⟶ R) (P : ℕ → A → Prop)
    (h : ∀ F, IsIso (β.app (single.obj F)) ↔ ∀ q, P q F)
    (I : M) (hI : ∀ q, P q (U.obj I)) : IsIso (β.app (Z.obj I)) := by
  subst Z
  exact (h _).mpr hI
end TypedTests

universe u dX dS dX' dS'
attribute [local instance] hasSheafifyLarge hasSheafifyModules
  moduleForget_preservesSheafification TorsionZMod.hasSheafifyStandard

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]

/-- Complete genuine-injective comparison, before all-coefficient specialization. -/
theorem derivedBaseChangeMap_zmodInjective_isIso_of_ringed_vanishing
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (n : ℕ)
    (hzero : ∀ F : AbelianSheaf.{u, u + 1} X, n • 𝟙 F = 0 →
      IsIso ((higherBaseChangeMap f f' g g' h 0).app F))
    (hvan : ∀ (q : ℕ) (I : ModuleSheaf X (ULift.{u + 1} (ZMod n))) [Injective I],
      IsZero ((higherDirectImage f' (q + 1)).obj ((inverseImage g').obj
        ((SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).obj I))))
    (I : ZModSheaf X n) [Injective I] :
    IsIso ((derivedBaseChangeMap f f' g g' h).app ((zmodSingle X n).obj I)) := by
  apply comparison_of_original_single_tests
    (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0)
    (zmodUnderlying X n) (zmodSingle X n) rfl
    (derivedBaseChangeMap f f' g g' h)
    (fun q F => IsIso ((higherBaseChangeMap f f' g g' h q).app F))
    (derivedBaseChangeMap_single_isIso_iff_higher f f' g g' h) I
  intro r
  cases r with
  | zero => exact hzero _ (zmodUnderlying_nsmul_id X n I)
  | succ r =>
    exact higherBaseChangeMap_zmodInjective_isIso_of_ringed_target_vanishing
      f f' g g' h n r (hvan r) I

/-- Genuine ringed-injective target vanishing and the original degree-zero
comparison supply every higher comparison on every actual n-killed coefficient. -/
theorem higherBaseChangeMap_isIso_of_ringed_injective_vanishing
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (n : ℕ)
    (hzero : ∀ F : AbelianSheaf.{u, u + 1} X, n • 𝟙 F = 0 →
      IsIso ((higherBaseChangeMap f f' g g' h 0).app F))
    (hvan : ∀ (q : ℕ) (I : ModuleSheaf X (ULift.{u + 1} (ZMod n))) [Injective I],
      IsZero ((higherDirectImage f' (q + 1)).obj ((inverseImage g').obj
        ((SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).obj I))))
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) (q : ℕ) :
    IsIso ((higherBaseChangeMap f f' g g' h q).app F) := by
  exact higherExchange_on_killedCoefficients f f' g g' h n
    (fun I _ => derivedBaseChangeMap_zmodInjective_isIso_of_ringed_vanishing
      f f' g g' h n hzero hvan I) F hF q

end AlgebraicGeometry.Scheme.EtaleCohomology
