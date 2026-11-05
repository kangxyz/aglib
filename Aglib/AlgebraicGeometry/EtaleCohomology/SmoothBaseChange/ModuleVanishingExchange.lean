/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.ModuleInjectiveAssembly
public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.OrdinaryCartesian

/-! # Actual smooth exchange from genuine module target vanishing

The original bounded ordinary smooth comparison supplies degree zero. The
complete exact-coefficient construction consumes positive-degree target
vanishing and returns the same canonical higher comparison on every actual
killed coefficient. The geometric positive-degree producer remains explicit.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u
attribute [local instance] hasSheafifyLarge hasSheafifyModules HasDerivedCategory.standard

/-- The original ordinary smooth theorem supplies the degree-zero input;
only genuine-injective positive target vanishing remains to be produced. -/
theorem higherBaseChangeMap_smooth_isIso_of_ringed_injective_vanishing
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (H : IsPullback g' f' f g) [Smooth g]
    (n : ℕ) (hn : 0 < n)
    (hvan : ∀ (q : ℕ) (I : ModuleSheaf X (ULift.{u + 1} (ZMod n))) [Injective I],
      IsZero ((higherDirectImage f' (q + 1)).obj ((inverseImage g').obj
        ((SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).obj I))))
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) (q : ℕ) :
    IsIso ((higherBaseChangeMap f f' g g' H.w.symm q).app F) := by
  refine higherBaseChangeMap_isIso_of_ringed_injective_vanishing
    f f' g g' H.w.symm n ?_ hvan F hF q
  intro M hM
  let : IsIso ((baseChangeMap f f' g g' H.w.symm).app M) :=
    baseChangeMap_smooth_bounded_isIso_of_isPullback f f' g g' H M n hn hM
  have hz := higherBaseChangeMap_zero f f' g g' H.w.symm M
  dsimp only [Functor.HigherExchangeZeroEquation] at hz
  apply (isIso_comp_right_iff _
    ((directImage f').rightDerivedZeroIsoSelf.hom.app ((inverseImage g').obj M))).mp
  rw [← hz]
  infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology
