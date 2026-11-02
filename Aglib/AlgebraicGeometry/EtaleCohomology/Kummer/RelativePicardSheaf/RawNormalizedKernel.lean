/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RelativePicardSheaf.BaseRootsEffacement

/-! # Pointed normalized-kernel effacement on the original raw family

The actual family remains `pullback p t`. Exactness constructs its base class;
the original base roots cover kills it. No small-site comma object is created.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u e

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open RelativePicard
attribute [local instance] hasSheafifyLarge

set_option backward.isDefEq.respectTransparency false in
/-- Actual normalized roots-kernel classes vanish on internally constructed raw refinements. -/
theorem normalizedRootsKernel_raw_pointed_effacement {X S U : Scheme.{u}}
    (p : X ⟶ S) [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]
    (o : S ⟶ X) (ho : o ≫ p = 𝟙 S) (t : U ⟶ S)
    [hAll : ∀ T : Scheme.{u}, HasExt.{e} (AbelianSheaf.{u, u + 1} T)]
    (n : ℕ) (hn : 0 < n) (hi : IsUnit (n : Γ(U, ⊤)))
    (c : Sheaf.H.{e} (mu (pullback p t) n) 1)
    (hc : rootsNormalizedPicardMap p o ho (Over.mk t) n hn
      (levelInvertible (pullback.snd p t) n hi) c = 0) (x : U) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ U) (_ : Etale a) (y : Y), a y = x ∧
      rootsCohomologyPullback
        (pullback.map p (a ≫ t) p t (𝟙 X) a (𝟙 S) (by simp) (by simp))
        n hn (levelInvertible (pullback.snd p t) n hi) 1 c = 0 := by
  obtain ⟨b, hb⟩ := (exact_rootsPullback_rootsNormalizedPicardMap p o ho
    (Over.mk t) n hn hi c).mp hc
  obtain ⟨Y, a, ha, y, hy, hzero⟩ := baseRoots_family_pointed_effacement
    p t n hn hi b x
  refine ⟨Y, a, ha, y, hy, ?_⟩
  let g := pullback.map p (a ≫ t) p t (𝟙 X) a (𝟙 S) (by simp) (by simp)
  exact (congrArg (@rootsCohomologyPullback (pullback p t) (pullback p (a ≫ t))
    (hAll (pullback p t)) (hAll (pullback p (a ≫ t))) g n hn
      (levelInvertible (pullback.snd p t) n hi) 1) hb.symm).trans hzero

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
