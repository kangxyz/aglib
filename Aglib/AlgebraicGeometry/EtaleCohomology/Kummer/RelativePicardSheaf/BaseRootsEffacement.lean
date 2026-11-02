/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootsPullbackSquare

/-! # Actual family effacement of a base roots class

The original root cover on the raw base kills the base class, and its literal
pullback square kills the family pullback. There is no normalized Picard input,
resized presheaf, or choice of an iterated fibre-product model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u e

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

attribute [local instance] hasSheafifyLarge

set_option backward.isDefEq.respectTransparency false in
/-- The original pulled-back base class is killed by an internally constructed root cover. -/
theorem baseRoots_family_pointed_effacement {X S U : Scheme.{u}}
    (p : X ⟶ S) (t : U ⟶ S)
    [hAll : ∀ T : Scheme.{u}, HasExt.{e} (AbelianSheaf.{u, u + 1} T)]
    (n : ℕ) (hn : 0 < n) (hi : IsUnit (n : Γ(U, ⊤)))
    (b : Sheaf.H.{e} (mu U n) 1) (x : U) :
    ∃ (Y : Scheme.{u}) (a : Y ⟶ U) (_ : Etale a) (y : Y), a y = x ∧
      rootsCohomologyPullback
        (pullback.map p (a ≫ t) p t (𝟙 X) a (𝟙 S) (by simp) (by simp))
        n hn (levelInvertible (pullback.snd p t) n hi) 1
        (rootsCohomologyPullback (pullback.snd p t) n hn hi 1 b) = 0 := by
  obtain ⟨Y, a, ha, y, hy, hzero⟩ := exists_etale_rootsPullback_eq_zero U n hn hi b x
  refine ⟨Y, a, ha, y, hy, ?_⟩
  let g := pullback.map p (a ≫ t) p t (𝟙 X) a (𝟙 S) (by simp) (by simp)
  have hs : g ≫ pullback.snd p t = pullback.snd p (a ≫ t) ≫ a := by
    simp [g, pullback.map]
  have hsq := @rootsPullback_commutativeSquare U (pullback p t) Y
    (pullback p (a ≫ t)) (hAll U) (hAll (pullback p t)) (hAll Y)
    (hAll (pullback p (a ≫ t))) (pullback.snd p t) a g (pullback.snd p (a ≫ t))
    hs n hn hi b
  exact hsq.trans ((congrArg (@rootsCohomologyPullback Y (pullback p (a ≫ t))
    (hAll Y) (hAll (pullback p (a ≫ t))) (pullback.snd p (a ≫ t)) n hn
      (levelInvertible a n hi) 1) hzero).trans (map_zero _))

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
