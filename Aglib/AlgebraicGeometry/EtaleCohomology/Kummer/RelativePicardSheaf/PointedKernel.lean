/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RelativePicardSheaf.RawNormalizedKernel

/-! # Pointed effacement for the original normalized family roots kernel

Exactness constructs the base cohomology class. The existing original root
cover kills that class, and the original family square kills its pullback.
No resized presheaf, Picard representative or effacement certificate is input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe u e

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open RelativePicard
attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (p : X ⟶ S)
    [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]
    (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)
    [hAll : ∀ Y : Scheme.{u}, HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]

/-- A normalized family roots-kernel class vanishes on a real pointed étale refinement. -/
theorem normalizedRootsKernel_pointed_effacement (U : S.Etale)
    (n : ℕ) (hn : 0 < n) (hi : IsUnit (n : Γ(U.left, ⊤)))
    (c : Sheaf.H.{e} (mu (pullback p U.hom) n) 1)
    (hc : rootsNormalizedPicardMap p o ho ((Scheme.Etale.forget S).obj U) n hn
      (levelInvertible (pullback.snd p U.hom) n hi) c = 0) (x : U.left) :
    ∃ (V : S.Etale) (v : V ⟶ U) (y : V.left), v.left y = x ∧
      rootsCohomologyPullback ((familyScheme p).map ((Scheme.Etale.forget S).map v))
        n hn (levelInvertible (pullback.snd p U.hom) n hi) 1 c = 0 := by
  obtain ⟨Y, a, ha, y, hy, hzero⟩ := normalizedRootsKernel_raw_pointed_effacement
    p o ho U.hom n hn hi c hc x
  let : Etale a := ha
  let V : S.Etale := Scheme.Etale.mk (a ≫ U.hom)
  let v : V ⟶ U := MorphismProperty.Over.homMk a rfl (by trivial)
  exact ⟨V, v, y, hy, hzero⟩


end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
