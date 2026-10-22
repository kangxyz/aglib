/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.TwoIdeal.OriginalStageComparison

/-! # Original transitions in the transposed two-ideal comparison -/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (K : X.IdealSheafData)
  (h : ClosedThickeningCompletionEssSurj f I K)
  (F : AdicSystem X (idealThickeningIdealSheaf f I))

local notation "J" => idealThickeningIdealSheaf f I

/-- The original transition as a morphism of its actual coherent coefficients. -/
def originalStageCoherentTransition (n : ℕ) :
    originalStageCoherent I f F (n + 1) ⟶ originalStageCoherent I f F n :=
  ObjectProperty.homMk (F.transition n)

/-- Transposing the original diagram retains the original I-adic transition.
This is the compatibility used when uniqueness recovers the whole I-system. -/
theorem twoIdealOriginalStageIso_transition (n : ℕ) :
    AdicSystem.quotientMap X K (J ^ (n + 1))
        (idealSheaf_pow_le X J (Nat.le_succ n)) (twoIdealCoefficientSystem I f K h F) ≫
      (twoIdealOriginalStageIso I f K h F n).hom =
    (twoIdealOriginalStageIso I f K h F (n + 1)).hom ≫
      (completionFunctor X K).map (originalStageCoherentTransition I f F n) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext e
  exact ((twoIdealCoefficientCompletionIso I f K h F).app e).hom.hom.naturality
    (homOfLE (Nat.le_succ n)).op

end AlgebraicGeometry.Scheme.Cohomology
