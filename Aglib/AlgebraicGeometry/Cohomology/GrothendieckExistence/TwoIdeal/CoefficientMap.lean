/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.TwoIdeal.CoefficientSystem
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.QuotientCompletionNaturality

/-! # The original two-ideal coefficient map to a fixed coherent target

The entire compatible map is lifted by full faithfulness at once. Its target
is the original coherent K-power quotient tower of the fixed algebraic sheaf.
-/

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
  {H : X.CoherentSheaf}

local notation "J" => idealThickeningIdealSheaf f I
local notation "C" => completionFunctor X J
local notation "D" => twoIdealCoefficientDiagram I f K h F

/-- Full faithfulness lifts the whole original formal quotient-map diagram,
so the algebraic maps to H/K^e commute with every original transition. -/
def twoIdealCoefficientMapDiagram (φ : F ⟶ (C).obj H) :
    D ⟶ idealSheafCoherentQuotientTower X K H :=
  ((completionFunctorFullyFaithful I f).whiskeringRight ℕᵒᵖ).preimage
    ((twoIdealCoefficientCompletionIso I f K h F).hom ≫
      AdicSystem.quotientTowerHom X J K φ ≫
      (idealSheafCoherentQuotientTowerCompletionIso X J K H).inv)

/-- Completing each lifted algebraic map gives exactly the original reduced
formal map with the specified coefficient comparisons. -/
theorem twoIdealCoefficientMapDiagram_completion (φ : F ⟶ (C).obj H) (n : ℕ) :
    (C).map ((twoIdealCoefficientMapDiagram I f K h F φ).app (op n)) =
      (twoIdealCoefficientCompletionIso I f K h F).hom.app (op n) ≫
        (AdicSystem.quotientFunctor X J (K ^ n)).map φ ≫
        (idealSheafQuotientCompletionIso X J (K ^ n) H).inv := by
  have hh := ((completionFunctorFullyFaithful I f).whiskeringRight ℕᵒᵖ).map_preimage
    ((twoIdealCoefficientCompletionIso I f K h F).hom ≫
      AdicSystem.quotientTowerHom X J K φ ≫
      (idealSheafCoherentQuotientTowerCompletionIso X J K H).inv)
  exact congrArg (fun η => η.app (op n)) hh

/-- The reconstructed coefficient K-system maps to the original K-completion
of the fixed coherent target, retaining the lifted original algebraic maps. -/
def twoIdealCoefficientMap (φ : F ⟶ (C).obj H) :
    twoIdealCoefficientSystem I f K h F ⟶ (completionFunctor X K).obj H :=
  ObjectProperty.homMk (Functor.whiskerRight
    (twoIdealCoefficientMapDiagram I f K h F φ)
    (QuasiCoherent.finiteTypeSheavesToModules X))

@[simp]
theorem twoIdealCoefficientMap_app (φ : F ⟶ (C).obj H) (n : ℕ) :
    (twoIdealCoefficientMap I f K h F φ).hom.app (op n) =
      ((twoIdealCoefficientMapDiagram I f K h F φ).app (op n)).hom := rfl

end AlgebraicGeometry.Scheme.Cohomology
