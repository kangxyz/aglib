/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.TwoIdeal.CoefficientSystem

/-! # Recovering each original formal stage as a completed coefficient quotient

Transposing the actual two-index diagram identifies the J-quotient of the
K-coefficient system with the K-completion of the original J-formal stage.
The comparison retains the original coefficient transitions in both indices.
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

local notation "J" => idealThickeningIdealSheaf f I
local notation "D" => twoIdealCoefficientDiagram I f K h F
local notation "E" => twoIdealCoefficientCompletionIso I f K h F

/-- The original nth formal coefficient, retaining its actual coherent sheaf. -/
def originalStageCoherent (n : ℕ) : X.CoherentSheaf :=
  ⟨F.obj.obj (op n), F.property.coherent n⟩

/-- Transposition of the actual diagram comparison, not a new choice of
isomorphisms at independent orders. -/
def twoIdealOriginalStageDiagramIso (n : ℕ) :
    (AdicSystem.quotient X K (J ^ n) (twoIdealCoefficientSystem I f K h F)).obj ≅
      ((completionFunctor X K).obj (originalStageCoherent I f F n)).obj :=
  NatIso.ofComponents
    (fun e => ((adicSystemToDiagram X J).mapIso ((E).app e)).app (op n)) (by
      intro e d g
      exact congrArg (fun z => z.hom.app (op n)) ((E).hom.naturality g))

/-- Completing each original stage in K recovers the original J-power
quotient of the genuine K-coefficient system. -/
def twoIdealOriginalStageIso (n : ℕ) :
    AdicSystem.quotient X K (J ^ n) (twoIdealCoefficientSystem I f K h F) ≅
      (completionFunctor X K).obj (originalStageCoherent I f F n) :=
  ObjectProperty.isoMk _ (twoIdealOriginalStageDiagramIso I f K h F n)

@[simp]
theorem twoIdealOriginalStageIso_hom_app (n e : ℕ) :
    (twoIdealOriginalStageIso I f K h F n).hom.hom.app (op e) =
      (((E).app (op e)).hom.hom.app (op n)) := rfl

end AlgebraicGeometry.Scheme.Cohomology
