/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.TwoIdeal.CoefficientMap
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.IndependentFormalQuotientDefects
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ClosedImmersionReduction.KernelAnnihilation
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.ClosedImmersionReduction.CokernelAnnihilation

/-! # Uniform bounds on the actual algebraized coefficient system

The independent quotient doubles the exponent once. Proper completion then
reflects each ordinary defect bound unchanged, using the original maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
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

/-- The genuine K-adic coefficient map has one uniform bound on its ordinary
algebraic defects. The input is actual GE on each closed K-power thickening. -/
theorem twoIdealCoefficientMap_defectsKilled (φ : F ⟶ (C).obj H) (t : ℕ)
    (hφ : AdicSystem.DefectsKilled K t φ) :
    AdicSystem.DefectsKilled K (t * 2) (twoIdealCoefficientMap I f K h F φ) := by
  intro n
  let a := (twoIdealCoefficientMapDiagram I f K h F φ).app (op n)
  have ha : AdicSystem.DefectsKilled K (t * 2) ((C).map a) := by
    apply (hφ.quotient (K ^ n)).of_iso_square
      ((twoIdealCoefficientCompletionIso I f K h F).app (op n))
      (idealSheafQuotientCompletionIso X J (K ^ n) H)
    exact (Iso.eq_comp_inv (idealSheafQuotientCompletionIso X J (K ^ n) H)).mp
      ((twoIdealCoefficientMapDiagram_completion I f K h F φ n).trans
        (Category.assoc _ _ _).symm)
  exact ⟨killedByIdealSheaf_kernel_of_completion I f (K ^ (t * 2)) a
      (fun m => (ha m).1),
    killedByIdealSheaf_cokernel_of_completion I f (K ^ (t * 2)) a
      (fun m => (ha m).2)⟩

end AlgebraicGeometry.Scheme.Cohomology
