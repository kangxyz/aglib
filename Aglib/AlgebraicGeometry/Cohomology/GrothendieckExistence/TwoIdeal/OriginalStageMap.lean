/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.TwoIdeal.OriginalStageComparison
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.TwoIdeal.CoefficientMap

/-! # Original-stage comparisons retain the algebraic target map -/

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
  (F : AdicSystem X (idealThickeningIdealSheaf f I)) {H : X.CoherentSheaf}

local notation "J" => idealThickeningIdealSheaf f I
local notation "C" => completionFunctor X J
local notation "E" => twoIdealCoefficientCompletionIso I f K h F

/-- The original nth coefficient of the map to the completed algebraic target. -/
def originalStageCoherentMap (φ : F ⟶ (C).obj H) (n : ℕ) :
    originalStageCoherent I f F n ⟶ idealSheafCoherentQuotient X (J ^ n) H :=
  ObjectProperty.homMk (φ.hom.app (op n))

/-- The transposed comparison respects the actual maps to the quotient of H.
This is the specified square required for bounded reconstruction uniqueness. -/
theorem twoIdealOriginalStageIso_map (φ : F ⟶ (C).obj H) (n : ℕ) :
    (AdicSystem.quotientFunctor X K (J ^ n)).map
        (twoIdealCoefficientMap I f K h F φ) ≫
      (idealSheafQuotientCompletionIso X K (J ^ n) H).inv =
    (twoIdealOriginalStageIso I f K h F n).hom ≫
      (completionFunctor X K).map (originalStageCoherentMap I f F φ n) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext e
  let a := (twoIdealCoefficientMapDiagram I f K h F φ).app e
  let c := idealSheafQuotientInterchangeIso X (K ^ e.unop) (J ^ n) H.obj
  have hh : (idealSheafQuotientFunctor X (J ^ n)).map a.hom =
      ((E).app e).hom.hom.app (op n) ≫
        (idealSheafQuotientFunctor X (K ^ e.unop)).map (φ.hom.app (op n)) ≫ c.inv :=
    congrArg (fun z => z.hom.app (op n))
      (twoIdealCoefficientMapDiagram_completion I f K h F φ e.unop)
  change (idealSheafQuotientFunctor X (J ^ n)).map a.hom ≫ c.hom =
    ((E).app e).hom.hom.app (op n) ≫
      (idealSheafQuotientFunctor X (K ^ e.unop)).map (φ.hom.app (op n))
  exact (Iso.eq_comp_inv c).mp (hh.trans (Category.assoc _ _ _).symm)

end AlgebraicGeometry.Scheme.Cohomology
