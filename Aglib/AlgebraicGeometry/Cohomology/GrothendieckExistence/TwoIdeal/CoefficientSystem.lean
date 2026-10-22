/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.TwoIdeal.CoefficientDiagram
public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.QuotientCompletionUnit

/-! # The algebraized independent quotients form an original adic system -/

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
local notation "C" => completionFunctor X J
local notation "E" => twoIdealCoefficientCompletionIso I f K h F

/-- The completed reduction is the composite of original quotient interchange,
the chosen whole-diagram comparison, and original nested quotient reduction. -/
def twoIdealCoefficientReductionCompletionIso (n : ℕ) :
    (C).obj (idealSheafCoherentQuotient X (K ^ n) ((D).obj (op (n + 1)))) ≅
      (C).obj ((D).obj (op n)) :=
  idealSheafQuotientCompletionIso X J (K ^ n) ((D).obj (op (n + 1))) ≪≫
    (AdicSystem.quotientFunctor X J (K ^ n)).mapIso ((E).app (op (n + 1))) ≪≫
    AdicSystem.quotientReductionIso X (K ^ (n + 1)) J
      (idealSheaf_pow_le X K (Nat.le_succ n)) F ≪≫
    ((E).app (op n)).symm

/-- Full faithfulness lifts the specified completed reduction, not an
unrelated choice of reduction equivalence. -/
def twoIdealCoefficientReductionIso (n : ℕ) :
    idealSheafCoherentQuotient X (K ^ n) ((D).obj (op (n + 1))) ≅ (D).obj (op n) :=
  (completionFunctorFullyFaithful I f).preimageIso
    (twoIdealCoefficientReductionCompletionIso I f K h F n)

set_option backward.isDefEq.respectTransparency false in
/-- The lifted algebraic reduction retains the original transition and
original quotient unit. This forces coherence of the algebraizations. -/
@[reassoc]
theorem twoIdealCoefficientUnit_reductionIso_hom (n : ℕ) :
    idealSheafCoherentQuotientUnit X (K ^ n) ((D).obj (op (n + 1))) ≫
      (twoIdealCoefficientReductionIso I f K h F n).hom =
      (D).map (homOfLE (Nat.le_succ n)).op := by
  let ff := completionFunctorFullyFaithful I f
  apply ff.map_injective
  rw [Functor.map_comp]
  change (C).map (idealSheafCoherentQuotientUnit X (K ^ n) ((D).obj (op (n + 1)))) ≫
    (C).map (ff.preimage (twoIdealCoefficientReductionCompletionIso I f K h F n).hom) = _
  rw [ff.map_preimage]
  change (C).map (idealSheafCoherentQuotientUnit X (K ^ n) ((D).obj (op (n + 1)))) ≫
      (idealSheafQuotientCompletionIso X J (K ^ n) ((D).obj (op (n + 1)))).hom ≫
      (AdicSystem.quotientFunctor X J (K ^ n)).map ((E).app (op (n + 1))).hom ≫
      (AdicSystem.quotientReductionIso X (K ^ (n + 1)) J
        (idealSheaf_pow_le X K (Nat.le_succ n)) F).hom ≫
      ((E).app (op n)).inv = _
  rw [completionQuotientUnit_interchange_assoc]
  have hu :
      ((E).app (op (n + 1))).hom ≫
          AdicSystem.quotientUnit X J (K ^ n)
            (AdicSystem.quotient X J (K ^ (n + 1)) F) =
        AdicSystem.quotientUnit X J (K ^ n) ((C).obj ((D).obj (op (n + 1)))) ≫
          (AdicSystem.quotientFunctor X J (K ^ n)).map ((E).app (op (n + 1))).hom := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext m
    exact (idealSheafQuotientUnit X (K ^ n)).naturality
      (((E).app (op (n + 1))).hom.hom.app m)
  rw [← Category.assoc, ← hu, Category.assoc,
    AdicSystem.quotientUnit_reductionIso_hom_assoc]
  have hn := (E).hom.naturality (homOfLE (Nat.le_succ n)).op
  change (C).map ((D).map (homOfLE (Nat.le_succ n)).op) ≫ ((E).app (op n)).hom =
    ((E).app (op (n + 1))).hom ≫
      AdicSystem.quotientMap X J (K ^ (n + 1))
        (idealSheaf_pow_le X K (Nat.le_succ n)) F at hn
  rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The actual coherent algebraizations and actual lifted transitions satisfy
all original K-adic conditions, including the zero stage. -/
theorem twoIdealCoefficient_isAdicSystem :
    IsAdicSystem X K (D ⋙ QuasiCoherent.finiteTypeSheavesToModules X) where
  coherent n := ((D).obj (op n)).property
  annihilated n := twoIdealCoefficient_killed I f K h F n
  reduction n := ⟨(QuasiCoherent.finiteTypeSheavesToModules X).mapIso
    (twoIdealCoefficientReductionIso I f K h F n), by
      exact congrArg (fun g => g.hom) (twoIdealCoefficientUnit_reductionIso_hom I f K h F n)⟩

/-- The genuine independent-ideal formal system needed for same-ideal
reconstruction. The thickening-effectivity hypothesis remains explicit. -/
def twoIdealCoefficientSystem : AdicSystem X K :=
  ⟨D ⋙ QuasiCoherent.finiteTypeSheavesToModules X,
    twoIdealCoefficient_isAdicSystem I f K h F⟩

end AlgebraicGeometry.Scheme.Cohomology
