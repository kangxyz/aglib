/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Etale.Field

/-! # Differential bases above a separating rational function field

The basis is constructed by localization and separable formally-étale transport of
the native polynomial differential basis. Separability here is the algebraic
separability above the displayed rational function field, not general separability
of the original extension over the ground field.
-/

@[expose] public noncomputable section

open MvPolynomial TensorProduct

namespace KaehlerDifferential

variable (k : Type*) [Field k] (ι : Type*) (L K : Type*) [Field L] [Field K]
variable [Algebra (MvPolynomial ι k) L] [IsFractionRing (MvPolynomial ι k) L]
variable [Algebra k K] [Algebra (MvPolynomial ι k) K] [Algebra L K]
variable [IsScalarTower k (MvPolynomial ι k) K]
variable [IsScalarTower (MvPolynomial ι k) L K] [Algebra.IsSeparable L K]

include L in
/-- Differentials of the actual polynomial coordinates form a basis after passage
through a fraction field and an algebraic separable field extension. -/
theorem exists_basis_of_fractionRing_separable :
    ∃ b : Module.Basis ι K (KaehlerDifferential k K),
      ∀ i, b i = D k K (algebraMap (MvPolynomial ι k) K (X i)) := by
  let : Algebra.FormallyEtale (MvPolynomial ι k) L :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (MvPolynomial ι k))
  let : Algebra.FormallyEtale L K := Algebra.FormallyEtale.of_isSeparable L K
  let : Algebra.FormallyEtale (MvPolynomial ι k) K :=
    Algebra.FormallyEtale.comp (MvPolynomial ι k) L K
  let e := tensorKaehlerEquivOfFormallyEtale k (MvPolynomial ι k) K
  refine ⟨((mvPolynomialBasis k ι).baseChange K).map e, ?_⟩
  intro i
  simp only [Module.Basis.map_apply, Module.Basis.baseChange_apply,
    mvPolynomialBasis_apply, e, tensorKaehlerEquivOfFormallyEtale_apply,
    mapBaseChange_tmul, one_smul, map_D]

end KaehlerDifferential
