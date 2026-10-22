/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.ParameterLocalization
public import Aglib.RingTheory.Extension.Generators.Parameters
public import Mathlib.RingTheory.Localization.BaseChange

/-! # The actual chart after projecting parameter coordinates

The source has its genuine polynomial parameter action. Absorbing those coordinates
before native base change gives a finite generating family over the parameter DVR,
without claiming that prime localization is finite type over the old coefficient ring.
-/

@[expose] public noncomputable section

open MvPolynomial
open scoped TensorProduct

namespace ParameterLocalization

variable {R A α β : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing A] [Algebra R A] [Algebra (MvPolynomial α R) A]
  [IsScalarTower R (MvPolynomial α R) A]
variable (p : R) [Fact (Irreducible p)]

/-- The literal tensor chart over the actual second parameter localization. -/
abbrev Chart := Ring R α p ⊗[MvPolynomial α R] A

/-- The actual retained generators are obtained by absorption and native base change. -/
def chartGenerators (P : Algebra.Generators R A (β ⊕ α))
    (ha : ∀ i, algebraMap (MvPolynomial α R) A (X i) = P.val (.inr i)) :
    Algebra.Generators (Ring R α p) (Chart (A := A) (α := α) p) β :=
  (P.absorbParameters (X : α → MvPolynomial α R) ha).baseChange (Ring R α p)

/-- Retained coordinates are the images of the original, unchanged coordinates. -/
@[simp] theorem chartGenerators_val (P : Algebra.Generators R A (β ⊕ α))
    (ha : ∀ i, algebraMap (MvPolynomial α R) A (X i) = P.val (.inr i)) (j : β) :
    (chartGenerators p P ha).val j = (1 : Ring R α p) ⊗ₜ[MvPolynomial α R] P.val (.inl j) :=
  rfl

omit [IsScalarTower R (MvPolynomial α R) A] in
/-- The removed coordinates really equal the corresponding coefficient parameters. -/
theorem chart_parameter (P : Algebra.Generators R A (β ⊕ α))
    (ha : ∀ i, algebraMap (MvPolynomial α R) A (X i) = P.val (.inr i)) (i : α) :
    algebraMap (Ring R α p) (Chart (A := A) (α := α) p)
      (algebraMap (MvPolynomial α R) (Ring R α p) (X i)) =
        (1 : Ring R α p) ⊗ₜ[MvPolynomial α R] P.val (.inr i) := by
  change algebraMap (MvPolynomial α R) (Ring R α p) (X i) ⊗ₜ[MvPolynomial α R] 1 = _
  rw [Algebra.TensorProduct.tmul_one_eq_one_tmul, ha]

/-- Finitely many retained coordinates give genuine finite type over the new coefficient ring. -/
theorem finiteType_chart [Finite β] (P : Algebra.Generators R A (β ⊕ α))
    (ha : ∀ i, algebraMap (MvPolynomial α R) A (X i) = P.val (.inr i)) :
    Algebra.FiniteType (Ring R α p) (Chart (A := A) (α := α) p) :=
  (chartGenerators p P ha).finiteType

omit [Algebra R A] [IsScalarTower R (MvPolynomial α R) A] in
/-- Under the original-source action, this tensor chart is the required localization. -/
theorem isLocalization_chart :
    letI : Algebra A (Chart (A := A) (α := α) p) :=
      Algebra.TensorProduct.rightAlgebra
    IsLocalization
      (Algebra.algebraMapSubmonoid A (parameterIdeal R α p).primeCompl)
      (Chart (A := A) (α := α) p) := by
  let : Algebra A (Chart (A := A) (α := α) p) := Algebra.TensorProduct.rightAlgebra
  exact IsLocalization.tensorRight (R := MvPolynomial α R) (S := A)
    (Ring R α p) (parameterIdeal R α p).primeCompl

/-- The chart is canonically the literal source localization used by the residue-point theorem. -/
def chartEquivLocalization :
    letI : Algebra A (Chart (A := A) (α := α) p) := Algebra.TensorProduct.rightAlgebra
    Chart (A := A) (α := α) p ≃ₐ[A]
      Localization (Algebra.algebraMapSubmonoid A (parameterIdeal R α p).primeCompl) := by
  let : Algebra A (Chart (A := A) (α := α) p) := Algebra.TensorProduct.rightAlgebra
  let : IsLocalization
      (Algebra.algebraMapSubmonoid A (parameterIdeal R α p).primeCompl)
      (Chart (A := A) (α := α) p) := isLocalization_chart (A := A) p
  exact IsLocalization.algEquiv
    (Algebra.algebraMapSubmonoid A (parameterIdeal R α p).primeCompl)
    (Chart (A := A) (α := α) p)
    (Localization (Algebra.algebraMapSubmonoid A (parameterIdeal R α p).primeCompl))

omit [Algebra R A] [IsScalarTower R (MvPolynomial α R) A] in
/-- The localization comparison preserves every original source element. -/
theorem chartEquivLocalization_one_tmul (a : A) :
    chartEquivLocalization (A := A) (α := α) p ((1 : Ring R α p) ⊗ₜ[MvPolynomial α R] a) =
      algebraMap A
        (Localization (Algebra.algebraMapSubmonoid A (parameterIdeal R α p).primeCompl)) a := by
  let : Algebra A (Chart (A := A) (α := α) p) := Algebra.TensorProduct.rightAlgebra
  exact (chartEquivLocalization (A := A) (α := α) p).commutes a

end ParameterLocalization
