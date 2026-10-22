/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kaehler.GenericParameterTrdeg
public import Aglib.RingTheory.Kaehler.GenericSeparatingCoordinates
public import Aglib.RingTheory.Kaehler.AlgebraicIndependentBasis

/-! # A genuine separating basis from generic projection coordinates

The original separating basis fixes the transcendence degree. The actual generic
coordinates are proved independent using this degree, and their algebraic
extension is proved finite using the given field-generating family.
-/

@[expose] public noncomputable section

open scoped IntermediateField.algebraAdjoinAdjoin

namespace GenericParameterField

attribute [local instance] MvPolynomial.algebraMvPolynomial fractionAlgebra

variable (k K : Type*) [Field k] [Field K] [Algebra k K]
variable (n : Type*) [Fintype n]

local notation "F" => FractionRing (MvPolynomial (n × n) k)
local notation "L" => FractionRing (MvPolynomial (n × n) K)

/-- Generic projection of actual field generators gives a transcendence basis
with finite separable extension, starting from an original separating basis. -/
theorem generic_coordinates_isTranscendenceBasis_and_finite {d : ℕ}
    (t : Fin d → K) (ht : IsTranscendenceBasis k t)
    [Algebra.IsSeparable (IntermediateField.adjoin k (Set.range t)) K]
    (x : n → K) (hx : IntermediateField.adjoin k (Set.range x) = ⊤)
    (e : Fin d ↪ n) :
    let y := fun j => coordinate k K n x (e j)
    IsTranscendenceBasis F y ∧
      Module.Finite (IntermediateField.adjoin F (Set.range y)) L ∧
      Algebra.IsSeparable (IntermediateField.adjoin F (Set.range y)) L := by
  let y := fun j => coordinate k K n x (e j)
  let E := IntermediateField.adjoin F (Set.range y)
  obtain ⟨b, _⟩ := KaehlerDifferential.exists_basis_of_algebraicIndependent t ht.1
  have hsep : Algebra.IsSeparable E L :=
    (generic_coordinates_span_and_isSeparable k K n x hx b e).2
  let := hsep
  let : Algebra.IsAlgebraic (Algebra.adjoin F (Set.range y)) L :=
    Algebra.IsAlgebraic.trans (Algebra.adjoin F (Set.range y)) E L
  have htdeg : Algebra.trdeg k K = (d : Cardinal) := by
    simpa using ht.lift_cardinalMk_eq_trdeg.symm
  have hdeg : Algebra.trdeg F L = (d : Cardinal) := by
    rw [trdeg_fractionAlgebra k K (n × n), htdeg, Cardinal.lift_natCast]
  have hy : IsTranscendenceBasis F y :=
    Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite F y (by simp [hdeg])
  let : Algebra.EssFiniteType k K := IntermediateField.fg_top_iff.mp
    (hx ▸ IntermediateField.fg_adjoin_of_finite (Set.finite_range x))
  let : Algebra.EssFiniteType k (MvPolynomial (n × n) K) :=
    Algebra.EssFiniteType.comp k K (MvPolynomial (n × n) K)
  let : Algebra.EssFiniteType k L :=
    Algebra.EssFiniteType.comp k (MvPolynomial (n × n) K) L
  let : Algebra.EssFiniteType F L := Algebra.EssFiniteType.of_comp k F L
  let : Algebra.EssFiniteType E L := Algebra.EssFiniteType.of_comp F E L
  exact ⟨hy, Algebra.finite_of_essFiniteType_of_isAlgebraic, hsep⟩

end GenericParameterField
