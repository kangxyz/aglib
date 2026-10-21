/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kaehler.GenericParameter
public import Aglib.RingTheory.Kaehler.GenericDifferentialProjection
public import Aglib.RingTheory.Kaehler.SeparatingOfSpan
public import Aglib.LinearAlgebra.Matrix.GenericCoordinateProjection
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! # Actual separating coordinates after generic parameter extension

The new coordinates use rows of the same whole parameter matrix. Parameter
derivatives vanish because these elements come from the actual generic ground
field. Differential base change and a nonzero determinant then produce the
spanning statement and algebraic separability over the field they generate.
-/

@[expose] public noncomputable section

open TensorProduct KaehlerDifferential MvPolynomial

namespace GenericParameterField

variable (k K : Type*) [Field k] [Field K] [Algebra k K]
variable (n : Type*) [Fintype n]

attribute [local instance] MvPolynomial.algebraMvPolynomial fractionAlgebra

local notation "P" => MvPolynomial (n × n) k
local notation "B" => MvPolynomial (n × n) K
local notation "F" => FractionRing P
local notation "L" => FractionRing B

/-- Generic linear combinations with coefficients in the actual generic base field. -/
def coordinate (x : n → K) (i : n) : L :=
  ∑ l, algebraMap F L (algebraMap P F (X (i, l))) * algebraMap K L (x l)

/-- A differential basis transported through the actual generic base-change equivalence. -/
def coordinateDifferentialBasis {d : ℕ} (b : Module.Basis (Fin d) K Ω[K⁄k]) :
    Module.Basis (Fin d) L Ω[L⁄F] :=
  (b.baseChange L).map (differentialEquiv k K (n × n))

omit [Fintype n] in
/-- Original coefficient derivatives have the transported original coordinates. -/
theorem coordinateDifferentialBasis_repr_D {d : ℕ}
    (b : Module.Basis (Fin d) K Ω[K⁄k]) (x : K) (i : Fin d) :
    (coordinateDifferentialBasis k K n b).repr (D F L (algebraMap K L x)) i =
      algebraMap K L (b.repr (D k K x) i) := by
  have h := differentialEquiv_tmul_D k K (n × n) (1 : L) x
  rw [one_smul] at h
  rw [← h]
  change (b.baseChange L).repr
    ((differentialEquiv k K (n × n)).symm
      ((differentialEquiv k K (n × n)) (1 ⊗ₜ[K] D k K x))) i = _
  rw [LinearEquiv.symm_apply_apply, Module.Basis.baseChange_repr_tmul]
  simp only [Algebra.smul_def, mul_one]

/-- Parameter coefficients are constants over the actual new ground field. -/
theorem D_coordinate (x : n → K) (i : n) :
    D F L (coordinate k K n x i) =
      ∑ l, algebraMap B L (X (i, l)) • D F L (algebraMap K L (x l)) := by
  simp only [coordinate, map_sum, Derivation.leibniz, Derivation.map_algebraMap,
    smul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  exact fractionMap_X k K (n × n) (i, l)

/-- Actual field generators yield separating generic coordinates, with the
new ground field and its action fixed canonically. -/
theorem generic_coordinates_span_and_isSeparable {d : ℕ} (x : n → K)
    (hx : IntermediateField.adjoin k (Set.range x) = ⊤)
    (b : Module.Basis (Fin d) K Ω[K⁄k]) (e : Fin d ↪ n) :
    Submodule.span L (Set.range (fun j => D F L (coordinate k K n x (e j)))) = ⊤ ∧
      Algebra.IsSeparable
        (IntermediateField.adjoin F (Set.range (fun j => coordinate k K n x (e j)))) L := by
  classical
  let A : Matrix (Fin d) n K := fun i j => b.repr (D k K (x j)) i
  let Q : Matrix (Fin d) (Fin d) B :=
    (A.map C * (Matrix.mvPolynomialX n n K).transpose).submatrix id e
  have hA : Submodule.span K (Set.range A.transpose) = ⊤ := by
    change Submodule.span K (Set.range (b.equivFun ∘ fun j => D k K (x j))) = ⊤
    rw [Set.range_comp]
    change Submodule.span K (b.equivFun.toLinearMap ''
      Set.range (fun j => D k K (x j))) = ⊤
    rw [← Submodule.map_span, span_range_D_of_adjoin_eq_top x hx, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr b.equivFun.surjective
  have hQ : Q.det ≠ 0 := Matrix.whole_genericProjection_det_ne_zero A e hA
  let bL := coordinateDifferentialBasis k K n b
  have hcoord : bL.toMatrix (fun j => D F L (coordinate k K n x (e j))) =
      Q.map (algebraMap B L) := by
    apply Matrix.ext
    intro i j
    change bL.repr (D F L (coordinate k K n x (e j))) i =
      algebraMap B L (∑ l, C (A i l) * X (e j, l))
    rw [D_coordinate]
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      bL, coordinateDifferentialBasis_repr_D, map_mul]
    apply Finset.sum_congr rfl
    intro l _
    rw [IsScalarTower.algebraMap_apply K B L]
    change algebraMap B L (X (e j, l)) * algebraMap B L (C (A i l)) = _
    exact mul_comm _ _
  have hdet : IsUnit (bL.det (fun j => D F L (coordinate k K n x (e j)))) := by
    rw [Module.Basis.det_apply, hcoord]
    change IsUnit ((algebraMap B L).mapMatrix Q).det
    rw [← RingHom.map_det]
    exact isUnit_iff_ne_zero.mpr
      (fun h => hQ ((FaithfulSMul.algebraMap_injective B L) (h.trans (map_zero _).symm)))
  have hspan := ((Module.Basis.is_basis_iff_det bL).mpr hdet).2
  refine ⟨hspan, ?_⟩
  let : Algebra.EssFiniteType k K := IntermediateField.fg_top_iff.mp
    (hx ▸ IntermediateField.fg_adjoin_of_finite (Set.finite_range x))
  let : Algebra.EssFiniteType k B := Algebra.EssFiniteType.comp k K B
  let : Algebra.EssFiniteType k L := Algebra.EssFiniteType.comp k B L
  let : Algebra.EssFiniteType F L := Algebra.EssFiniteType.of_comp k F L
  exact isSeparable_adjoin_of_span_differentials _ hspan

end GenericParameterField
