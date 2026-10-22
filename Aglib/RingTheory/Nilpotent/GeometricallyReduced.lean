/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Unramified.Field

/-!
# Testing geometric reducedness on finite field extensions

Only finite extensions in the universe of the base field are needed. The other
algebra can lie in an independent universe, and its supplied base-field action
is retained throughout. No Noetherian or regularity condition is imposed on an
algebraic-closure tensor product.
-/

open scoped TensorProduct

@[expose] public noncomputable section

universe u v

namespace Algebra

/-- Reducedness after all finite field extensions implies reducedness after
base change to the algebraic closure. The finite-coefficient descent is supplied
by `IsReduced.tensorProduct_of_flat_of_forall_fg`, after commuting factors. -/
theorem isReduced_algebraicClosure_tensorProduct_of_finiteExtensions
    (K : Type u) (A : Type v) [Field K] [CommRing A] [Algebra K A]
    (h : ∀ (E : Type u) [Field E] [Algebra K E] [FiniteDimensional K E],
      IsReduced (E ⊗[K] A)) :
    IsReduced (AlgebraicClosure K ⊗[K] A) := by
  have hfinite (B : Subalgebra K (AlgebraicClosure K)) (hB : B.FG) :
      FiniteDimensional K B := by
    obtain ⟨s, rfl⟩ := hB
    exact Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet
      (fun x _ ↦ Algebra.IsIntegral.isIntegral x)
  have hcomm : IsReduced (A ⊗[K] AlgebraicClosure K) := by
    apply IsReduced.tensorProduct_of_flat_of_forall_fg
    intro B hB
    let : Field B := B.isField_of_algebraic.toField
    let : FiniteDimensional K B := hfinite B hB
    let : IsReduced (B ⊗[K] A) := h B
    exact isReduced_of_injective (Algebra.TensorProduct.comm K A B)
      (Algebra.TensorProduct.comm K A B).injective
  let : IsReduced (A ⊗[K] AlgebraicClosure K) := hcomm
  exact isReduced_of_injective (Algebra.TensorProduct.comm K (AlgebraicClosure K) A)
    (Algebra.TensorProduct.comm K (AlgebraicClosure K) A).injective

/-- Finite field extensions test geometric reducedness over a field.
In particular this applies to a field `A` with its actual `K`-algebra action. -/
theorem IsGeometricallyReduced.of_finiteExtensions
    (K : Type u) (A : Type v) [Field K] [CommRing A] [Algebra K A]
    (h : ∀ (E : Type u) [Field E] [Algebra K E] [FiniteDimensional K E],
      IsReduced (E ⊗[K] A)) :
    IsGeometricallyReduced K A :=
  (isGeometricallyReduced_field_iff K A).mpr
    (isReduced_algebraicClosure_tensorProduct_of_finiteExtensions K A h)

/-- Every field extension of a perfect field is geometrically reduced, with
respect to its supplied algebra structure. The extension need not be algebraic
or finitely generated. -/
theorem isGeometricallyReduced_field_of_perfectField
    (k : Type u) (L : Type v) [Field k] [Field L] [Algebra k L]
    [PerfectField k] : IsGeometricallyReduced k L := by
  apply IsGeometricallyReduced.of_finiteExtensions k L
  intro E _ _ _
  let : FormallyUnramified k E := FormallyUnramified.of_isSeparable k E
  let : IsReduced (L ⊗[k] E) := FormallyUnramified.isReduced_of_field L (L ⊗[k] E)
  exact isReduced_of_injective (Algebra.TensorProduct.comm k E L)
    (Algebra.TensorProduct.comm k E L).injective

end Algebra
