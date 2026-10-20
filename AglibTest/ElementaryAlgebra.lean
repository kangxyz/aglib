/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Aglib.Algebra.Group.NormalizedQuotient
import Aglib.Data.ZMod.CoefficientMaps
import Aglib.RingTheory.TensorProduct.PolynomialCoordinates
import Aglib.GroupTheory.QuotientGroup.Power

/-! Direct consumers of the literal maps exposed by the elementary algebra migration. -/

open scoped TensorProduct Polynomial

namespace AglibTest.ElementaryAlgebra

universe u

/-- The normalized quotient equivalence uses the original quotient projection. -/
theorem normalized_forward {C I : Type*} [AddCommGroup C] [AddCommGroup I]
    (c : C →+ I) (s : I →+ C) (hsc : Function.LeftInverse s c) (x : s.ker) :
    AddMonoidHom.Retraction.normalizedQuotientEquiv c s hsc x =
      QuotientAddGroup.mk' c.range (x : I) := rfl

/-- Restriction to torsion retains the forward additive equivalence on elements. -/
theorem torsion_forward {P Q : Type*} [AddCommGroup P] [AddCommGroup Q]
    (n : ℕ) (e : P ≃+ Q) (x : AddSubgroup.torsionBy P (n : ℤ)) :
    (AddEquiv.torsionByNat n e x : Q) = e (x : P) := rfl

/-- Insertion runs from the smaller level to the larger and multiplies by their ratio. -/
theorem coefficient_insertion_direction :
    ZMod.divisorInsertion (show 2 ∣ 6 from ⟨3, rfl⟩) (1 : ZMod 2) = (3 : ZMod 6) := by
  simpa using ZMod.divisorInsertion_intCast (show 2 ∣ 6 from ⟨3, rfl⟩) (1 : ℤ)

/-- Scalar extension uses Mathlib's actual equivalence and the given coefficient map. -/
theorem polynomial_tensor_forward {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] (a : A) (p : R[X]) :
    (polyEquivTensor' R A).symm (a ⊗ₜ[R] p) =
      Polynomial.C a * p.map (algebraMap R A) :=
  Polynomial.polyEquivTensor'_symm_tmul (R := R) (A := A) a p

/-- The quotient power map acts on literal representatives by the chosen exponent. -/
theorem quotient_power_forward {G : Type*} [CommGroup G]
    (p q : G) (a b : ℕ) (h : p ^ a = q ^ b) (x : G) :
    QuotientGroup.zpowersPowerMap p q a b h (QuotientGroup.mk x) =
      QuotientGroup.mk (x ^ a) := rfl

end AglibTest.ElementaryAlgebra
