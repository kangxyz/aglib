/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Unramified.Finite
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-!
# Transcendence degree of an actual flat unramified polynomial chart

The source algebra and the coefficient ring are domains. Flatness makes the
polynomial coefficient map faithful before its extension to fraction fields.
The fraction algebra is finite over the polynomial fraction field by the
native finite-dimensionality theorem for formally unramified field algebras.
No fraction map is associated to a possibly noninjective quotient map.
-/

@[expose] public noncomputable section

universe u v

namespace Algebra.FormallyUnramified

variable (R : Type u) (A : Type v) (n : ℕ)
variable [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
variable [Algebra R A] [Algebra (MvPolynomial (Fin n) R) A]
variable [IsScalarTower R (MvPolynomial (Fin n) R) A]
variable [Module.Flat (MvPolynomial (Fin n) R) A]
variable [Algebra.EssFiniteType (MvPolynomial (Fin n) R) A]
variable [Algebra.FormallyUnramified (MvPolynomial (Fin n) R) A]

/-- An actual flat essentially finite type formally unramified chart in n
polynomial parameters bounds the original-base transcendence degree by n. -/
theorem lift_trdeg_le_of_polynomial_chart :
    Cardinal.lift.{u} (Algebra.trdeg R A) ≤ (n : Cardinal) := by
  let P := MvPolynomial (Fin n) R
  let L := FractionRing A
  let F := FractionRing P
  let : IsScalarTower R P L := IsScalarTower.to₁₂₄ R P A L
  let : Module.Flat P L := Module.Flat.trans P A L
  let : FaithfulSMul P L := inferInstance
  let : Algebra F L := FractionRing.liftAlgebra P L
  let : IsScalarTower P F L := FractionRing.isScalarTower_liftAlgebra P L
  let : Algebra.EssFiniteType A L :=
    Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors A)
  let : Algebra.EssFiniteType P L := Algebra.EssFiniteType.comp P A L
  let : Algebra.EssFiniteType F L := Algebra.EssFiniteType.of_comp P F L
  let : Algebra.FormallyUnramified A L :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors A)
  let : Algebra.FormallyUnramified P L := Algebra.FormallyUnramified.comp P A L
  let : Algebra.FormallyUnramified F L :=
    Algebra.FormallyUnramified.of_restrictScalars P F L
  let : Module.Finite F L := Algebra.FormallyUnramified.finite_of_free F L
  let : Algebra.IsAlgebraic F L := inferInstance
  let : Algebra.IsAlgebraic P F := IsLocalization.isAlgebraic F (nonZeroDivisors P)
  let : Algebra.IsAlgebraic P L := Algebra.IsAlgebraic.trans P F L
  have hdeg : Cardinal.lift.{u} (Algebra.trdeg R L) = (n : Cardinal) := by
    simpa [P, trdeg_eq_zero] using (lift_trdeg_add_eq R P L).symm
  have hle : Algebra.trdeg R A ≤ Algebra.trdeg R L :=
    trdeg_le_of_injective (IsScalarTower.toAlgHom R A L) (IsFractionRing.injective A L)
  exact (Cardinal.lift_le.mpr hle).trans_eq hdeg

end Algebra.FormallyUnramified
