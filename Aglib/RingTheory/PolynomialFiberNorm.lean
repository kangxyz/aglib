/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteAlgebraNormLength
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.Algebra.Polynomial.Degree.Units
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Norms in the literal fibers of a polynomial algebra

A finite free algebra over `k[X]` and a unit in it give equal determinant
norms in every evaluation fiber. The all-point residue-norm formula retains
the full local lengths, including nonreduced fibers and every branch.

This is the algebraic norm calculation only. It does not identify the fiber
fundamental cycle with any correspondence-theoretic endpoint pullback.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open Polynomial

namespace Algebra

/-- The determinant norm commutes with arbitrary scalar extension. The
multiplication operator is the actual base change of multiplication by `b`. -/
theorem norm_one_tmul {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Module.Free R B] [Module.Finite R B] (b : B) :
    Algebra.norm A (1 ⊗ₜ[R] b : A ⊗[R] B) = algebraMap R A (Algebra.norm R b) := by
  rw [Algebra.norm_apply, ← Algebra.baseChange_lmul, LinearMap.det_baseChange,
    ← Algebra.norm_apply]

end Algebra

namespace Algebra.PolynomialFiber

universe u v

variable {k : Type u} [Field k]

/-- The polynomial action on the residue field at the literal point `a`. -/
abbrev evaluationAlgebra (a : k) : Algebra k[X] k := (Polynomial.evalRingHom a).toAlgebra

variable (B : Type v) [CommRing B] [Algebra k[X] B]

/-- The literal tensor-product fiber, with polynomial scalars acting on `k`
by evaluation at `a`. -/
abbrev Fiber (a : k) : Type (max u v) :=
  let := evaluationAlgebra a
  k ⊗[k[X]] B

instance fiberCommRing (a : k) : CommRing (Fiber B a) :=
  let := evaluationAlgebra a
  inferInstanceAs (CommRing (k ⊗[k[X]] B))

instance fiberAlgebra (a : k) : Algebra k (Fiber B a) :=
  let := evaluationAlgebra a
  inferInstanceAs (Algebra k (k ⊗[k[X]] B))

instance fiberFinite [Module.Finite k[X] B] (a : k) : Module.Finite k (Fiber B a) :=
  let := evaluationAlgebra a
  inferInstanceAs (Module.Finite k (k ⊗[k[X]] B))

/-- The actual right tensor inclusion into the evaluation fiber. -/
def specialize (a : k) : B →+* Fiber B a :=
  let := evaluationAlgebra a
  Algebra.TensorProduct.includeRight.toRingHom

variable {B}

/-- The norm of the image in a fiber is the evaluation of the original
polynomial-valued determinant norm. -/
theorem norm_specialize [Module.Free k[X] B] [Module.Finite k[X] B]
    (a : k) (b : B) :
    Algebra.norm k (specialize B a b) = (Algebra.norm k[X] b).eval a := by
  let := evaluationAlgebra a
  exact Algebra.norm_one_tmul (R := k[X]) (A := k) b

/-- The existing norm sends a unit to a constant unit polynomial. -/
theorem norm_unit_eq_C (u : Bˣ) :
    ∃ c : kˣ, Algebra.norm k[X] (u : B) = Polynomial.C (c : k) := by
  obtain ⟨c, hc, h⟩ := Polynomial.isUnit_iff.mp (u.isUnit.map (Algebra.norm k[X]))
  obtain ⟨c, rfl⟩ := hc
  exact ⟨c, h.symm⟩

/-- Every two actual fibers have equal norms of a global unit. -/
theorem norm_specialize_eq [Module.Free k[X] B] [Module.Finite k[X] B]
    (u : Bˣ) (a b : k) :
    Algebra.norm k (specialize B a (u : B)) =
      Algebra.norm k (specialize B b (u : B)) := by
  obtain ⟨c, hc⟩ := norm_unit_eq_C (k := k) u
  simp only [norm_specialize, hc, Polynomial.eval_C]



/-- Finite torsion-free polynomial algebras meet the finite-free hypothesis
because a polynomial ring over a field is a PID. -/
theorem norm_specialize_eq_of_torsionFree [Module.Finite k[X] B]
    [Module.IsTorsionFree k[X] B] (u : Bˣ) (a b : k) :
    Algebra.norm k (specialize B a (u : B)) =
      Algebra.norm k (specialize B b (u : B)) := by
  let : Module.Free k[X] B := Module.free_of_finite_type_torsion_free'
  exact norm_specialize_eq u a b

/-- The equality also holds in the actual unit group of the base field,
using the existing norm monoid homomorphism on both fibers. -/
theorem normUnits_specialize_eq [Module.Free k[X] B] [Module.Finite k[X] B]
    (u : Bˣ) (a b : k) :
    Units.map (Algebra.norm k) (Units.map (specialize B a).toMonoidHom u) =
      Units.map (Algebra.norm k) (Units.map (specialize B b).toMonoidHom u) := by
  apply Units.ext
  exact norm_specialize_eq u a b

/-- The fiber norm is the product over all its actual maximal ideals,
with exponents equal to the literal local-ring lengths. -/
theorem norm_specialize_eq_prod [Module.Finite k[X] B]
    (a : k) [Fintype (MaximalSpectrum (Fiber B a))] (x : B) :
    Algebra.norm k (specialize B a x) =
      ∏ p : MaximalSpectrum (Fiber B a),
        Algebra.norm k (Ideal.Quotient.mk p.asIdeal (specialize B a x)) ^
          (Module.length (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime p.asIdeal)).toNat :=
  Algebra.norm_eq_prod_quotient_norm_pow_local_length _

/-- Equality of the actual length-weighted residue-norm products in two
fibers. No reducedness, separability, or etaleness hypothesis is used. -/
theorem prod_residue_norm_eq [Module.Free k[X] B] [Module.Finite k[X] B]
    (u : Bˣ) (a b : k)
    [Fintype (MaximalSpectrum (Fiber B a))] [Fintype (MaximalSpectrum (Fiber B b))] :
    (∏ p : MaximalSpectrum (Fiber B a),
      Algebra.norm k (Ideal.Quotient.mk p.asIdeal (specialize B a (u : B))) ^
        (Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)).toNat) =
    ∏ p : MaximalSpectrum (Fiber B b),
      Algebra.norm k (Ideal.Quotient.mk p.asIdeal (specialize B b (u : B))) ^
        (Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)).toNat := by
  rw [← norm_specialize_eq_prod, ← norm_specialize_eq_prod]
  exact norm_specialize_eq u a b

/-- The same all-point product equality with the finite spectra derived
from finite generation, rather than supplied as extra hypotheses. -/
theorem prod_residue_norm_eq_of_finite [Module.Free k[X] B] [Module.Finite k[X] B]
    (u : Bˣ) (a b : k) :
    let : Finite (MaximalSpectrum (Fiber B a)) :=
      Module.finiteAlgebra_maximalSpectrum_finite k (Fiber B a)
    let : Finite (MaximalSpectrum (Fiber B b)) :=
      Module.finiteAlgebra_maximalSpectrum_finite k (Fiber B b)
    let : Fintype (MaximalSpectrum (Fiber B a)) := Fintype.ofFinite _
    let : Fintype (MaximalSpectrum (Fiber B b)) := Fintype.ofFinite _
    (∏ p : MaximalSpectrum (Fiber B a),
      Algebra.norm k (Ideal.Quotient.mk p.asIdeal (specialize B a (u : B))) ^
        (Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)).toNat) =
    ∏ p : MaximalSpectrum (Fiber B b),
      Algebra.norm k (Ideal.Quotient.mk p.asIdeal (specialize B b (u : B))) ^
        (Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)).toNat := by
  let : Finite (MaximalSpectrum (Fiber B a)) :=
    Module.finiteAlgebra_maximalSpectrum_finite k (Fiber B a)
  let : Finite (MaximalSpectrum (Fiber B b)) :=
    Module.finiteAlgebra_maximalSpectrum_finite k (Fiber B b)
  let : Fintype (MaximalSpectrum (Fiber B a)) := Fintype.ofFinite _
  let : Fintype (MaximalSpectrum (Fiber B b)) := Fintype.ofFinite _
  exact prod_residue_norm_eq u a b

end Algebra.PolynomialFiber
