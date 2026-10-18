/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.K3.Map
public import Aglib.KTheory.MilnorK.K3.Symbols
public import Aglib.KTheory.MilnorK.K3.PolynomialResidue
public import Aglib.FieldTheory.RatFuncInversion

/-!
# The actual Milnor K₃ residue at infinity

Apply the actual rational-function automorphism `X ↦ X⁻¹`, take the finite
residue at `X`, and identify `AdjoinRoot X` with the original base field.
This constructs a map to the original Milnor K₂ quotient. It vanishes on the
entire image of constant Milnor K₃, sends `{X⁻¹,a,b}` to `{a,b}`, and sends
`{X,a,b}` to `−{a,b}`. No norm, reciprocity, degree formula, or leading-
coefficient formula is assumed.
-/

@[expose] public noncomputable section

namespace MilnorK.K3.InfinityResidue

open Polynomial MilnorK.K2 PolynomialResidue

variable (k : Type*) [Field k]

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩

/-- Evaluation at zero identifies the actual quotient `k[X]/(X)` with `k`. -/
def rootXEquiv : AdjoinRoot (X : k[X]) ≃ₐ[k] k := by
  let f := AdjoinRoot.liftAlgHom (X : k[X]) (Algebra.ofId k k) 0 (by simp)
  exact AlgEquiv.ofBijective f ⟨f.injective, fun a =>
    ⟨algebraMap k (AdjoinRoot (X : k[X])) a, f.commutes a⟩⟩

/-- The equivalence is actual evaluation at zero on every polynomial quotient class. -/
@[simp]
theorem rootXEquiv_mk (q : k[X]) :
    rootXEquiv k (AdjoinRoot.mk (X : k[X]) q) = q.eval 0 := rfl

/-- The original rational-function unit represented by the variable. -/
def variableUnit : (RatFunc k)ˣ := polynomialUnit X X_ne_zero

/-- The literal constant-field embedding on units. -/
def constantUnit (a : kˣ) : (RatFunc k)ˣ := Units.map RatFunc.C.toMonoidHom a

@[simp]
theorem variableUnit_coe : (variableUnit k : RatFunc k) = RatFunc.X := rfl

@[simp]
theorem constantUnit_coe (a : kˣ) : (constantUnit k a : RatFunc k) = RatFunc.C (a : k) := rfl

theorem inversion_variableUnit :
    Units.map (RatFunc.inversion k).toRingHom.toMonoidHom (variableUnit k) =
      (variableUnit k)⁻¹ := by
  apply Units.ext
  exact RatFunc.inversion_X k

theorem inversion_constantUnit (a : kˣ) :
    Units.map (RatFunc.inversion k).toRingHom.toMonoidHom (constantUnit k a) =
      constantUnit k a := by
  apply Units.ext
  exact RatFunc.inversion_C k a

/-- The actual infinity residue, with the original Milnor K₂ group as target. -/
def residue : Group (RatFunc k) →ₗ[ℤ] MilnorK.K2.Group k :=
  (MilnorK.K2.map (rootXEquiv k).toRingHom).comp
    ((residueAt (X : k[X])).comp (MilnorK.K3.map (RatFunc.inversion k).toRingHom))

/-- A nonzero constant polynomial is prime to the variable. -/
theorem not_dvd_constant (a : kˣ) : ¬ (X : k[X]) ∣ C (a : k) := by
  simpa only [X_dvd_iff, coeff_C_zero] using a.ne_zero

/-- The polynomial and constant-field constructions give the same actual unit. -/
theorem polynomialUnit_constant (a : kˣ) :
    polynomialUnit (C (a : k)) (C_ne_zero.mpr a.ne_zero) = constantUnit k a := by
  apply Units.ext
  rfl

/-- Evaluation of a constant quotient unit returns the original base-field unit. -/
theorem rootXEquiv_quotientUnit_constant (a : kˣ) :
    Units.map (rootXEquiv k).toRingHom.toMonoidHom
      (quotientUnit (X : k[X]) (C (a : k)) (not_dvd_constant k a)) = a := by
  apply Units.ext
  change rootXEquiv k (algebraMap k (AdjoinRoot (X : k[X])) (a : k)) = (a : k)
  exact (rootXEquiv k).commutes (a : k)

/-- Literal first-slot normalization at infinity, with uniformizer `X⁻¹`. -/
theorem residue_inv_variable (a b : kˣ) :
    residue k (symbol3 (variableUnit k)⁻¹ (constantUnit k a) (constantUnit k b)) =
      symbol a b := by
  rw [residue, LinearMap.comp_apply, LinearMap.comp_apply, map_symbol3,
    map_inv, inversion_variableUnit, inv_inv, inversion_constantUnit,
    inversion_constantUnit]
  rw [← polynomialUnit_constant k a, ← polynomialUnit_constant k b]
  change MilnorK.K2.map (rootXEquiv k).toRingHom
    (residueAt (X : k[X]) (symbol3 (polynomialUnit X X_ne_zero) _ _)) = _
  rw [residueAt_polynomial_units X (C (a : k)) (C (b : k))
    (C_ne_zero.mpr a.ne_zero) (C_ne_zero.mpr b.ne_zero)
    (not_dvd_constant k a) (not_dvd_constant k b), MilnorK.K2.map_symbol,
    rootXEquiv_quotientUnit_constant, rootXEquiv_quotientUnit_constant]

/-- The variable itself has the negative infinity normalization. -/
theorem residue_variable (a b : kˣ) :
    residue k (symbol3 (variableUnit k) (constantUnit k a) (constantUnit k b)) =
      -symbol a b := by
  have h := residue_inv_variable k a b
  rw [symbol3_inv_left, map_neg, neg_eq_iff_eq_neg] at h
  exact h

/-- Three literal constant units have zero infinity residue. -/
theorem residue_constant_symbols (a b c : kˣ) :
    residue k (symbol3 (constantUnit k a) (constantUnit k b) (constantUnit k c)) = 0 := by
  rw [residue, LinearMap.comp_apply, LinearMap.comp_apply, map_symbol3,
    inversion_constantUnit, inversion_constantUnit, inversion_constantUnit,
    ← polynomialUnit_constant k a, ← polynomialUnit_constant k b,
    ← polynomialUnit_constant k c,
    residueAt_polynomial_units_zero X (C (a : k)) (C (b : k)) (C (c : k))
      (C_ne_zero.mpr a.ne_zero) (C_ne_zero.mpr b.ne_zero) (C_ne_zero.mpr c.ne_zero)
      (not_dvd_constant k a) (not_dvd_constant k b) (not_dvd_constant k c), map_zero]

/-- The entire image of constant Milnor K₃ has zero infinity residue. -/
theorem residue_comp_constants :
    (residue k).comp (MilnorK.K3.map (RatFunc.C : k →+* RatFunc k)) = 0 := by
  apply MilnorK.K3.linearMap_ext
  intro a b c
  exact residue_constant_symbols k a b c

/-- Vanishing applies to every constant class, not merely chosen symbols. -/
theorem residue_constants (x : Group k) :
    residue k (MilnorK.K3.map (RatFunc.C : k →+* RatFunc k) x) = 0 :=
  LinearMap.congr_fun (residue_comp_constants k) x

end MilnorK.K3.InfinityResidue
