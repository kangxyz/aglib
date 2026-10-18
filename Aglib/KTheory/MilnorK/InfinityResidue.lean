/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Residue.Polynomial.Basic
public import Aglib.FieldTheory.RatFuncInversion

/-!
# Actual infinity residues in every Milnor degree

Invert the variable, take the actual finite residue at `X`, then identify
`AdjoinRoot X` with the base field by evaluation at zero. Last-slot
normalization sends `{a₁,…,aₙ,X⁻¹}` to `{a₁,…,aₙ}` in every degree and
sends the analogous variable symbol to its negative. The entire image of
constant Milnor K-theory has zero residue. No norm or reciprocity is assumed.
-/

@[expose] public noncomputable section

namespace MilnorK.InfinityResidue

open Polynomial PolynomialResidue

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

/-- Inversion followed by the actual finite residue at `X`, in every degree. -/
def residue (n : ℕ) : K (RatFunc k) (n + 1) →ₗ[ℤ] K k n :=
  (MilnorK.map n (rootXEquiv k).toRingHom).comp
    ((residueAt (X : k[X]) n).comp (MilnorK.map (n + 1) (RatFunc.inversion k).toRingHom))

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

/-- Inversion fixes every tuple of literal constant units. -/
theorem inversion_constant_tuple (n : ℕ) (a : SymbolTuple k n) :
    Units.map (RatFunc.inversion k).toRingHom.toMonoidHom ∘ (constantUnit k ∘ a) =
      constantUnit k ∘ a := by
  funext i
  exact inversion_constantUnit k (a i)

/-- The constant tuple agrees with its nonzero constant polynomial representation. -/
theorem polynomialUnit_constant_tuple (n : ℕ) (a : SymbolTuple k n) :
    (fun i => polynomialUnit (C (a i : k)) (C_ne_zero.mpr (a i).ne_zero)) =
      constantUnit k ∘ a := by
  funext i
  exact polynomialUnit_constant k (a i)

/-- Last-slot normalization at infinity, with actual uniformizer `X⁻¹`. -/
theorem residue_inv_variable (n : ℕ) (a : SymbolTuple k n) :
    residue k n (symbol (Fin.snoc (constantUnit k ∘ a) (variableUnit k)⁻¹)) =
      symbol a := by
  rw [residue, LinearMap.comp_apply, LinearMap.comp_apply, MilnorK.map_symbol,
    Fin.comp_snoc, map_inv, inversion_variableUnit, inv_inv, inversion_constant_tuple,
    ← polynomialUnit_constant_tuple]
  change MilnorK.map n (rootXEquiv k).toRingHom
    (residueAt (X : k[X]) n (symbol (Fin.snoc _ (polynomialUnit X X_ne_zero)))) = _
  rw [residueAt_polynomial_units X n (fun i => C (a i : k))
    (fun i => C_ne_zero.mpr (a i).ne_zero) (fun i => not_dvd_constant k (a i)),
    MilnorK.map_symbol]
  congr 1
  funext i
  exact rootXEquiv_quotientUnit_constant k (a i)

/-- The variable itself has negative last-slot infinity normalization, in every degree. -/
theorem residue_variable (n : ℕ) (a : SymbolTuple k n) :
    residue k n (symbol (Fin.snoc (constantUnit k ∘ a) (variableUnit k))) = -symbol a := by
  have h := residue_inv_variable k n a
  have hneg : symbol (Fin.snoc (constantUnit k ∘ a) (variableUnit k)⁻¹) =
      -symbol (Fin.snoc (constantUnit k ∘ a) (variableUnit k)) := by
    simpa only [Fin.update_snoc_last] using
      symbol_update_inv (Fin.snoc (constantUnit k ∘ a) (variableUnit k))
        (Fin.last n) (variableUnit k)
  rw [hneg, map_neg, neg_eq_iff_eq_neg] at h
  exact h

/-- All-constant symbols have zero infinity residue, including degree one. -/
theorem residue_constant_symbols (n : ℕ) (a : SymbolTuple k (n + 1)) :
    residue k n (symbol (constantUnit k ∘ a)) = 0 := by
  rw [residue, LinearMap.comp_apply, LinearMap.comp_apply, MilnorK.map_symbol,
    inversion_constant_tuple, ← polynomialUnit_constant_tuple,
    residueAt_polynomial_units_zero X n (fun i => C (a i : k))
      (fun i => C_ne_zero.mpr (a i).ne_zero) (fun i => not_dvd_constant k (a i)), map_zero]

/-- The entire constant-field map is killed by the infinity residue. -/
theorem residue_comp_constants (n : ℕ) :
    (residue k n).comp (MilnorK.map (n + 1) (RatFunc.C : k →+* RatFunc k)) = 0 := by
  apply MilnorK.linearMap_ext
  intro a
  simp only [LinearMap.comp_apply, MilnorK.map_symbol, LinearMap.zero_apply]
  exact residue_constant_symbols k n a

/-- Infinity vanishing applies to all constant classes in every positive degree. -/
theorem residue_constants (n : ℕ) (x : K k (n + 1)) :
    residue k n (MilnorK.map (n + 1) (RatFunc.C : k →+* RatFunc k) x) = 0 :=
  LinearMap.congr_fun (residue_comp_constants k n) x

end MilnorK.InfinityResidue
