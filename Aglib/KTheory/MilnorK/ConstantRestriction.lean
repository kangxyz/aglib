/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.InfinityResidue

/-!
# Split injectivity of rational constant-field restriction

The literal embedding `k → k(t)` induces an injective map of Milnor groups
in every nonnegative degree. An explicit left inverse specializes at the
actual polynomial DVR `(X)` and then evaluates `k[X]/(X)` at zero. The proof
uses literal reduction of constant polynomial units, then the universal
property of the Milnor symbol quotient to cover every class.

This is specific to the rational constant-field embedding. It assumes no
finite-extension norm, rational exactness or general specialization naturality.
-/

@[expose] public noncomputable section

namespace MilnorK.ConstantRestriction

open Polynomial PolynomialResidue InfinityResidue

variable (k : Type*) [Field k]

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩

/-- Specialize at the actual DVR `(X)`, then evaluate its residue field at zero. -/
def specializeZero (n : ℕ) : K (RatFunc k) n →ₗ[ℤ] K k n :=
  (MilnorK.map n (rootXEquiv k).toRingHom).comp (specializeAt (X : k[X]) n)

/-- Constant-field restriction sends symbols to literal rational constant units. -/
theorem constants_symbol (n : ℕ) (a : SymbolTuple k n) :
    MilnorK.map n (RatFunc.C : k →+* RatFunc k) (symbol a) =
      symbol (constantUnit k ∘ a) :=
  MilnorK.map_symbol n RatFunc.C a

/-- The explicit specialization recovers each original constant symbol, also in degree zero. -/
theorem specializeZero_constant_symbols (n : ℕ) (a : SymbolTuple k n) :
    specializeZero k n (symbol (constantUnit k ∘ a)) = symbol a := by
  rw [specializeZero, LinearMap.comp_apply, ← polynomialUnit_constant_tuple,
    specializeAt_polynomial_units X n (fun i => C (a i : k))
      (fun i => C_ne_zero.mpr (a i).ne_zero) (fun i => not_dvd_constant k (a i)),
    MilnorK.map_symbol]
  congr 1
  funext i
  exact rootXEquiv_quotientUnit_constant k (a i)

/-- The actual linear maps compose to the identity on the entire Milnor quotient. -/
theorem specializeZero_comp_constants (n : ℕ) :
    (specializeZero k n).comp (MilnorK.map n (RatFunc.C : k →+* RatFunc k)) =
      LinearMap.id := by
  apply MilnorK.linearMap_ext
  intro a
  rw [LinearMap.comp_apply, constants_symbol, specializeZero_constant_symbols,
    LinearMap.id_apply]

/-- Every constant class is recovered, with no symbol-representability hypothesis. -/
theorem specializeZero_constants (n : ℕ) (x : K k n) :
    specializeZero k n (MilnorK.map n (RatFunc.C : k →+* RatFunc k) x) = x :=
  LinearMap.congr_fun (specializeZero_comp_constants k n) x

/-- Constant-field restriction has this explicit left inverse in every degree. -/
theorem constants_leftInverse (n : ℕ) :
    Function.LeftInverse (specializeZero k n)
      (MilnorK.map n (RatFunc.C : k →+* RatFunc k)) :=
  specializeZero_constants k n

/-- The actual constant-field restriction is injective in every nonnegative degree. -/
theorem constants_injective (n : ℕ) :
    Function.Injective (MilnorK.map n (RatFunc.C : k →+* RatFunc k)) :=
  (constants_leftInverse k n).injective

end MilnorK.ConstantRestriction
