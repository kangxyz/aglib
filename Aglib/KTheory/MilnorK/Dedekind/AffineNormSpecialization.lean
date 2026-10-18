/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Dedekind.AffineUnramifiedNorm
public import Aglib.KTheory.MilnorK.ConstantRestriction
public import Aglib.KTheory.MilnorK.Residue.Polynomial.LinearPlace

/-!
# Linear-place specialization of actual affine unit norms

Evaluation of the actual specialization at `X - C a` is a left inverse to
constant-field restriction in every degree. Hence all linear places agree on
the actual field norm of every unramified affine class, in particular every
global ring-unit symbol. No boundary, moving, or symbol-representability
assumption enters the endpoint equality.
-/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial

namespace PolynomialResidue

open InfinityResidue

variable {k : Type*} [Field k]

local instance (a : k) : Fact (Irreducible (X - C a)) :=
  ⟨irreducible_X_sub_C a⟩

/-- Specialization at the literal linear DVR, followed by evaluation at its root. -/
def linearSpecialization (a : k) (n : ℕ) : K (RatFunc k) n →ₗ[ℤ] K k n :=
  (MilnorK.map n (linearRootEquiv a).toRingHom).comp (specializeAt (X - C a) n)

/-- Residue at the literal linear DVR, followed by evaluation at its root. -/
def linearResidue (a : k) (n : ℕ) : K (RatFunc k) (n + 1) →ₗ[ℤ] K k n :=
  (MilnorK.map n (linearRootEquiv a).toRingHom).comp (residueAt (X - C a) n)

/-- A nonzero constant polynomial is prime to every literal linear place. -/
theorem linear_not_dvd_constant (a : k) (b : kˣ) : ¬ X - C a ∣ C (b : k) := by
  simpa only [dvd_iff_isRoot, IsRoot, eval_C] using b.ne_zero

/-- Actual evaluation recovers a constant quotient unit at any linear place. -/
theorem linearRootEquiv_quotientUnit_constant (a : k) (b : kˣ) :
    Units.map (linearRootEquiv a).toRingHom.toMonoidHom
      (quotientUnit (X - C a) (C (b : k)) (linear_not_dvd_constant a b)) = b := by
  apply Units.ext
  change linearRootEquiv a (algebraMap k (AdjoinRoot (X - C a)) (b : k)) = (b : k)
  exact (linearRootEquiv a).commutes (b : k)

/-- Constant symbols are recovered at every actual linear place, including degree zero. -/
theorem linearSpecialization_constant_symbols (a : k) (n : ℕ) (b : SymbolTuple k n) :
    linearSpecialization a n (symbol (constantUnit k ∘ b)) = symbol b := by
  rw [linearSpecialization, LinearMap.comp_apply, ← polynomialUnit_constant_tuple,
    specializeAt_polynomial_units (X - C a) n (fun i => C (b i : k))
      (fun i => C_ne_zero.mpr (b i).ne_zero) (fun i => linear_not_dvd_constant a (b i)),
    MilnorK.map_symbol]
  congr 1
  funext i
  exact linearRootEquiv_quotientUnit_constant a (b i)

/-- The literal specialization is a left inverse on the entire quotient. -/
theorem linearSpecialization_comp_constants (a : k) (n : ℕ) :
    (linearSpecialization a n).comp (MilnorK.map n (RatFunc.C : k →+* RatFunc k)) =
      LinearMap.id := by
  apply MilnorK.linearMap_ext
  intro b
  rw [LinearMap.comp_apply, ConstantRestriction.constants_symbol,
    linearSpecialization_constant_symbols, LinearMap.id_apply]

/-- Recovery applies to an arbitrary constant class, not merely a pure symbol. -/
theorem linearSpecialization_constants (a : k) (n : ℕ) (x : K k n) :
    linearSpecialization a n (MilnorK.map n (RatFunc.C : k →+* RatFunc k) x) = x :=
  LinearMap.congr_fun (linearSpecialization_comp_constants a n) x

/-- All actual linear-place specializations agree on the entire constant image. -/
theorem linearSpecialization_eq_of_mem_constant_range (a b : k) (n : ℕ)
    (x : K (RatFunc k) n)
    (hx : x ∈ LinearMap.range (MilnorK.map n (RatFunc.C : k →+* RatFunc k))) :
    linearSpecialization a n x = linearSpecialization b n x := by
  obtain ⟨y, rfl⟩ := hx
  rw [linearSpecialization_constants, linearSpecialization_constants]

/-- Last-slot multiplication by the actual linear uniformizer recovers every
constant class through its actual evaluated residue. -/
theorem linearResidue_productUnit_constants (a : k) (n : ℕ) (x : K k n) :
    linearResidue a n
      (productUnit n (MilnorK.map n (RatFunc.C : k →+* RatFunc k) x)
        (Additive.ofMul (polynomialUnit (X - C a) (irreducible_X_sub_C a).ne_zero))) = x := by
  have h : (linearResidue a n).comp
      (((productUnit n).flip
        (Additive.ofMul (polynomialUnit (X - C a) (irreducible_X_sub_C a).ne_zero))).comp
          (MilnorK.map n (RatFunc.C : k →+* RatFunc k))) = LinearMap.id := by
    apply MilnorK.linearMap_ext
    intro b
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, ConstantRestriction.constants_symbol,
      productUnit_symbol, LinearMap.id_apply]
    change linearResidue a n (symbol (Fin.snoc (constantUnit k ∘ b)
      (polynomialUnit (X - C a) (irreducible_X_sub_C a).ne_zero))) = symbol b
    rw [linearResidue, LinearMap.comp_apply, ← polynomialUnit_constant_tuple,
      residueAt_polynomial_units (X - C a) n (fun i => C (b i : k))
        (fun i => C_ne_zero.mpr (b i).ne_zero) (fun i => linear_not_dvd_constant a (b i)),
      MilnorK.map_symbol]
    congr 1
    funext i
    exact linearRootEquiv_quotientUnit_constant a (b i)
  exact LinearMap.congr_fun h x

/-- On any constant-image class, last-slot linear-uniformizer residue equals
actual specialization at that same place. -/
theorem linearResidue_productUnit_eq_specialization (a : k) (n : ℕ)
    (x : K (RatFunc k) n)
    (hx : x ∈ LinearMap.range (MilnorK.map n (RatFunc.C : k →+* RatFunc k))) :
    linearResidue a n
      (productUnit n x
        (Additive.ofMul (polynomialUnit (X - C a) (irreducible_X_sub_C a).ne_zero))) =
      linearSpecialization a n x := by
  obtain ⟨y, rfl⟩ := hx
  rw [linearResidue_productUnit_constants, linearSpecialization_constants]

end PolynomialResidue

namespace DedekindResidue

open PolynomialResidue IsLocalRing IsDedekindDomain

universe u
variable (k S E : Type u) [Field k] [CharZero k]
  [CommRing S] [IsDedekindDomain S] [Algebra k[X] S] [Module.Finite k[X] S]
  [Module.IsTorsionFree k[X] S]
  [Field E] [Algebra S E] [IsFractionRing S E]
  [Algebra k[X] E] [IsScalarTower k[X] S E]
  [Algebra (RatFunc k) E] [IsScalarTower k[X] (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E]

/-- At any two endpoints, the literal specializations of the actual norm of
an arbitrary everywhere unramified affine class agree. -/
theorem linearSpecialization_norm_eq_of_totalResidue_zero (a b : k) (n : ℕ)
    (x : K E (n + 1)) (hx : totalResidue S E n x = 0) :
    linearSpecialization a (n + 1) (finiteExtensionNorm (RatFunc k) E (n + 1) x) =
      linearSpecialization b (n + 1) (finiteExtensionNorm (RatFunc k) E (n + 1) x) :=
  linearSpecialization_eq_of_mem_constant_range a b (n + 1) _
    (norm_mem_constant_range_of_totalResidue_zero k S E n x hx)

/-- Actual field norms of global coordinate-unit symbols have equal literal
endpoint specializations, without any boundary hypothesis. -/
theorem linearSpecialization_norm_ring_unit_symbol_eq (a b : k) (n : ℕ)
    (u : Fin (n + 1) → Sˣ) :
    linearSpecialization a (n + 1) (finiteExtensionNorm (RatFunc k) E (n + 1)
      (symbol (Units.map (algebraMap S E).toMonoidHom ∘ u))) =
      linearSpecialization b (n + 1) (finiteExtensionNorm (RatFunc k) E (n + 1)
        (symbol (Units.map (algebraMap S E).toMonoidHom ∘ u))) :=
  linearSpecialization_eq_of_mem_constant_range a b (n + 1) _
    (norm_ring_unit_symbol_mem_constant_range k S E n u)

/-- The actual norm's last-slot linear-uniformizer residue is precisely its
literal specialization, for every global coordinate-unit symbol. -/
theorem linearResidue_norm_ring_unit_symbol_productUnit (a : k) (n : ℕ)
    (u : Fin (n + 1) → Sˣ) :
    linearResidue a (n + 1)
      (productUnit (n + 1) (finiteExtensionNorm (RatFunc k) E (n + 1)
        (symbol (Units.map (algebraMap S E).toMonoidHom ∘ u)))
        (Additive.ofMul (polynomialUnit (X - C a) (irreducible_X_sub_C a).ne_zero))) =
      linearSpecialization a (n + 1) (finiteExtensionNorm (RatFunc k) E (n + 1)
        (symbol (Units.map (algebraMap S E).toMonoidHom ∘ u))) :=
  linearResidue_productUnit_eq_specialization a (n + 1) _
    (norm_ring_unit_symbol_mem_constant_range k S E n u)

end DedekindResidue
end MilnorK
