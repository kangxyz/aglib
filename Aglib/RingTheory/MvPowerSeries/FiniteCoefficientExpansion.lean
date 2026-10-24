/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.MvPowerSeries.Expand

/-!
# A finite coefficient basis after expanding two formal variables

The scalar map first applies the given coefficient-field map and then sends
each variable to its `q`-th power. A finite coefficient basis and the two
exponent residues give a basis of the original power-series ring. The inverse
extracts the coefficient at `q • n + r` and applies the coefficient basis.
All sums in the reconstruction are finite; no continuity hypothesis is used.
-/

@[expose] public noncomputable section

open Module

namespace MvPowerSeries
namespace FiniteCoefficientExpansion

variable {k₀ k D : Type*} [Field k₀] [Field k] [Algebra k₀ k]

/-- The actual coefficient inclusion followed by expansion of both variables. -/
def scalarMap (q : ℕ) (hq : q ≠ 0) :
    MvPowerSeries (Fin 2) k₀ →+* MvPowerSeries (Fin 2) k :=
  (expand q hq).toRingHom.comp (MvPowerSeries.map (algebraMap k₀ k))

@[simp]
theorem scalarMap_apply (q : ℕ) (hq : q ≠ 0) (f : MvPowerSeries (Fin 2) k₀) :
    scalarMap (k := k) q hq f = expand q hq (MvPowerSeries.map (algebraMap k₀ k) f) :=
  rfl

/-- The scalar structure is explicitly installed from `scalarMap`. -/
@[instance_reducible]
def scalarAlgebra (q : ℕ) (hq : q ≠ 0) :
    Algebra (MvPowerSeries (Fin 2) k₀) (MvPowerSeries (Fin 2) k) :=
  (scalarMap (k₀ := k₀) (k := k) q hq).toAlgebra

/-- A coefficient-basis index together with the two exponent residues. -/
abbrev Index (D : Type*) (q : ℕ) := D × (Fin 2 → Fin q)

/-- A pair of residues as the exponent vector of a literal monomial. -/
def residue {q : ℕ} (r : Fin 2 → Fin q) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (r i : ℕ)

@[simp]
theorem residue_apply {q : ℕ} (r : Fin 2 → Fin q) (i : Fin 2) :
    residue r i = (r i : ℕ) := rfl

theorem residue_injective {q : ℕ} :
    Function.Injective (residue (q := q)) := by
  intro r s h
  funext i
  apply Fin.ext
  exact congrArg (fun d : Fin 2 →₀ ℕ => d i) h

/-- Each monomial coefficient is supported in its own exponent residue class. -/
theorem coeff_scalarMap_mul_monomial
    (q : ℕ) (hq : q ≠ 0) (f : MvPowerSeries (Fin 2) k₀) (a : k)
    (r s : Fin 2 → Fin q) (n : Fin 2 →₀ ℕ) :
    coeff (q • n + residue r) (scalarMap q hq f * monomial (residue s) a) =
      if s = r then algebraMap k₀ k (coeff n f) * a else 0 := by
  classical
  by_cases hsr : s = r
  · subst s
    rw [ite_eq_left rfl, coeff_add_mul_monomial, scalarMap_apply,
      coeff_expand_smul, coeff_map]
  · rw [ite_eq_right hsr, coeff_mul_monomial]
    split_ifs with hle
    · obtain ⟨i, hi⟩ : ∃ i, s i ≠ r i := by
        by_contra h
        push Not at h
        exact hsr (funext h)
      have hnd : ¬ q ∣ (q • n + residue r - residue s) i := by
        intro hd
        obtain ⟨m, hm⟩ := hd
        have heq : q * n i + (r i : ℕ) = (s i : ℕ) + q * m := by
          have ht := Nat.sub_add_cancel
            (show residue s i ≤ (q • n + residue r) i from hle i)
          rw [← Finsupp.tsub_apply, hm] at ht
          simpa only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
            residue_apply, add_comm] using ht.symm
        have hmod := congrArg (fun x : ℕ => x % q) heq
        have hrs : (r i : ℕ) = (s i : ℕ) := by
          simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, zero_mul,
            Nat.zero_mod, zero_add, add_zero, Nat.mod_eq_of_lt (r i).isLt,
            Nat.mod_eq_of_lt (s i).isLt] using hmod
        exact hi (Fin.ext hrs.symm)
      rw [scalarMap_apply, coeff_expand_of_not_dvd q hq _ hnd, zero_mul]
    · rfl

/-- The original coefficient-basis monomial. -/
def basisVector (b : Basis D k₀ k) {q : ℕ} (i : Index D q) :
    MvPowerSeries (Fin 2) k :=
  monomial (residue i.2) (b i.1)

theorem basisVector_eq_prod (b : Basis D k₀ k) {q : ℕ} (i : Index D q) :
    basisVector b i = C (b i.1) * ∏ j : Fin 2, (X j) ^ (i.2 j : ℕ) := by
  classical
  rw [basisVector, monomial_eq', Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

/-- Coefficient extraction at `q • n + r`, followed by the given coefficient basis. -/
def coordinates (b : Basis D k₀ k) (q : ℕ) (f : MvPowerSeries (Fin 2) k) :
    Index D q → MvPowerSeries (Fin 2) k₀ :=
  fun i n => b.repr (coeff (q • n + residue i.2) f) i.1

@[simp]
theorem coeff_coordinates (b : Basis D k₀ k) (q : ℕ)
    (f : MvPowerSeries (Fin 2) k) (i : Index D q) (n : Fin 2 →₀ ℕ) :
    coeff n (coordinates b q f i) = b.repr (coeff (q • n + residue i.2) f) i.1 :=
  rfl

section GivenAlgebra

variable [Fintype D]
variable [Algebra (MvPowerSeries (Fin 2) k₀) (MvPowerSeries (Fin 2) k)]

/-- Finite reconstruction is linear for the supplied series scalar structure. -/
def synthesis (b : Basis D k₀ k) (q : ℕ) :
    (Index D q → MvPowerSeries (Fin 2) k₀) →ₗ[MvPowerSeries (Fin 2) k₀]
      MvPowerSeries (Fin 2) k where
  toFun c := ∑ i, c i • basisVector b i
  map_add' c d := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    change (∑ i, (a * c i) • basisVector b i) = a • ∑ i, c i • basisVector b i
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_smul a (c i) (basisVector b i)

@[simp]
theorem synthesis_apply (b : Basis D k₀ k) (q : ℕ)
    (c : Index D q → MvPowerSeries (Fin 2) k₀) :
    synthesis b q c = ∑ i, c i • basisVector b i := rfl

variable (b : Basis D k₀ k) (q : ℕ) (hq : q ≠ 0)
variable (hmap : algebraMap (MvPowerSeries (Fin 2) k₀) (MvPowerSeries (Fin 2) k) =
  scalarMap q hq)

include hmap

/-- A reconstructed coefficient is the finite coefficient-field expansion in its residue class. -/
theorem coeff_synthesis (c : Index D q → MvPowerSeries (Fin 2) k₀)
    (r : Fin 2 → Fin q) (n : Fin 2 →₀ ℕ) :
    coeff (q • n + residue r) (synthesis b q c) =
      ∑ d, algebraMap k₀ k (coeff n (c (d, r))) * b d := by
  classical
  simp only [synthesis_apply, map_sum, Algebra.smul_def, hmap, basisVector,
    coeff_scalarMap_mul_monomial, Fintype.sum_prod_type]
  simp

/-- Extracting all coefficients of a finite reconstruction returns its original coordinates. -/
theorem coordinates_synthesis (c : Index D q → MvPowerSeries (Fin 2) k₀) :
    coordinates b q (synthesis b q c) = c := by
  funext i
  apply MvPowerSeries.ext
  intro n
  rw [coeff_coordinates, coeff_synthesis b q hq hmap]
  simpa only [Algebra.smul_def] using
    congrFun (b.repr_sum_self (fun d => coeff n (c (d, i.2)))) i.1

/-- Every formal series is reconstructed from its coefficientwise coordinates. -/
theorem synthesis_coordinates (f : MvPowerSeries (Fin 2) k) :
    synthesis b q (coordinates b q f) = f := by
  apply MvPowerSeries.ext
  intro m
  let n : Fin 2 →₀ ℕ := m.mapRange (fun a => a / q) (Nat.zero_div q)
  let r : Fin 2 → Fin q := fun i => ⟨m i % q, Nat.mod_lt _ (Nat.pos_of_ne_zero hq)⟩
  have hm : q • n + residue r = m := by
    ext i
    simpa only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
      Finsupp.mapRange_apply, residue_apply, n, r] using Nat.div_add_mod (m i) q
  calc
    coeff m (synthesis b q (coordinates b q f)) =
        coeff (q • n + residue r) (synthesis b q (coordinates b q f)) := by rw [hm]
    _ = ∑ d, algebraMap k₀ k (coeff n (coordinates b q f (d, r))) * b d :=
      coeff_synthesis b q hq hmap _ r n
    _ = coeff (q • n + residue r) f := by
      simpa only [coeff_coordinates, Algebra.smul_def] using
        b.sum_repr (coeff (q • n + residue r) f)
    _ = coeff m f := by rw [hm]

/-- The actual reconstruction map is a linear equivalence with the coefficientwise inverse. -/
def synthesisEquiv :
    (Index D q → MvPowerSeries (Fin 2) k₀) ≃ₗ[MvPowerSeries (Fin 2) k₀]
      MvPowerSeries (Fin 2) k where
  __ := synthesis b q
  invFun := coordinates b q
  left_inv := coordinates_synthesis b q hq hmap
  right_inv := synthesis_coordinates b q hq hmap

/-- A basis for any supplied scalar structure proved equal to the original composite map. -/
def basisOfAlgebraMap :
    Basis (Index D q) (MvPowerSeries (Fin 2) k₀) (MvPowerSeries (Fin 2) k) :=
  Basis.ofEquivFun (synthesisEquiv b q hq hmap).symm

@[simp]
theorem basisOfAlgebraMap_apply (i : Index D q) :
    basisOfAlgebraMap b q hq hmap i = monomial (residue i.2) (b i.1) := by
  classical
  rw [basisOfAlgebraMap, Basis.coe_ofEquivFun]
  change synthesis b q (Pi.single i 1) = basisVector b i
  simp [synthesis_apply, Pi.single_apply]

@[simp]
theorem coeff_basisOfAlgebraMap_repr
    (f : MvPowerSeries (Fin 2) k) (i : Index D q) (n : Fin 2 →₀ ℕ) :
    coeff n ((basisOfAlgebraMap b q hq hmap).repr f i) =
      b.repr (coeff (q • n + residue i.2) f) i.1 := rfl

end GivenAlgebra

section OriginalAlgebra

variable [Fintype D] (b : Basis D k₀ k) (q : ℕ) (hq : q ≠ 0)

/-- The finite monomial basis under the literal coefficient-map/expansion scalar action. -/
def basis :
    letI := scalarAlgebra (k₀ := k₀) (k := k) q hq
    Basis (Index D q) (MvPowerSeries (Fin 2) k₀) (MvPowerSeries (Fin 2) k) := by
  letI := scalarAlgebra (k₀ := k₀) (k := k) q hq
  exact basisOfAlgebraMap b q hq rfl

@[simp]
theorem basis_apply (i : Index D q) :
    basis b q hq i = monomial (residue i.2) (b i.1) := by
  let := scalarAlgebra (k₀ := k₀) (k := k) q hq
  exact basisOfAlgebraMap_apply b q hq rfl i

theorem basis_apply_prod (i : Index D q) :
    basis b q hq i = C (b i.1) * ∏ j : Fin 2, (X j) ^ (i.2 j : ℕ) := by
  rw [basis_apply]
  exact basisVector_eq_prod b i

/-- The basis coordinates retain the literal input coefficient at `q • n + r`. -/
@[simp]
theorem coeff_basis_repr
    (f : MvPowerSeries (Fin 2) k) (i : Index D q) (n : Fin 2 →₀ ℕ) :
    letI := scalarAlgebra (k₀ := k₀) (k := k) q hq
    coeff n ((basis b q hq).repr f i) =
      b.repr (coeff (q • n + residue i.2) f) i.1 := by
  let := scalarAlgebra (k₀ := k₀) (k := k) q hq
  exact coeff_basisOfAlgebraMap_repr b q hq rfl f i n

end OriginalAlgebra

section Finite

variable [Finite D] (b : Basis D k₀ k) (q : ℕ) (hq : q ≠ 0)

include b

/-- Freeness refers to the actual expanded scalar structure. -/
theorem module_free :
    letI := scalarAlgebra (k₀ := k₀) (k := k) q hq
    Module.Free (MvPowerSeries (Fin 2) k₀) (MvPowerSeries (Fin 2) k) := by
  let := Fintype.ofFinite D
  let := scalarAlgebra (k₀ := k₀) (k := k) q hq
  exact Module.Free.of_basis (basis b q hq)

/-- Finiteness follows from the constructed finite basis, with the same scalar map. -/
theorem module_finite :
    letI := scalarAlgebra (k₀ := k₀) (k := k) q hq
    Module.Finite (MvPowerSeries (Fin 2) k₀) (MvPowerSeries (Fin 2) k) := by
  let := Fintype.ofFinite D
  let := scalarAlgebra (k₀ := k₀) (k := k) q hq
  exact Module.Finite.of_basis (basis b q hq)

end Finite

end FiniteCoefficientExpansion
end MvPowerSeries
