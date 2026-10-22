/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.SeparablyGenerated.FrobeniusCoefficients
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Finite Frobenius independence characterizes geometric reducedness

The argument uses only finite coefficient spaces and finite tensor supports.
The base and extension fields retain independent universes and their supplied
algebra map. No finite imperfection degree or global separating basis is used.
-/

open scoped TensorProduct
open TensorProduct

@[expose] public noncomputable section

namespace Algebra

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- The finite, actual-map version of the Frobenius independence criterion. -/
def PreservesFiniteFrobeniusIndependence (p : ℕ) [ExpChar F p] [ExpChar L p] : Prop :=
  ∀ (n : ℕ) (b : Fin n → F),
    LinearIndependent (frobenius F p).fieldRange b →
      LinearIndependent (frobenius L p).fieldRange (fun i => algebraMap F L (b i))

/-- The `Fin n` formulation also applies to finite index types in any universe. -/
theorem PreservesFiniteFrobeniusIndependence.linearIndependent
    (p : ℕ) [ExpChar F p] [ExpChar L p]
    (h : PreservesFiniteFrobeniusIndependence (F := F) (L := L) p)
    {ι : Type*} [Finite ι] {b : ι → F}
    (hb : LinearIndependent (frobenius F p).fieldRange b) :
    LinearIndependent (frobenius L p).fieldRange (fun i => algebraMap F L (b i)) := by
  classical
  let := Fintype.ofFinite ι
  let e := (Fintype.equivFin ι).symm
  exact (linearIndependent_equiv e).mp (h _ (b ∘ e) (hb.comp e e.injective))

/-- Finite coefficient independence implies preservation of independence by
raising the extension-field vectors to the characteristic power. -/
theorem linearIndependent_pow_of_finiteFrobeniusIndependence
    (p : ℕ) (hp : p.Prime) [ExpChar F p] [ExpChar L p]
    (h : PreservesFiniteFrobeniusIndependence (F := F) (L := L) p)
    {ι : Type*} [Finite ι] {v : ι → L} (hv : LinearIndependent F v) :
    LinearIndependent F (fun i => v i ^ p) := by
  classical
  let := Fintype.ofFinite ι
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  let P := (frobenius F p).fieldRange
  let W := Submodule.span P (Set.range c)
  let : FiniteDimensional P W := FiniteDimensional.span_of_finite P (Set.finite_range c)
  let B := Module.finBasis P W
  let b : Fin (Module.finrank P W) → F := fun j => (B j : F)
  have hb : LinearIndependent P b :=
    B.linearIndependent.map' W.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  let w (i : ι) : W := ⟨c i, Submodule.subset_span (Set.mem_range_self i)⟩
  let d (i : ι) (j : Fin (Module.finrank P W)) : P := B.repr (w i) j
  have hd (i : ι) : ∑ j, (d i j : F) * b j = c i := by
    have hh := congrArg (fun z : W => (z : F)) (B.sum_repr (w i))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hh
    change ∑ j, (d i j : F) * b j = c i at hh
    exact hh
  have hroot (i : ι) (j : Fin (Module.finrank P W)) :
      ∃ z : F, z ^ p = (d i j : F) := by
    have hh := (d i j).property
    change ∃ z : F, frobenius F p z = (d i j : F) at hh
    simpa only [frobenius_def] using hh
  choose q hq using hroot
  have hqsum (i : ι) : ∑ j, q i j ^ p * b j = c i := by
    simpa only [hq] using hd i
  let z (j : Fin (Module.finrank P W)) : L :=
    ∑ i, algebraMap F L (q i j) * v i
  have hzpow (j : Fin (Module.finrank P W)) :
      z j ^ p = ∑ i, (algebraMap F L (q i j)) ^ p * v i ^ p := by
    simpa only [z, mul_pow] using
      (sum_pow_char p Finset.univ (fun i => algebraMap F L (q i j) * v i))
  have hrel : ∑ j, z j ^ p * algebraMap F L (b j) = 0 := by
    calc
      _ = ∑ j, ∑ i, (algebraMap F L (q i j)) ^ p * v i ^ p *
          algebraMap F L (b j) := by simp only [hzpow, Finset.sum_mul]
      _ = ∑ i, ∑ j, algebraMap F L (q i j ^ p * b j) * v i ^ p := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        simp only [map_mul, map_pow]
        ring
      _ = ∑ i, algebraMap F L (c i) * v i ^ p := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.sum_mul, ← map_sum, hqsum]
      _ = 0 := by simpa only [Algebra.smul_def] using hc
  let zp (j : Fin (Module.finrank P W)) : (frobenius L p).fieldRange :=
    (frobenius L p).rangeRestrictField (z j)
  have hz0 : ∀ j, zp j = 0 :=
    Fintype.linearIndependent_iff.mp (h _ b hb) zp (by
      change ∑ j, z j ^ p * algebraMap F L (b j) = 0
      exact hrel)
  have hz (j : Fin (Module.finrank P W)) : z j = 0 := by
    have hh : z j ^ p = 0 := congrArg Subtype.val (hz0 j)
    exact eq_zero_of_pow_eq_zero hh
  have hq0 (j : Fin (Module.finrank P W)) : ∀ i, q i j = 0 :=
    Fintype.linearIndependent_iff.mp hv (fun i => q i j) (by
      simpa only [Algebra.smul_def] using hz j)
  intro i
  rw [← hqsum i]
  simp only [hq0, zero_pow hp.ne_zero, zero_mul, Finset.sum_const_zero]

/-- Finite independence of characteristic powers suffices for reducedness
of the algebraic-closure tensor. This is a direct finite-support argument. -/
theorem isGeometricallyReduced_of_linearIndependent_pow
    (p : ℕ) (hp : p.Prime) [ExpChar F p]
    (h : ∀ (n : ℕ) (v : Fin n → L), LinearIndependent F v →
      LinearIndependent F (fun i => v i ^ p)) :
    IsGeometricallyReduced F L := by
  classical
  let A := AlgebraicClosure F
  let D := A ⊗[F] L
  let : ExpChar A p := expChar_of_injective_algebraMap
    (RingHom.injective (algebraMap F A)) p
  let : ExpChar D p := expChar_of_injective_ringHom
    (Algebra.TensorProduct.includeLeft_injective (R := F) (S := F)
      (A := A) (B := L) (RingHom.injective (algebraMap F L))) p
  apply (isGeometricallyReduced_field_iff F L).mpr
  apply (isReduced_iff_pow_one_lt p hp.one_lt).mpr
  intro x hx
  let B := Module.Free.chooseBasis F L
  obtain ⟨c, hc⟩ := TensorProduct.eq_repr_basis_right B x
  let v : c.support → L := fun i => B i
  have hv : LinearIndependent F v := B.linearIndependent.comp _ Subtype.val_injective
  let e := (Fintype.equivFin c.support).symm
  have hvp : LinearIndependent F (fun i : c.support => v i ^ p) :=
    (linearIndependent_equiv e).mp (h _ (v ∘ e) (hv.comp e e.injective))
  have hrep : (∑ i : c.support, c i ⊗ₜ[F] v i : D) = x := by
    rw [Finsupp.sum, ← Finset.sum_coe_sort c.support] at hc
    exact hc
  have hpow : (∑ i : c.support, (c i ^ p) ⊗ₜ[F] (v i ^ p) : D) = 0 := by
    rw [← hrep] at hx
    simpa only [sum_pow_char, Algebra.TensorProduct.tmul_pow] using hx
  have ht : LinearIndependent A (fun i : c.support => (1 : A) ⊗ₜ[F] (v i ^ p)) :=
    Module.Flat.linearIndependent_one_tmul hvp
  have hc0 : ∀ i : c.support, c i ^ p = 0 :=
    Fintype.linearIndependent_iff.mp ht (fun i => c i ^ p) (by
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using hpow)
  rw [← hrep]
  apply Finset.sum_eq_zero
  intro i hi
  rw [eq_zero_of_pow_eq_zero (hc0 i), TensorProduct.zero_tmul]

/-- The reverse field criterion, for the actual supplied scalar action. -/
theorem isGeometricallyReduced_of_finiteFrobeniusIndependence
    (p : ℕ) (hp : p.Prime) [ExpChar F p] [ExpChar L p]
    (h : PreservesFiniteFrobeniusIndependence (F := F) (L := L) p) :
    IsGeometricallyReduced F L := by
  apply isGeometricallyReduced_of_linearIndependent_pow p hp
  intro n v hv
  exact linearIndependent_pow_of_finiteFrobeniusIndependence p hp h hv

/-- Geometric reducedness is equivalent to finite Frobenius coefficient
independence, without any finiteness hypothesis on the fields. -/
theorem isGeometricallyReduced_iff_finiteFrobeniusIndependence
    (p : ℕ) (hp : p.Prime) [ExpChar F p] [ExpChar L p] :
    IsGeometricallyReduced F L ↔
      PreservesFiniteFrobeniusIndependence (F := F) (L := L) p := by
  constructor
  · intro h
    let := h
    intro n b hb
    exact linearIndependent_frobeniusFieldRange_map_of_geometricallyReduced p hp hb
  · exact isGeometricallyReduced_of_finiteFrobeniusIndependence p hp

/-- Composition uses the actual scalar tower, not abstract field identifications. -/
theorem PreservesFiniteFrobeniusIndependence.trans
    {M : Type*} [Field M] [Algebra F M] [Algebra L M] [IsScalarTower F L M]
    (p : ℕ) [ExpChar F p] [ExpChar L p] [ExpChar M p]
    (hFL : PreservesFiniteFrobeniusIndependence (F := F) (L := L) p)
    (hLM : PreservesFiniteFrobeniusIndependence (F := L) (L := M) p) :
    PreservesFiniteFrobeniusIndependence (F := F) (L := M) p := by
  intro n b hb
  simpa only [← IsScalarTower.algebraMap_apply F L M] using
    hLM n (fun i => algebraMap F L (b i)) (hFL n b hb)

end Algebra
