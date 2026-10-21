/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.LocalRing.Module

/-!
# One denominator from a spanning residue fiber

If selected elements span the residue fiber of a finite module at a prime,
one element outside that prime multiplies the whole module into their span.
The proof uses the actual quotient module, right exactness of tensor product,
and the native support criterion proved by localized Nakayama. It therefore
supplies a common annihilator, rather than assuming a localization equality.
-/

@[expose] public section

noncomputable section

open TensorProduct

namespace Module

variable {A M ι : Type*} [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- A spanning residue fiber gives one multiplier outside the prime which
puts every module element into the span of the chosen elements. -/
theorem exists_notMem_smul_mem_span_of_residue_span
    (p : PrimeSpectrum A) (v : ι → M)
    (hspan : Submodule.span p.asIdeal.ResidueField
      (Set.range fun i => (1 : p.asIdeal.ResidueField) ⊗ₜ[A] v i) = ⊤) :
    ∃ h : A, h ∉ p.asIdeal ∧ ∀ x : M, h • x ∈ Submodule.span A (Set.range v) := by
  classical
  let K := p.asIdeal.ResidueField
  let N := Submodule.span A (Set.range v)
  let g : K ⊗[A] M →ₗ[K] K ⊗[A] (M ⧸ N) := N.mkQ.baseChange K
  have hker : Submodule.span K (Set.range fun i => (1 : K) ⊗ₜ[A] v i) ≤
      LinearMap.ker g := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change N.mkQ.baseChange K ((1 : K) ⊗ₜ[A] v i) = 0
    rw [LinearMap.baseChange_tmul]
    have hv : N.mkQ (v i) = 0 :=
      (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.subset_span ⟨i, rfl⟩)
    rw [hv, TensorProduct.tmul_zero]
  have hgzero (x : K ⊗[A] M) : g x = 0 := by
    exact hker (hspan.symm ▸ Submodule.mem_top)
  have hgsurj : Function.Surjective g :=
    LinearMap.lTensor_surjective K N.mkQ_surjective
  have : Subsingleton (K ⊗[A] (M ⧸ N)) := by
    constructor
    intro a b
    obtain ⟨x, rfl⟩ := hgsurj a
    obtain ⟨y, rfl⟩ := hgsurj b
    rw [hgzero, hgzero]
  have hnot : p ∉ Module.support A (M ⧸ N) := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    exact not_nontrivial_iff_subsingleton.mpr inferInstance
  have hnotann : ¬ Module.annihilator A (M ⧸ N) ≤ p.asIdeal := by
    exact fun h => hnot (Module.mem_support_iff_of_finite.mpr h)
  obtain ⟨h, hh, hp⟩ := SetLike.not_le_iff_exists.mp hnotann
  refine ⟨h, hp, fun x => ?_⟩
  apply (Submodule.Quotient.mk_eq_zero N).mp
  change N.mkQ (h • x) = 0
  rw [map_smul]
  exact Module.mem_annihilator.mp hh (N.mkQ x)

end Module
