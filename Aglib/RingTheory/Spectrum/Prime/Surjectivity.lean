/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Spectrum.Prime.Module

/-!
# Open surjectivity loci for residue-field base change

For a linear map with finite target, surjectivity on a residue-field fibre
is equivalent to the corresponding prime lying outside the support of the
original cokernel. This also identifies surjectivity of the original
localized map. The locus is open and every one of its points has a basic
open neighbourhood on which all residue-field maps are surjective.
No Noetherianity or finiteness of the source is required.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct

namespace LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Module.Finite R N]

/-- Residue-field surjectivity is the complement of the actual cokernel support. -/
theorem residueField_baseChange_surjective_iff_notMem_support
    (f : M →ₗ[R] N) (p : PrimeSpectrum R) :
    Function.Surjective (f.baseChange p.asIdeal.ResidueField) ↔
      p ∉ Module.support R (N ⧸ f.range) := by
  let K := p.asIdeal.ResidueField
  have hex := lTensor_exact K f.exact_map_mkQ_range (Submodule.mkQ_surjective f.range)
  have hsurj := (f.range.mkQ).lTensor_surjective K (Submodule.mkQ_surjective f.range)
  have hzero : Function.Surjective (f.lTensor K) ↔
      Subsingleton (K ⊗[R] (N ⧸ f.range)) := by
    rw [surjective_iff_eq_zero_of_exact hex]
    constructor
    · intro h
      have hz (z : K ⊗[R] (N ⧸ f.range)) : z = 0 := by
        obtain ⟨y, rfl⟩ := hsurj z
        exact DFunLike.congr_fun h y
      exact ⟨fun x y => (hz x).trans (hz y).symm⟩
    · intro h
      let := h
      ext x
      exact Subsingleton.elim _ _
  change Function.Surjective (f.lTensor K) ↔ _
  rw [hzero, ← not_nontrivial_iff_subsingleton,
    ← Module.mem_support_iff_nontrivial_residueField_tensorProduct]

/-- The localized map and its residue-field map have the same surjectivity condition. -/
theorem localizedMap_surjective_iff_residueField_baseChange_surjective
    (f : M →ₗ[R] N) (p : PrimeSpectrum R) :
    Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl f) ↔
      Function.Surjective (f.baseChange p.asIdeal.ResidueField) := by
  rw [localizedMap_surjective_iff_subsingleton_localized_coker,
    ← Module.notMem_support_iff, residueField_baseChange_surjective_iff_notMem_support]

/-- Fibrewise surjectivity of a linear map with finite target is an open condition. -/
theorem isOpen_surjective_residueField_baseChange (f : M →ₗ[R] N) :
    IsOpen {p : PrimeSpectrum R |
      Function.Surjective (f.baseChange p.asIdeal.ResidueField)} := by
  have he : {p : PrimeSpectrum R |
      Function.Surjective (f.baseChange p.asIdeal.ResidueField)} =
      (Module.support R (N ⧸ f.range))ᶜ := by
    ext p
    exact residueField_baseChange_surjective_iff_notMem_support f p
  rw [he]
  exact (Module.isClosed_support (R := R) (M := N ⧸ f.range)).isOpen_compl

/-- A surjective residue-field map stays surjective on some actual basic open neighbourhood. -/
theorem exists_basicOpen_residueField_baseChange_surjective (f : M →ₗ[R] N)
    (p : PrimeSpectrum R) (hp : Function.Surjective (f.baseChange p.asIdeal.ResidueField)) :
    ∃ r ∉ p.asIdeal, ∀ q ∈ PrimeSpectrum.basicOpen r,
      Function.Surjective (f.baseChange q.asIdeal.ResidueField) := by
  obtain ⟨_, ⟨r, rfl⟩, hpr, hr⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp
      (isOpen_surjective_residueField_baseChange f) p hp
  exact ⟨r, hpr, fun q hq => hr hq⟩

end LinearMap
