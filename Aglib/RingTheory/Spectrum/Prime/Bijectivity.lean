/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Spectrum.Prime.Surjectivity
public import Mathlib.Algebra.Module.Projective

/-!
# Bijectivity from bijectivity on every residue-field fibre

Let `R` be a commutative ring and `f : M →ₗ[R] N` a linear map. If `N` is finite and
`κ(p) ⊗ f` is surjective for every prime `p`, then `f` is surjective
(`LinearMap.surjective_of_residueField_baseChange_surjective`). If moreover `M` is finite, `N`
is projective and every `κ(p) ⊗ f` is bijective, then `f` is bijective
(`LinearMap.bijective_of_residueField_baseChange_bijective`). No Noetherianity is assumed.

The first statement is Nakayama's lemma at every prime applied to the cokernel
(`Module.subsingleton_of_subsingleton_residueField_tensorProduct`, from Mathlib's
`Module.mem_support_iff_nontrivial_residueField_tensorProduct`). For the second, a section of
the surjection `f` onto the projective `N` splits off the kernel `K` as a direct summand of `M`;
then `K` is finite, `κ(p) ⊗ K → κ(p) ⊗ M` is injective with image killed by the injective
`κ(p) ⊗ f`, so `κ(p) ⊗ K = 0` for every `p` and `K = 0`
(`LinearMap.injective_of_surjective_of_residueField_baseChange_injective`). Its hypotheses differ
from those of `LinearMap.injective_of_residueField_baseChange_injective` (`FiberInjectivity`),
which needs a free source over a reduced ring but no surjectivity or finiteness.

This is the Nakayama step in the proof of the universal property of the flattening
stratification, Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1,
Thm 4.3 (ii), pp. 22–23: a map of finite modules with projective target that is an isomorphism
on every fibre is an isomorphism.
-/

@[expose] public section

noncomputable section

open TensorProduct

namespace Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- **Nakayama at every prime**: a finite module whose residue-field fibres all vanish is
zero. -/
theorem subsingleton_of_subsingleton_residueField_tensorProduct
    (h : ∀ p : PrimeSpectrum R, Subsingleton (p.asIdeal.ResidueField ⊗[R] M)) :
    Subsingleton M := by
  rw [← Module.support_eq_empty_iff (R := R), Set.eq_empty_iff_forall_notMem]
  intro p hp
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hp
  exact not_nontrivial_iff_subsingleton.mpr (h p) hp

end Module

namespace LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]

/-- A linear map to a finite module that is surjective on every residue-field fibre is
surjective. -/
theorem surjective_of_residueField_baseChange_surjective [Module.Finite R N] (f : M →ₗ[R] N)
    (h : ∀ p : PrimeSpectrum R, Function.Surjective (f.baseChange p.asIdeal.ResidueField)) :
    Function.Surjective f := by
  have hs : Subsingleton (N ⧸ LinearMap.range f) := by
    rw [← Module.support_eq_empty_iff (R := R), Set.eq_empty_iff_forall_notMem]
    exact fun p => (residueField_baseChange_surjective_iff_notMem_support f p).mp (h p)
  exact LinearMap.range_eq_top.mp (Submodule.Quotient.subsingleton_iff.mp hs)

/-- A surjective linear map from a finite module onto a projective module that is injective on
every residue-field fibre is injective. -/
theorem injective_of_surjective_of_residueField_baseChange_injective [Module.Finite R M]
    [Module.Projective R N] (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (h : ∀ p : PrimeSpectrum R, Function.Injective (f.baseChange p.asIdeal.ResidueField)) :
    Function.Injective f := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let K := LinearMap.ker f
  let ρ : M →ₗ[R] M := LinearMap.id - s.comp f
  have hmem (x : M) : ρ x ∈ K := by
    change f (x - s (f x)) = 0
    rw [map_sub, ← LinearMap.comp_apply f s, hs, LinearMap.id_apply, sub_self]
  let π : M →ₗ[R] K := LinearMap.codRestrict K ρ hmem
  have hπι : π.comp K.subtype = LinearMap.id := by
    ext k
    change (k : M) - s (f k) = k
    rw [show f k = 0 from k.2, map_zero, sub_zero]
  have hπ : Function.Surjective π := fun k => ⟨k, LinearMap.congr_fun hπι k⟩
  have : Module.Finite R K := Module.Finite.of_surjective π hπ
  have hfι : f.comp K.subtype = 0 := by
    ext k
    exact k.2
  have hK : Subsingleton K := by
    refine Module.subsingleton_of_subsingleton_residueField_tensorProduct (R := R) fun p => ?_
    let k := p.asIdeal.ResidueField
    have h₁ (z : k ⊗[R] K) : π.baseChange k (K.subtype.baseChange k z) = z := by
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hπι, LinearMap.baseChange_id,
        LinearMap.id_apply]
    have h₂ (z : k ⊗[R] K) : f.baseChange k (K.subtype.baseChange k z) = 0 := by
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hfι, LinearMap.baseChange_zero,
        LinearMap.zero_apply]
    have h₃ (z : k ⊗[R] K) : z = 0 := by
      have hz : K.subtype.baseChange k z = 0 :=
        h p ((h₂ z).trans (map_zero (f.baseChange k)).symm)
      rw [← h₁ z, hz, map_zero]
    exact ⟨fun a b => (h₃ a).trans (h₃ b).symm⟩
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.eq_bot_of_subsingleton

/-- **A fibrewise isomorphism onto a finite projective module is an isomorphism**: a linear map
of finite modules with projective target that is bijective on every residue-field fibre is
bijective. -/
theorem bijective_of_residueField_baseChange_bijective [Module.Finite R M] [Module.Finite R N]
    [Module.Projective R N] (f : M →ₗ[R] N)
    (h : ∀ p : PrimeSpectrum R, Function.Bijective (f.baseChange p.asIdeal.ResidueField)) :
    Function.Bijective f := by
  have hsurj := surjective_of_residueField_baseChange_surjective f fun p => (h p).2
  exact ⟨injective_of_surjective_of_residueField_baseChange_injective f hsurj fun p => (h p).1,
    hsurj⟩

end LinearMap
