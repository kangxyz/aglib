/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.LocalRing.ResidueTensor
public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Cyclic module presentations under localization

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/SmoothIdeal.lean`, SHA-256
  `1e1f564e4d5d68f6f673a435f935642b06c6faeca7632d110bc71565993a96e4`.

Actual objects, maps, universes and stated conditions are retained.
Native proof validation is pending the coordinated build.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open TensorProduct
open LinearMap

section
namespace Module

/-- A finite module cyclic at a prime has a single-generator presentation on
some principal neighbourhood of that prime. -/
theorem exists_away_surjective_unit_of_localized_surjective_unit
    (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : Ideal R) [p.IsPrime]
    (f : Localization.AtPrime p →ₗ[Localization.AtPrime p] LocalizedModule p.primeCompl M)
    (hf : Function.Surjective f) :
    ∃ s : R, s ∉ p ∧ ∃ a : M,
      Function.Surjective (LocalizedModule.map (Submonoid.powers s)
        (LinearMap.toSpanSingleton R M a)) := by
  obtain ⟨g, _, _, hg⟩ := Module.exists_localizedMap_surjective_of_surjective p.primeCompl
    (Algebra.linearMap R (Localization.AtPrime p))
    (LocalizedModule.mkLinearMap p.primeCompl M) (ϕ := f.restrictScalars R) hf
  have hmap : IsLocalizedModule.map p.primeCompl
      (Algebra.linearMap R (Localization.AtPrime p))
      (LocalizedModule.mkLinearMap p.primeCompl M) g =
      ((LocalizedModule.map p.primeCompl g).restrictScalars R).comp
        (IsLocalizedModule.iso p.primeCompl (Algebra.linearMap R (Localization.AtPrime
          p))).symm.toLinearMap := by
    apply IsLocalizedModule.linearMap_ext p.primeCompl
      (Algebra.linearMap R (Localization.AtPrime p))
      (LocalizedModule.mkLinearMap p.primeCompl M)
    rw [LinearMap.comp_assoc, IsLocalizedModule.iso_symm_comp, IsLocalizedModule.map_comp]
    apply LinearMap.ext
    intro r
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk]
  have hg' : Function.Surjective (LocalizedModule.map p.primeCompl g) := by
    rw [hmap] at hg
    exact Function.Surjective.of_comp hg
  obtain ⟨s, hs, hgs⟩ :=
    Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective p g hg'
  have he : g = LinearMap.toSpanSingleton R M (g 1) := by
    apply LinearMap.ext
    intro r
    simpa using g.map_smul r 1
  exact ⟨s, hs, g 1, he ▸ hgs⟩

end Module
end

section
namespace LocalizedModule

/-- Localization preserves an actual module isomorphism. -/
def localizedModuleEquiv {R M N : Type u} [CommRing R] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] (S : Submonoid R) (e : M ≃ₗ[R] N) :
    LocalizedModule S M ≃ₗ[Localization S] LocalizedModule S N :=
  (LocalizedModule.equivTensorProduct S M).trans
    ((AlgebraTensorModule.congr (LinearEquiv.refl (Localization S) (Localization S)) e).trans
      (LocalizedModule.equivTensorProduct S N).symm)

end LocalizedModule
end

section
namespace Ideal

/-- Surjectivity from the unit module identifies an ideal with the span of
the value of one. -/
theorem ideal_eq_span_of_surjective_unit
    {R : Type u} [CommRing R] (I : Ideal R) (f : R →ₗ[R] I)
    (hf : Function.Surjective f) : I = Ideal.span {(f 1).val} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨r, hr⟩ := hf ⟨x, hx⟩
    rw [Ideal.mem_span_singleton']
    refine ⟨r, ?_⟩
    have h : f r = r • f 1 := by simpa using f.map_smul r 1
    have := congrArg Subtype.val (h.symm.trans hr)
    simpa only [Submodule.coe_smul_of_tower, smul_eq_mul] using this
  · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (f 1).property)

/-- A localized singleton presentation yields the literal principal ideal
inside the localized ring. -/
theorem idealMap_eq_span_of_localized_surjective
    {R : Type u} [CommRing R] (I : Ideal R) (s : Submonoid R) (a : I)
    (hg : Function.Surjective (LocalizedModule.map s (LinearMap.toSpanSingleton R I a))) :
    I.map (algebraMap R (Localization s)) =
      Ideal.span {algebraMap R (Localization s) a.val} := by
  let Rs := Localization s
  let J := I.map (algebraMap R Rs)
  let u := Algebra.linearMap R Rs
  let v := Algebra.idealMap Rs I
  let g := LinearMap.toSpanSingleton R I a
  let f : Rs →ₗ[Rs] J := IsLocalizedModule.mapExtendScalars s u v Rs g
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := hg ((IsLocalizedModule.iso s v).symm y)
    refine ⟨IsLocalizedModule.iso s u x, ?_⟩
    have hm := congrFun (LocalizedModule.coe_map_eq u v g) x
    rw [hx] at hm
    exact (IsLocalizedModule.iso s v).symm.injective hm.symm
  have h1 : f 1 = v a := by
    change (IsLocalizedModule.map s u v g) 1 = v a
    have h := IsLocalizedModule.map_apply s u v g 1
    simpa [u, g] using h
  change J = Ideal.span {algebraMap R Rs a.val}
  rw [_root_.Ideal.ideal_eq_span_of_surjective_unit J f hf, h1]
  rfl

end Ideal
end
