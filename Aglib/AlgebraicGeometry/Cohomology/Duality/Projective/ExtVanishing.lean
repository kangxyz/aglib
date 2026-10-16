/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Higher

/-!
# Coherent-source Ext into the projective dualizing twist above the dimension

The original degree-zero cohomology injection dualizes surjectively over a field.
Canonical Serre duality transfers this to the original Ext row, proving vanishing in
one degree above the dimension. Actual coherent negative-twist presentations then give
all higher degrees by native dimension shifting. No assertion about arbitrary
noncoherent source modules or an ambient injective dimension is made.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (K : Type u) [Field K] (ι : Type u) [Fintype ι]

/-- Actual H⁰ injectivity and canonical duality annihilate the original top Ext boundary
of a short exact presentation with coherent first two terms. -/
theorem projectiveDualizingExt_succ_dimension_subsingleton_of_shortExact
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (S : ShortComplex (ProjectiveSpace K ι).Modules) (hS : S.ShortExact)
    (h₁ : affineLocallyFiniteType (ProjectiveSpace K ι) S.X₁)
    (h₂ : affineLocallyFiniteType (ProjectiveSpace K ι) S.X₂)
    (hE : Subsingleton (Ext.{u + 1} (C := (ProjectiveSpace K ι).Modules)
      S.X₂ (twistingSheaf K ι (-(Fintype.card ι : ℤ))) (n + 1))) :
    Subsingleton (Ext.{u + 1} (C := (ProjectiveSpace K ι).Modules)
      S.X₃ (twistingSheaf K ι (-(Fintype.card ι : ℤ))) (n + 1)) := by
  let α : K →+* Γ(ProjectiveSpace K ι, ⊤) :=
    (toSpec K ι).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let := moduleCategoryLinearOfHom (ProjectiveSpace K ι) α
  let := moduleCohomologyModuleOfHom (ProjectiveSpace K ι) α S.X₁ 0
  let := moduleCohomologyModuleOfHom (ProjectiveSpace K ι) α S.X₂ 0
  let : Mono S.f := hS.mono_f
  let ω := twistingSheaf K ι (-(Fintype.card ι : ℤ))
  let f := moduleCohomologyMapOfHom (ProjectiveSpace K ι) α S.f 0
  let p₁ := projectiveSerrePairing K ι n e S.X₁ 0 n (Nat.zero_add n)
  let p₂ := projectiveSerrePairing K ι n e S.X₂ 0 n (Nat.zero_add n)
  let ε := (Ext.mk₀ (C := (ProjectiveSpace K ι).Modules) S.f).precompOfLinear K ω
    (Nat.zero_add n)
  let Δ := hS.extClass.precompOfLinear (C := (ProjectiveSpace K ι).Modules)
    K ω (show 1 + n = n + 1 by omega)
  have hp₁ : Function.Bijective p₁ :=
    projectiveSerrePairing_bijective K ι n e S.X₁ h₁ 0 n (Nat.zero_add n)
  have hp₂ : Function.Bijective p₂ :=
    projectiveSerrePairing_bijective K ι n e S.X₂ h₂ 0 n (Nat.zero_add n)
  have hsquare : p₁.comp ε = f.dualMap.comp p₂ := by
    ext y x
    exact projectiveSerrePairing_naturality K ι n e S.f 0 n (Nat.zero_add n) y x
  have hεsurj : Function.Surjective ε := by
    have hcomp : Function.Surjective (p₁.comp ε) := by
      rw [hsquare]
      exact (LinearMap.dualMap_surjective_of_injective
        (moduleH0MapOfHom_injective (ProjectiveSpace K ι) α S.f)).comp hp₂.surjective
    exact Function.Surjective.of_comp_left (f := p₁) (g := ε) hcomp hp₁.injective
  have hεδ : Function.Exact ε Δ :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      (Ext.contravariant_sequence_exact₁' (C := (ProjectiveSpace K ι).Modules)
        hS ω n (n + 1) (by omega))
  have hΔzero : Δ = 0 := (LinearMap.surjective_iff_eq_zero_of_exact hεδ).mp hεsurj
  have hΔsurj : Function.Surjective Δ := by
    intro x
    exact Ext.contravariant_sequence_exact₃ (C := (ProjectiveSpace K ι).Modules)
      hS ω x (hE.elim _ 0) (show 1 + n = n + 1 by omega)
  have hz (x : Ext.{u + 1} (C := (ProjectiveSpace K ι).Modules) S.X₃ ω (n + 1)) :
      x = 0 := by
    obtain ⟨y, hy⟩ := hΔsurj x
    rw [hΔzero, LinearMap.zero_apply] at hy
    exact hy.symm
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- Every coherent source has zero native Ext into the dualizing twist one degree above
the projective dimension, including dimension zero. -/
theorem projectiveDualizingExt_succ_dimension_subsingleton
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace K ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace K ι) M) :
    Subsingleton (Ext.{u + 1} (C := (ProjectiveSpace K ι).Modules)
      M (twistingSheaf K ι (-(Fintype.card ι : ℤ))) (n + 1)) := by
  obtain ⟨N, hN, I, hI, π, hS, hKer⟩ :=
    exists_uniformNegativeTwistCoherentPresentation K ι M hM (Fintype.card ι)
  let := hI
  exact projectiveDualizingExt_succ_dimension_subsingleton_of_shortExact K ι n e
    (ShortComplex.kernelSequence π) hS hKer
    (twistingCoproduct_affineLocallyFiniteType K ι (fun _ : I => -(N : ℤ)))
    (negativeTwistCoproductExt_dualizing_subsingleton K ι n e
      (fun _ : I => N) (fun _ => hN) (n + 1) (by omega))

/-- All native Ext groups from a coherent source into the original dualizing twist vanish
strictly above the projective dimension. -/
theorem projectiveDualizingExt_subsingleton_of_gt
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace K ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace K ι) M)
    (q : ℕ) (hq : n < q) :
    Subsingleton (Ext.{u + 1} (C := (ProjectiveSpace K ι).Modules)
      M (twistingSheaf K ι (-(Fintype.card ι : ℤ))) q) := by
  induction q using Nat.strong_induction_on generalizing M with
  | h q ih =>
    by_cases hqeq : q = n + 1
    · subst q
      exact projectiveDualizingExt_succ_dimension_subsingleton K ι n e M hM
    · obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show q ≠ 0 by omega)
      obtain ⟨N, hN, I, hI, π, hS, hKer⟩ :=
        exists_uniformNegativeTwistCoherentPresentation K ι M hM (Fintype.card ι)
      let := hI
      let ω := twistingSheaf K ι (-(Fintype.card ι : ℤ))
      let : Subsingleton (Ext.{u + 1} (C := (ProjectiveSpace K ι).Modules)
          (kernel π) ω r) := ih r (by omega) (kernel π) hKer (by omega)
      have hP := negativeTwistCoproductExt_dualizing_subsingleton K ι n e
        (fun _ : I => N) (fun _ => hN) (r + 1) (by omega)
      let Δ : Ext.{u + 1} (C := (ProjectiveSpace K ι).Modules) (kernel π) ω r →+
          Ext.{u + 1} (C := (ProjectiveSpace K ι).Modules) M ω (r + 1) :=
        hS.extClass.precomp ω (show 1 + r = r + 1 by omega)
      have hΔsurj : Function.Surjective Δ := by
        intro x
        exact Ext.contravariant_sequence_exact₃ (C := (ProjectiveSpace K ι).Modules)
          hS ω x (hP.elim _ 0) (show 1 + r = r + 1 by omega)
      exact hΔsurj.subsingleton

/-- Native Ext from a coherent source into the dualizing twist is finite over the original
base field in every nonnegative degree. -/
theorem projectiveDualizingExt_finite (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M : (ProjectiveSpace K ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace K ι) M) (q : ℕ) :
    let α : K →+* Γ(ProjectiveSpace K ι, ⊤) :=
      (toSpec K ι).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
    letI := moduleCategoryLinearOfHom (ProjectiveSpace K ι) α
    Module.Finite K (Ext.{u + 1} (C := (ProjectiveSpace K ι).Modules)
      M (twistingSheaf K ι (-(Fintype.card ι : ℤ))) q) := by
  let α : K →+* Γ(ProjectiveSpace K ι, ⊤) :=
    (toSpec K ι).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let := moduleCategoryLinearOfHom (ProjectiveSpace K ι) α
  by_cases hq : q ≤ n
  · let := moduleCohomologyModuleOfHom (ProjectiveSpace K ι) α M (n - q)
    let : Module.Finite K
        (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace K ι) M) (n - q)) :=
      projectiveCohomology_finite K ι n e M hM (n - q)
    exact Module.Finite.equiv
      (projectiveSerreDuality K ι n e M hM (n - q) q (Nat.sub_add_cancel hq)).symm
  · let := projectiveDualizingExt_subsingleton_of_gt K ι n e M hM q (by omega)
    infer_instance

end AlgebraicGeometry.Scheme.Cohomology
