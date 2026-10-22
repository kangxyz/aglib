/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Exact.Modules
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Comparison
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars.Open
public import Aglib.AlgebraicGeometry.Modules.Linear
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Cohomology kernels bounded by section comparison cokernels

Injectivity of the original punctured-open H1 restriction detects sections of
the quotient in an actual short exact coefficient sequence. An injective
comparison of those sections then bounds the actual kernel in H1 by its
comparison cokernel. These are the diagram and length steps in Stacks 0AXJ.

The geometric restriction-injectivity theorem, the construction of the strict
transform and its finite normalization, and finite normalization colength are
not assumed silently or supplied by a resolution-existence predicate.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u v

private theorem openHomEquiv_zero (X : Scheme.{u}) (U : X.Opens)
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    additiveOpenHomEquiv X U A 0 = 0 := by
  simpa using additiveOpenHomEquiv_naturality_coefficient X U
    (𝟙 ((additiveOpenFreeFunctor X).obj U))
    (0 : (additiveOpenFreeFunctor X).obj U ⟶ A)

/-- The original H1 restriction controls an actual section comparison.
The first kernel condition says that comparison-zero sections vanish on the
chosen open. The second says that the comparison is faithful on sections
coming from the original middle coefficient. -/
theorem sectionComparison_injective_of_h1Restriction
    (X : Scheme.{u}) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (U : X.Opens) {N : Type v} [AddCommGroup N]
    (ρ : S.X₃.val.obj (op ⊤) →+ N)
    (hH : Function.Injective
      (((moduleAddSheaf X S.X₁).cohomologyPresheaf 1).map
        (homOfLE (show U ≤ ⊤ from le_top)).op))
    (hU : ∀ s, ρ s = 0 →
      S.X₃.val.map (homOfLE (show U ≤ ⊤ from le_top)).op s = 0)
    (hbase : ∀ t, ρ (S.g.val.app (op ⊤) t) = 0 → S.g.val.app (op ⊤) t = 0) :
    Function.Injective ρ := by
  apply (injective_iff_map_eq_zero ρ).mpr
  intro s hs
  let T := moduleCoefficientSequence X S
  have hT : T.ShortExact := moduleCoefficientSequence_shortExact X S hS
  let k : U ⟶ (⊤ : X.Opens) := homOfLE le_top
  let r := (additiveOpenFreeFunctor X).map k
  let t := (additiveOpenHomEquiv X ⊤ T.X₃).symm s
  have ht : additiveOpenHomEquiv X ⊤ T.X₃ t = s := Equiv.apply_symm_apply _ _
  have hrt : r ≫ t = 0 := by
    apply (additiveOpenHomEquiv X U T.X₃).injective
    rw [openHomEquiv_zero, additiveOpenHomEquiv_naturality, ht]
    exact hU s hs
  let ξ : Sheaf.H'.{u + 1} T.X₁ 1 ⊤ :=
    (Ext.mk₀ t).comp hT.extClass rfl
  have hξ : ξ = 0 := by
    apply hH
    rw [map_zero]
    change (Ext.mk₀ r).comp ((Ext.mk₀ t).comp hT.extClass rfl) (Nat.zero_add 1) = 0
    rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, hrt,
      Ext.mk₀_zero, Ext.zero_comp]
  obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₃
    ((additiveOpenFreeFunctor X).obj ⊤) hT (Ext.mk₀ t) rfl hξ
  have hat : Ext.addEquiv₀ a ≫ T.g = t := by
    apply (Ext.mk₀_bijective _ _).injective
    rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_addEquiv₀_apply]
    exact ha
  let a' := additiveOpenHomEquiv X ⊤ T.X₂ (Ext.addEquiv₀ a)
  have has : S.g.val.app (op ⊤) a' = s := by
    change T.g.hom.app (op ⊤) a' = s
    rw [← additiveOpenHomEquiv_naturality_coefficient, hat, ht]
  rw [← has]
  exact hbase a' (has.symm ▸ hs)

private theorem quotient_length_le_of_injective
    {R : Type*} [CommRing R] {M V N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup V] [Module R V]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] V) (ι : V →ₗ[R] N) (hι : Function.Injective ι) :
    Module.length R (V ⧸ LinearMap.range f) ≤
      Module.length R (N ⧸ LinearMap.range (ι.comp f)) := by
  let q := (LinearMap.range f).mapQ (LinearMap.range (ι.comp f)) ι (by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩)
  apply Module.length_le_of_injective q
  apply (injective_iff_map_eq_zero q).mpr
  intro z hz
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range f) z
  have hv : ι v ∈ LinearMap.range (ι.comp f) := by
    exact (Submodule.Quotient.mk_eq_zero _).mp hz
  obtain ⟨x, hx⟩ := hv
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨x, hι hx⟩

/-- The actual connecting sequence bounds its H1 kernel by the cokernel
of an injective comparison on original quotient sections. The scalar ring
is the supplied original ring map to global functions. -/
theorem h1Kernel_length_le_sectionComparison
    (X : Scheme.{u}) {R : Type u} [CommRing R] (α : R →+* Γ(X, ⊤))
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    {N : Type v} [AddCommGroup N] [Module R N]
    (ι : letI : Module R (S.X₃.val.obj (op ⊤)) := Module.compHom _ α
      S.X₃.val.obj (op ⊤) →ₗ[R] N) (hι : Function.Injective ι) :
    letI : Module R (S.X₃.val.obj (op ⊤)) := Module.compHom _ α
    let := moduleCohomologyModuleOfHom X α S.X₁ 1
    let := moduleCohomologyModuleOfHom X α S.X₂ 1
    let := moduleCohomologyModuleOfHom X α S.X₂ 0
    let := moduleCohomologyModuleOfHom X α S.X₃ 0
    Module.length R (LinearMap.ker (moduleCohomologyMapOfHom X α S.f 1)) ≤
      Module.length R (N ⧸ LinearMap.range
        ((ι.comp (moduleH0EquivOfHom X α S.X₃).toLinearMap).comp
          (moduleCohomologyMapOfHom X α S.g 0))) := by
  let : Module R (S.X₃.val.obj (op ⊤)) := Module.compHom _ α
  let := moduleCohomologyModuleOfHom X α S.X₁ 1
  let := moduleCohomologyModuleOfHom X α S.X₂ 1
  let := moduleCohomologyModuleOfHom X α S.X₂ 0
  let := moduleCohomologyModuleOfHom X α S.X₃ 0
  let δ := moduleCohomologyConnectingOfHom X α S hS 0
  let g := moduleCohomologyMapOfHom X α S.g 0
  let i := ι.comp (moduleH0EquivOfHom X α S.X₃).toLinearMap
  have hk : LinearMap.ker δ = LinearMap.range g :=
    LinearMap.exact_iff.mp (moduleCohomologyConnectingOfHom_exact_left X α S hS 0)
  have hr : LinearMap.ker (moduleCohomologyMapOfHom X α S.f 1) = LinearMap.range δ :=
    LinearMap.exact_iff.mp (moduleCohomologyConnectingOfHom_exact_right X α S hS 0)
  rw [hr, ← δ.quotKerEquivRange.length_eq, hk]
  exact quotient_length_le_of_injective g i
    (hι.comp (moduleH0EquivOfHom X α S.X₃).injective)

/-- The punctured-open injection supplies the section injection needed by
the length bound, on the original short exact coefficient sequence. -/
theorem h1Kernel_length_le_of_h1Restriction
    (X : Scheme.{u}) {R : Type u} [CommRing R] (α : R →+* Γ(X, ⊤))
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (U : X.Opens)
    {N : Type v} [AddCommGroup N] [Module R N]
    (ι : letI : Module R (S.X₃.val.obj (op ⊤)) := Module.compHom _ α
      S.X₃.val.obj (op ⊤) →ₗ[R] N)
    (hH : Function.Injective
      (((moduleAddSheaf X S.X₁).cohomologyPresheaf 1).map
        (homOfLE (show U ≤ ⊤ from le_top)).op))
    (hU : ∀ s, ι s = 0 →
      S.X₃.val.map (homOfLE (show U ≤ ⊤ from le_top)).op s = 0)
    (hbase : ∀ t, ι (S.g.val.app (op ⊤) t) = 0 → S.g.val.app (op ⊤) t = 0) :
    letI : Module R (S.X₃.val.obj (op ⊤)) := Module.compHom _ α
    let := moduleCohomologyModuleOfHom X α S.X₁ 1
    let := moduleCohomologyModuleOfHom X α S.X₂ 1
    let := moduleCohomologyModuleOfHom X α S.X₂ 0
    let := moduleCohomologyModuleOfHom X α S.X₃ 0
    Module.length R (LinearMap.ker (moduleCohomologyMapOfHom X α S.f 1)) ≤
      Module.length R (N ⧸ LinearMap.range
        ((ι.comp (moduleH0EquivOfHom X α S.X₃).toLinearMap).comp
          (moduleCohomologyMapOfHom X α S.g 0))) :=
  h1Kernel_length_le_sectionComparison X α S hS ι
    (sectionComparison_injective_of_h1Restriction X S hS U ι.toAddMonoidHom hH hU hbase)

private theorem h0Sections_map (X : Scheme.{u}) {R : Type u} [CommRing R]
    (α : R →+* Γ(X, ⊤)) {M Q : X.Modules} (g : M ⟶ Q)
    (z : Sheaf.H.{u + 1} (moduleAddSheaf X M) 0) :
    moduleH0EquivOfHom X α Q (moduleCohomologyMapOfHom X α g 0 z) =
      g.val.app (op ⊤) (moduleH0EquivOfHom X α M z) :=
  (Sheaf.H.equiv₀_naturality isTerminalTop
    ((SheafOfModules.toSheaf X.ringCatSheaf).map g) z).symm

/-- A surjective original constants map makes the comparison cokernel
independent of the modification. The displayed fixed map `c` is retained. -/
theorem h1Kernel_length_le_fixedComparison
    (X : Scheme.{u}) {R : Type u} [CommRing R] (α : R →+* Γ(X, ⊤))
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (U : X.Opens)
    {N : Type v} [AddCommGroup N] [Module R N]
    (ι : letI : Module R (S.X₃.val.obj (op ⊤)) := Module.compHom _ α
      S.X₃.val.obj (op ⊤) →ₗ[R] N)
    (σ : letI : Module R (S.X₂.val.obj (op ⊤)) := Module.compHom _ α
      R →ₗ[R] S.X₂.val.obj (op ⊤)) (hσ : Function.Surjective σ)
    (c : R →ₗ[R] N) (hc : ∀ r, ι (S.g.val.app (op ⊤) (σ r)) = c r)
    (hH : Function.Injective
      (((moduleAddSheaf X S.X₁).cohomologyPresheaf 1).map
        (homOfLE (show U ≤ ⊤ from le_top)).op))
    (hU : ∀ s, ι s = 0 →
      S.X₃.val.map (homOfLE (show U ≤ ⊤ from le_top)).op s = 0)
    (hbase : ∀ t, ι (S.g.val.app (op ⊤) t) = 0 → S.g.val.app (op ⊤) t = 0) :
    letI := moduleCohomologyModuleOfHom X α S.X₁ 1
    letI := moduleCohomologyModuleOfHom X α S.X₂ 1
    Module.length R (LinearMap.ker (moduleCohomologyMapOfHom X α S.f 1)) ≤
      Module.length R (N ⧸ LinearMap.range c) := by
  let : Module R (S.X₃.val.obj (op ⊤)) := Module.compHom _ α
  let := moduleCohomologyModuleOfHom X α S.X₁ 1
  let := moduleCohomologyModuleOfHom X α S.X₂ 1
  let := moduleCohomologyModuleOfHom X α S.X₂ 0
  let := moduleCohomologyModuleOfHom X α S.X₃ 0
  have h := h1Kernel_length_le_of_h1Restriction X α S hS U ι hH hU hbase
  have hr : LinearMap.range
      ((ι.comp (moduleH0EquivOfHom X α S.X₃).toLinearMap).comp
        (moduleCohomologyMapOfHom X α S.g 0)) = LinearMap.range c := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      obtain ⟨r, hr⟩ := hσ (moduleH0EquivOfHom X α S.X₂ t)
      refine ⟨r, ?_⟩
      change c r = ι (moduleH0EquivOfHom X α S.X₃
        (moduleCohomologyMapOfHom X α S.g 0 t))
      rw [h0Sections_map, ← hr]
      exact (hc r).symm
    · rintro ⟨r, rfl⟩
      refine ⟨(moduleH0EquivOfHom X α S.X₂).symm (σ r), ?_⟩
      change ι (moduleH0EquivOfHom X α S.X₃
        (moduleCohomologyMapOfHom X α S.g 0 _)) = c r
      rw [h0Sections_map, LinearEquiv.apply_symm_apply]
      exact hc r
  rwa [hr] at h

/-- The kernel of the actual scalar coefficient map on H1 is the native
submodule of elements annihilated by that same scalar. -/
theorem h1ScalarKernel_eq_torsionBy
    (X : Scheme.{u}) {R : Type u} [CommRing R] (α : R →+* Γ(X, ⊤))
    (M : X.Modules) (a : R) :
    letI := moduleCohomologyModuleOfHom X α M 1
    LinearMap.ker (moduleCohomologyMapOfHom X α
      (Scheme.Modules.globalScalarEndomorphism X M (α a)) 1) =
        Submodule.torsionBy R (Sheaf.H.{u + 1} (moduleAddSheaf X M) 1) a := by
  let := moduleCohomologyModuleOfHom X α M 1
  have he : (SheafOfModules.toSheaf X.ringCatSheaf).map
      (Scheme.Modules.globalScalarEndomorphism X M (α a)) =
        moduleScalarOfGlobal X M (α a) := by
    ext V x
    exact Scheme.Modules.globalScalarEndomorphism_app X M (α a) V.unop x
  ext z
  change Sheaf.H.map _ 1 z = 0 ↔ a • z = 0
  rw [he]
  rfl

/-- The fixed-element H1 torsion bound for an actual scalar short exact
sequence and an actual comparison into a fixed normalization module.
All geometric restriction and comparison hypotheses stay explicit. -/
theorem h1Torsion_length_le_fixedComparison
    (X : Scheme.{u}) {R : Type u} [CommRing R] (α : R →+* Γ(X, ⊤))
    (M Q : X.Modules) (a : R) (g : M ⟶ Q)
    (hz : Scheme.Modules.globalScalarEndomorphism X M (α a) ≫ g = 0)
    (hS : (ShortComplex.mk (Scheme.Modules.globalScalarEndomorphism X M (α a)) g hz).ShortExact)
    (U : X.Opens) {N : Type v} [AddCommGroup N] [Module R N]
    (ι : letI : Module R (Q.val.obj (op ⊤)) := Module.compHom _ α
      Q.val.obj (op ⊤) →ₗ[R] N)
    (σ : letI : Module R (M.val.obj (op ⊤)) := Module.compHom _ α
      R →ₗ[R] M.val.obj (op ⊤)) (hσ : Function.Surjective σ)
    (c : R →ₗ[R] N) (hc : ∀ r, ι (g.val.app (op ⊤) (σ r)) = c r)
    (hH : Function.Injective
      (((moduleAddSheaf X M).cohomologyPresheaf 1).map
        (homOfLE (show U ≤ ⊤ from le_top)).op))
    (hU : ∀ s, ι s = 0 → Q.val.map (homOfLE (show U ≤ ⊤ from le_top)).op s = 0)
    (hbase : ∀ t, ι (g.val.app (op ⊤) t) = 0 → g.val.app (op ⊤) t = 0) :
    letI := moduleCohomologyModuleOfHom X α M 1
    Module.length R (Submodule.torsionBy R (Sheaf.H.{u + 1} (moduleAddSheaf X M) 1) a) ≤
      Module.length R (N ⧸ LinearMap.range c) := by
  let := moduleCohomologyModuleOfHom X α M 1
  rw [← h1ScalarKernel_eq_torsionBy X α M a]
  exact h1Kernel_length_le_fixedComparison X α
    (ShortComplex.mk (Scheme.Modules.globalScalarEndomorphism X M (α a)) g hz)
    hS U ι σ hσ c hc hH hU hbase

/-- For a scalar quotient, the comparison's base-section kernel condition
follows from the original constants map and the fixed base map's kernel.
For a reduced-divisor normalization this kernel is the original principal
ideal `(a)`, so no section-injectivity premise is hidden here. -/
theorem h1Torsion_length_le_of_comparisonKernel
    (X : Scheme.{u}) {R : Type u} [CommRing R] (α : R →+* Γ(X, ⊤))
    (M Q : X.Modules) (a : R) (g : M ⟶ Q)
    (hz : Scheme.Modules.globalScalarEndomorphism X M (α a) ≫ g = 0)
    (hS : (ShortComplex.mk (Scheme.Modules.globalScalarEndomorphism X M (α a)) g hz).ShortExact)
    (U : X.Opens) {N : Type v} [AddCommGroup N] [Module R N]
    (ι : letI : Module R (Q.val.obj (op ⊤)) := Module.compHom _ α
      Q.val.obj (op ⊤) →ₗ[R] N)
    (σ : letI : Module R (M.val.obj (op ⊤)) := Module.compHom _ α
      R →ₗ[R] M.val.obj (op ⊤)) (hσ : Function.Surjective σ)
    (c : R →ₗ[R] N) (hc : ∀ r, ι (g.val.app (op ⊤) (σ r)) = c r)
    (hker : ∀ r, c r = 0 → a ∣ r)
    (hH : Function.Injective
      (((moduleAddSheaf X M).cohomologyPresheaf 1).map
        (homOfLE (show U ≤ ⊤ from le_top)).op))
    (hU : ∀ s, ι s = 0 → Q.val.map (homOfLE (show U ≤ ⊤ from le_top)).op s = 0) :
    letI := moduleCohomologyModuleOfHom X α M 1
    Module.length R (Submodule.torsionBy R (Sheaf.H.{u + 1} (moduleAddSheaf X M) 1) a) ≤
      Module.length R (N ⧸ LinearMap.range c) := by
  let : Module R (M.val.obj (op ⊤)) := Module.compHom _ α
  apply h1Torsion_length_le_fixedComparison X α M Q a g hz hS U ι σ hσ c hc hH hU
  intro t ht
  obtain ⟨r, rfl⟩ := hσ t
  obtain ⟨s, hs⟩ := hker r ((hc r).symm.trans ht)
  have hzero := congrArg (fun p : M ⟶ Q => p.val.app (op ⊤) (σ s)) hz
  have hmul : g.val.app (op ⊤) ((α a) • σ s) = 0 := by
    change g.val.app (op ⊤)
      ((Scheme.Modules.globalScalarEndomorphism X M (α a)).val.app (op ⊤) (σ s)) = 0 at hzero
    have he := Scheme.Modules.globalScalarEndomorphism_app X M (α a) ⊤ (σ s)
    change (Scheme.Modules.globalScalarEndomorphism X M (α a)).val.app (op ⊤) (σ s) =
      globalRestriction X ⊤ (α a) • σ s at he
    rw [globalRestriction_top_apply] at he
    exact (congrArg (fun z => g.val.app (op ⊤) z) he).symm.trans hzero
  have hσmul : σ (a * s) = (α a) • σ s := σ.map_smul a s
  rw [hs, hσmul]
  exact hmul

end AlgebraicGeometry.Scheme.Cohomology
