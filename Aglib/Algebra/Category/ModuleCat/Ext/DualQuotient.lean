/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Regular.Category
public import Mathlib.RingTheory.Regular.Free

/-!
# Reducing a dual modulo a regular scalar

Vanishing of the actual first Ext group makes the coefficient quotient map
surjective on Hom. Its kernel is precisely scalar multiples of the dual.
The resulting quotient comparison lifts freeness over a Noetherian local ring.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Abelian Pointwise

namespace Module

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- The original coefficient quotient map on the dual. -/
def dualToQuotientHom (a : R) : Dual R M →ₗ[R] (M →ₗ[R] R ⧸ Ideal.span {a}) :=
  LinearMap.compRight R (Ideal.span {a}).mkQ

@[simp]
theorem dualToQuotientHom_apply (a : R) (f : Dual R M) (m : M) :
    dualToQuotientHom a f m = Ideal.Quotient.mk (Ideal.span {a}) (f m) := rfl

private abbrev principalCoefficientComplex (a : R) : ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.shortComplexOfCompEqZero (LinearMap.lsmul R R a) (Ideal.span {a}).mkQ
    (by
      apply LinearMap.ext
      intro r
      change Ideal.Quotient.mk (Ideal.span {a}) (a * r) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mul_mem_right r _ (Ideal.subset_span (Set.mem_singleton a))))

private theorem principalCoefficientComplex_shortExact (a : R) (ha : IsSMulRegular R a) :
    (principalCoefficientComplex a).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · intro x
    change (Ideal.Quotient.mk (Ideal.span {a}) x = 0) ↔ ∃ y, a * y = x
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    simp only [mul_comm]
  · exact ha
  · exact (Ideal.span {a}).mkQ_surjective

/-- Vanishing first Ext makes the original coefficient reduction surjective on Hom. -/
theorem dualToQuotientHom_surjective (a : R) (ha : IsSMulRegular R a)
    [Subsingleton (Ext (ModuleCat.of R M) (ModuleCat.of R R) 1)] :
    Function.Surjective (dualToQuotientHom (M := M) a) := by
  let S := principalCoefficientComplex a
  have hS : S.ShortExact := principalCoefficientComplex_shortExact a ha
  intro f
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ (ModuleCat.of R M) hS
    (Ext.mk₀ (ModuleCat.ofHom f)) rfl (Subsingleton.elim _ _)
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective (ModuleCat.of R M) S.X₂).surjective x
  refine ⟨g.hom, ?_⟩
  have hg : g ≫ S.g = ModuleCat.ofHom f :=
    (Ext.mk₀_bijective _ _).injective (by simpa only [Ext.mk₀_comp_mk₀] using hx)
  exact congrArg ModuleCat.Hom.hom hg

/-- The kernel of coefficient reduction consists of scalar multiples of the dual. -/
theorem ker_dualToQuotientHom (a : R) (ha : IsSMulRegular R a) :
    (dualToQuotientHom (M := M) a).ker = a • (⊤ : Submodule R (Dual R M)) := by
  let S := principalCoefficientComplex a
  have hS : S.ShortExact := principalCoefficientComplex_shortExact a ha
  ext f
  constructor
  · intro hf
    have hz : ModuleCat.ofHom f ≫ S.g = 0 := by
      exact congrArg ModuleCat.ofHom (LinearMap.mem_ker.mp hf)
    obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₂ (ModuleCat.of R M) hS
      (Ext.mk₀ (ModuleCat.ofHom f)) (by rw [Ext.mk₀_comp_mk₀, hz, Ext.mk₀_zero])
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective (ModuleCat.of R M) S.X₁).surjective x
    have hg : g ≫ S.f = ModuleCat.ofHom f :=
      (Ext.mk₀_bijective _ _).injective (by simpa only [Ext.mk₀_comp_mk₀] using hx)
    apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
    exact ⟨g.hom, Submodule.mem_top, congrArg ModuleCat.Hom.hom hg⟩
  · intro hf
    obtain ⟨g, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hf
    apply LinearMap.mem_ker.mpr
    ext m
    change Ideal.Quotient.mk (Ideal.span {a}) (a * g m) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mul_mem_right (g m) _ (Ideal.subset_span (Set.mem_singleton a)))

/-- The actual dual quotient identifies with Hom into the coefficient quotient. -/
def dualQuotSMulTopEquivHom (a : R) (ha : IsSMulRegular R a)
    [Subsingleton (Ext (ModuleCat.of R M) (ModuleCat.of R R) 1)] :
    QuotSMulTop a (Dual R M) ≃ₗ[R ⧸ Ideal.span {a}] (M →ₗ[R] R ⧸ Ideal.span {a}) :=
  ((Submodule.quotEquivOfEq _ _ (ker_dualToQuotientHom (M := M) a ha).symm).trans
    ((dualToQuotientHom a).quotKerEquivOfSurjective
      (dualToQuotientHom_surjective a ha))).extendScalarsOfSurjective
        Ideal.Quotient.mk_surjective

@[simp]
theorem dualQuotSMulTopEquivHom_apply_mk (a : R) (ha : IsSMulRegular R a)
    [Subsingleton (Ext (ModuleCat.of R M) (ModuleCat.of R R) 1)]
    (f : Dual R M) (m : M) :
    dualQuotSMulTopEquivHom a ha (Submodule.Quotient.mk f) m =
      Ideal.Quotient.mk (Ideal.span {a}) (f m) := rfl

/-- Vanishing first Ext into the coefficient quotient implies vanishing into the ring.
This uses finiteness and Nakayama, without a projective-dimension bound. -/
theorem subsingleton_ext_one_of_quotient [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R M] (a : R) (ha : IsSMulRegular R a)
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    [Subsingleton (Ext (ModuleCat.of R M)
      (ModuleCat.of R (R ⧸ Ideal.span {a})) 1)] :
    Subsingleton (Ext (ModuleCat.of R M) (ModuleCat.of R R) 1) := by
  let S := principalCoefficientComplex a
  have hS : S.ShortExact := principalCoefficientComplex_shortExact a ha
  let E := Ext (ModuleCat.of R M) (ModuleCat.of R R) 1
  have hsurj : Function.Surjective (fun x : E => a • x) := by
    intro x
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₂ (ModuleCat.of R M) hS x
      (Subsingleton.elim _ _)
    refine ⟨y, ?_⟩
    change y.comp (Ext.mk₀ (a • 𝟙 (ModuleCat.of R R))) (add_zero 1) = x at hy
    exact (Ext.smul_eq_comp_mk₀ (R := R) y a).trans hy
  have htop : (⊤ : Submodule R E) = ⊥ := by
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {a}) _
      Module.Finite.fg_top
    · rw [Submodule.ideal_span_singleton_smul]
      intro x _
      obtain ⟨y, rfl⟩ := hsurj x
      exact Submodule.smul_mem_pointwise_smul y a _ Submodule.mem_top
    · rw [Ideal.span_le, Set.singleton_subset_iff,
        IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      exact ham
  apply subsingleton_of_forall_eq 0
  intro x
  exact (show x ∈ (⊥ : Submodule R E) from htop ▸ Submodule.mem_top)

/-- A free reduced Hom module and vanishing first Ext lift freeness of the dual. -/
theorem free_dual_of_free_quotientHom [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R M] (a : R) (ha : IsSMulRegular R a)
    (ham : a ∈ IsLocalRing.maximalIdeal R)
    [Subsingleton (Ext (ModuleCat.of R M) (ModuleCat.of R R) 1)]
    [Free (R ⧸ Ideal.span {a}) (M →ₗ[R] R ⧸ Ideal.span {a})] : Free R (Dual R M) := by
  have := Module.finitePresentation_of_finite R (Dual R M)
  have : Free (R ⧸ Ideal.span {a}) (QuotSMulTop a (Dual R M)) :=
    Free.of_equiv (dualQuotSMulTopEquivHom (M := M) a ha).symm
  apply (free_quotSMulTop_iff_free R (Dual R M) ?_ ?_).mp this
  · rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  · intro f g h
    ext m
    exact ha (LinearMap.congr_fun h m)

end Module
