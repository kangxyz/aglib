/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.CofinalIdeals
public import Aglib.RingTheory.AdicCompletion.FiniteGeneration
public import Aglib.RingTheory.AdicCompletion.IdealMap
public import Aglib.RingTheory.AdicCompletion.RegularLocalRing
public import Aglib.RingTheory.RegularLocalRing.Domain
public import Mathlib.RingTheory.Finiteness.NilpotentKer
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Completion of an actual local parameter map

Complete the original source ring and retain its map into the original
complete local target. A maximal-radical parameter ideal and surjectivity
on the original residue point give module finiteness. Equality of finite
dimensions and a domain source then give injectivity by integral
incomparability and the nonzerodivisor dimension drop.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped nonZeroDivisors

namespace AdicCompletion

section Map

variable {B A : Type*} [CommRing B] [IsLocalRing B]
  [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [IsAdicComplete (maximalIdeal A) A]

/-- The actual completion map obtained from the original parameter map
and the proved cofinality of its image ideal. -/
def localParameterMap (f : B →+* A)
    (h : ((maximalIdeal B).map f).radical = maximalIdeal A) :
    AdicCompletion (maximalIdeal B) B →+* A :=
  let J := (maximalIdeal B).map f
  let hex := Ideal.exists_pow_le_of_le_radical_of_fg h.symm.le
    (maximalIdeal A).fg_of_isNoetherianRing
  let n := hex.choose + 1
  let hpow : maximalIdeal A ^ n ≤ J :=
    (Ideal.pow_le_pow_right (Nat.le_succ hex.choose)).trans hex.choose_spec
  (ofAlgEquiv (maximalIdeal A)).symm.toRingHom.comp
    ((sandwichAlgEquiv (maximalIdeal A) J n (Nat.zero_lt_succ _)
      (Ideal.le_radical.trans h.le) hpow).toRingHom.comp
      (idealMap f (maximalIdeal B) J rfl))

/-- The completed map extends the original map on every original element. -/
@[simp]
theorem localParameterMap_algebraMap (f : B →+* A)
    (h : ((maximalIdeal B).map f).radical = maximalIdeal A) (b : B) :
    localParameterMap f h
      (algebraMap B (AdicCompletion (maximalIdeal B) B) b) = f b := by
  unfold localParameterMap
  simp only [RingHom.comp_apply, idealMap_algebraMap]
  exact (ofAlgEquiv (maximalIdeal A)).symm.commutes (f b)

variable [IsNoetherianRing B]

/-- The extended maximal ideal is precisely the original parameter ideal. -/
theorem map_maximalIdeal_localParameterMap (f : B →+* A)
    (h : ((maximalIdeal B).map f).radical = maximalIdeal A) :
    (maximalIdeal (AdicCompletion (maximalIdeal B) B)).map (localParameterMap f h) =
      (maximalIdeal B).map f := by
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map]
  have he : (localParameterMap f h).comp
      (algebraMap B (AdicCompletion (maximalIdeal B) B)) = f := by
    ext b
    exact localParameterMap_algebraMap f h b
  rw [he]

/-- The completed map is local because its actual maximal ideal maps
to the original proper parameter ideal. -/
theorem localParameterMap_isLocalHom (f : B →+* A)
    (h : ((maximalIdeal B).map f).radical = maximalIdeal A) :
    IsLocalHom (localParameterMap f h) := by
  apply ((IsLocalRing.local_hom_TFAE (localParameterMap f h)).out 1 3).mpr
  rw [map_maximalIdeal_localParameterMap]
  exact Ideal.le_radical.trans h.le

end Map

private theorem finite_quotient_of_radical_eq_maximalIdeal
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing A] [IsNoetherianRing A]
    (J : Ideal A) (hJ : J.radical = maximalIdeal A)
    (hres : Function.Surjective (algebraMap R (ResidueField A))) :
    Module.Finite R (A ⧸ J) := by
  let : Module.Finite R (ResidueField A) :=
    Module.Finite.of_surjective (Algebra.linearMap R (ResidueField A)) hres
  have hJm : J ≤ maximalIdeal A := Ideal.le_radical.trans hJ.le
  let f : A ⧸ J →ₐ[R] ResidueField A := Ideal.Quotient.factorₐ R hJm
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hJm
  have hker : RingHom.ker f.toRingHom = (maximalIdeal A).map (Ideal.Quotient.mk J) :=
    Ideal.Quotient.factor_ker hJm
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJ.symm.le
    (maximalIdeal A).fg_of_isNoetherianRing
  have hnil : IsNilpotent (RingHom.ker f.toRingHom) := by
    refine ⟨n, ?_⟩
    rw [hker, ← Ideal.map_pow]
    exact Ideal.map_mk_eq_bot_of_le hn
  let : IsNoetherianRing (A ⧸ J) :=
    isNoetherianRing_of_surjective A (A ⧸ J) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  have hfg := (RingHom.ker f.toRingHom).fg_of_isNoetherianRing
  exact Module.finite_of_surjective_of_ker_le_nilradical f hf
    (hfg.isNilpotent_iff_le_nilradical.mp hnil) hfg

/-- The actual completed parameter map is module finite. Its residue
surjectivity and maximal-radical condition are the primitive inputs;
finiteness is derived by nilpotent-kernel descent and coefficient lifting. -/
theorem finite_localParameterMap
    {B A : Type*} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (f : B →+* A) (h : ((maximalIdeal B).map f).radical = maximalIdeal A)
    (hres : Function.Surjective ((residue A).comp f)) :
    let _ : Algebra (AdicCompletion (maximalIdeal B) B) A := (localParameterMap f h).toAlgebra
    Module.Finite (AdicCompletion (maximalIdeal B) B) A := by
  let R := AdicCompletion (maximalIdeal B) B
  let : Algebra R A := (localParameterMap f h).toAlgebra
  let : IsNoetherianRing R := AdicCompletion.isNoetherianRing B (maximalIdeal B)
  let : IsAdicComplete (maximalIdeal R) R := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact AdicCompletion.isAdicComplete_self (maximalIdeal B)
      (maximalIdeal B).fg_of_isNoetherianRing
  let J := (maximalIdeal R).map (algebraMap R A)
  have hJ : J.radical = maximalIdeal A := by
    change ((maximalIdeal R).map (localParameterMap f h)).radical = _
    rw [map_maximalIdeal_localParameterMap]
    exact h
  have hres' : Function.Surjective (algebraMap R (ResidueField A)) := by
    intro a
    obtain ⟨b, hb⟩ := hres a
    refine ⟨algebraMap B R b, ?_⟩
    change residue A (localParameterMap f h (algebraMap B R b)) = a
    rw [localParameterMap_algebraMap]
    exact hb
  let : Module.Finite R (A ⧸ J) := finite_quotient_of_radical_eq_maximalIdeal J hJ hres'
  let e : (A ⧸ (maximalIdeal R • ⊤ : Submodule R A)) ≃ₗ[R] A ⧸ J :=
    (Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map (maximalIdeal R))).trans
      (Submodule.Quotient.restrictScalarsEquiv R J)
  let : Module.Finite R (A ⧸ (maximalIdeal R • ⊤ : Submodule R A)) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  apply Module.finite_of_isPrecomplete_of_le_jacobson (maximalIdeal R)
  rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) bot_ne_top]
  exact Ideal.le_radical.trans hJ.le

private theorem ringKrullDim_le_of_integral
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.IsIntegral R S := ⟨hf⟩
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f)
  intro P Q hPQ
  exact Ideal.IsIntegral.under_lt_under hPQ

private theorem injective_of_integral_of_equal_finite_dimension
    {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) (d : ℕ)
    (hR : ringKrullDim R = (d : ℕ)) (hS : ringKrullDim S = (d : ℕ)) :
    Function.Injective f := by
  apply (injective_iff_map_eq_zero f).mpr
  intro r hr
  by_contra hr0
  let I : Ideal R := Ideal.span {r}
  have hI : I ≤ RingHom.ker f := (Ideal.span_singleton_le_iff_mem (RingHom.ker f)).mpr hr
  let g : R ⧸ I →+* S := Ideal.Quotient.lift I f (fun x hx ↦ hI hx)
  have hcomp : g.comp (Ideal.Quotient.mk I) = f := by ext; rfl
  have hg : g.IsIntegral :=
    RingHom.IsIntegral.tower_top (Ideal.Quotient.mk I) g (hcomp.symm ▸ hf)
  have hdim : ringKrullDim S + 1 ≤ ringKrullDim R := by
    calc
      ringKrullDim S + 1 = 1 + ringKrullDim S := add_comm _ _
      _ ≤ 1 + ringKrullDim (R ⧸ I) :=
        add_le_add_right (ringKrullDim_le_of_integral g hg) 1
      _ = ringKrullDim (R ⧸ I) + 1 := add_comm _ _
      _ ≤ ringKrullDim R :=
        ringKrullDim_quotient_succ_le_of_nonZeroDivisor
          (mem_nonZeroDivisors_iff_ne_zero.mpr hr0)
  rw [hR, hS] at hdim
  have : d + 1 ≤ d := by exact_mod_cast hdim
  omega

/-- For a regular source and an equally dimensional target, the actual
completed parameter map is injective as well as finite and local. -/
theorem injective_localParameterMap
    {B A : Type*} [CommRing B] [IsRegularLocalRing B]
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (f : B →+* A) (h : ((maximalIdeal B).map f).radical = maximalIdeal A)
    (hres : Function.Surjective ((residue A).comp f))
    (d : ℕ) (hB : ringKrullDim B = (d : ℕ)) (hA : ringKrullDim A = (d : ℕ)) :
    Function.Injective (localParameterMap f h) := by
  let R := AdicCompletion (maximalIdeal B) B
  let : IsRegularLocalRing R :=
    (AdicCompletion.isRegularLocalRing_iff_maximalCompletion B).mp inferInstance
  let : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
  let : Algebra R A := (localParameterMap f h).toAlgebra
  let : Module.Finite R A := finite_localParameterMap f h hres
  have hf : (localParameterMap f h).IsIntegral := Algebra.IsIntegral.isIntegral
  exact injective_of_integral_of_equal_finite_dimension (localParameterMap f h) hf d
    ((AdicCompletion.ringKrullDim_maximalIdeal_eq B).trans hB) hA

end AdicCompletion
