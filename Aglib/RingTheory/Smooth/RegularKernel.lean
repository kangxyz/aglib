/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.RingTheory.Etale.DifferentialCoordinates
public import Aglib.RingTheory.MvPolynomial.RegularSequence
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.SurjectiveOnStalks
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Regular.Flat

/-!
# Original regular kernels between smooth algebras

A surjective map between two smooth algebras over the same arbitrary
commutative base has, near each prime of its target, a regular list that
generates the kernel of the original principal-localized map.

The proof selects original conormal classes and original function
differentials, keeping the conormal block first. The native exact sequence,
local quotient-basis lifting and literal Kähler localization maps give an
actual differential-coordinate basis on a principal ambient neighborhood.
The same original `MvPolynomial.aeval` map is etale in those coordinates.
Native cotangent tensor and original ideal-localization comparisons,
finite generation and Nakayama identify the same normal functions as
actual kernel generators on a simultaneous principal neighborhood.
Their regularity follows from the original distinct polynomial variables
and native flat transport along that same etale map.

The base, ambient and quotient ring universes are independent. There is no
public Fintype choice, field, Noetherian, nontriviality, or regular-list
supplier premise. Zero rings have empty prime spectra; empty normal lists
are allowed. The geometric purity and canonical-line consumers retain the
original map and the conormal-first order.
-/

@[expose] public section
noncomputable section
open TensorProduct KaehlerDifferential
open scoped BigOperators
universe u v w
namespace Algebra.Smooth

section PointFrames
variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

private theorem regularKernelCotangentProjective (E : Algebra.Extension.{w} R B)
    [Algebra.FormallySmooth R E.Ring] [Algebra.FormallySmooth R B] :
    Module.Projective B E.Cotangent := by
  obtain ⟨l, hl⟩ := (E.formallySmooth_iff_split_injection).mp inferInstance
  exact Module.Projective.of_split E.cotangentComplex l hl

private theorem regularKernelNormalBasis (E : Algebra.Extension.{w} R B) (hfg : E.ker.FG)
    [Algebra.FormallySmooth R E.Ring] [Algebra.FormallySmooth R B] (p : PrimeSpectrum B) :
    ∃ (κ : Type w) (_ : Finite κ) (f : κ → E.ker)
      (b : Module.Basis κ (Localization.AtPrime p.asIdeal)
        ((Localization.AtPrime p.asIdeal) ⊗[B] E.Cotangent)),
      ∀ i, b i = (1 : Localization.AtPrime p.asIdeal) ⊗ₜ[B]
        Algebra.Extension.Cotangent.mk (f i) := by
  let Bp := Localization.AtPrime p.asIdeal
  let Cp := Bp ⊗[B] E.Cotangent
  let : Module.Finite B E.Cotangent := Algebra.Extension.Cotangent.finite hfg
  let : Module.Projective B E.Cotangent := regularKernelCotangentProjective E
  let : Module.Finite Bp Cp := inferInstance
  let : Module.Projective Bp Cp := inferInstance
  let : Module.FinitePresentation Bp Cp := Module.finitePresentation_of_projective Bp Cp
  have hs₀ : Submodule.span B (Set.range (Algebra.Extension.Cotangent.mk (P := E))) = ⊤ := by
    rw [Set.range_eq_univ.mpr Algebra.Extension.Cotangent.mk_surjective, Submodule.span_univ]
  have hs : Submodule.span Bp (Set.range (fun x : E.ker =>
      (1 : Bp) ⊗ₜ[B] Algebra.Extension.Cotangent.mk x)) = ⊤ := by
    have h := congrArg (Submodule.baseChange Bp) hs₀
    simpa only [Submodule.baseChange_span, Submodule.baseChange_top, ← Set.range_comp,
      Function.comp_def, TensorProduct.mk_apply] using h
  obtain ⟨κ, f, b, hb⟩ := Module.exists_basis_of_span_of_flat _ hs
  exact ⟨κ, Module.Finite.finite_basis b, f, b, hb⟩

private theorem regularKernelTangentBasis [Algebra.Smooth R B] (p : PrimeSpectrum B) :
    ∃ (κ : Type v) (_ : Finite κ) (a : κ → B)
      (b : Module.Basis κ (Localization.AtPrime p.asIdeal)
        Ω[Localization.AtPrime p.asIdeal⁄R]),
      ∀ i, b i = D R (Localization.AtPrime p.asIdeal)
        (algebraMap B (Localization.AtPrime p.asIdeal) (a i)) := by
  obtain ⟨κ, a, b, hb⟩ := Module.exists_basis_of_span_of_flat _
    (span_range_map_derivation_of_isLocalization R B (Localization.AtPrime p.asIdeal)
      p.asIdeal.primeCompl)
  refine ⟨κ, Module.Finite.finite_basis b, a, b, ?_⟩
  intro i
  simpa only [Function.comp_def, KaehlerDifferential.map_D] using hb i

end PointFrames

section PointSequence
variable {R B T : Type*} [CommRing R] [CommRing B] [CommRing T] [Algebra R B]
variable (E : Algebra.Extension R B)
variable [Algebra B T] [Algebra E.Ring T] [IsScalarTower E.Ring B T]

private def regularKernelMiddleEquiv : T ⊗[B] E.CotangentSpace ≃ₗ[T] T ⊗[E.Ring] Ω[E.Ring⁄R] :=
  AlgebraTensorModule.cancelBaseChange E.Ring B T T Ω[E.Ring⁄R]

private def regularKernelNormalMap : T ⊗[B] E.Cotangent →ₗ[T] T ⊗[E.Ring] Ω[E.Ring⁄R] :=
  (regularKernelMiddleEquiv E (T := T)).toLinearMap.comp (E.cotangentComplex.baseChange T)

private theorem regularKernelNormalMap_class (x : E.ker) :
    regularKernelNormalMap E ((1 : T) ⊗ₜ[B] Algebra.Extension.Cotangent.mk x) =
      (1 : T) ⊗ₜ[E.Ring] D R E.Ring x.val := by
  simp only [regularKernelNormalMap, regularKernelMiddleEquiv, LinearMap.comp_apply,
    LinearEquiv.coe_coe,
    LinearMap.baseChange_tmul, Algebra.Extension.cotangentComplex_mk,
    AlgebraTensorModule.cancelBaseChange_tmul, one_smul]

variable [Algebra R T] [IsScalarTower R B T] [Algebra.FormallyEtale B T]

private def regularKernelTangentMap : T ⊗[E.Ring] Ω[E.Ring⁄R] →ₗ[T] Ω[T⁄R] :=
  (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B T).toLinearMap.comp
    ((E.toKaehler.baseChange T).comp (regularKernelMiddleEquiv E (T := T)).symm.toLinearMap)

private theorem regularKernelTangentMap_d (a : E.Ring) :
    regularKernelTangentMap E ((1 : T) ⊗ₜ[E.Ring] D R E.Ring a) =
      D R T (algebraMap B T (algebraMap E.Ring B a)) := by
  simp only [regularKernelTangentMap, regularKernelMiddleEquiv, LinearMap.comp_apply,
    LinearEquiv.coe_coe,
    AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul,
    Algebra.Extension.toKaehler, KaehlerDifferential.mapBaseChange_tmul, one_smul,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply, KaehlerDifferential.map_D]

private theorem regularKernelPointExact [Module.Flat B T] :
    Function.Exact (regularKernelNormalMap E (T := T)) (regularKernelTangentMap E (T := T)) := by
  have h : Function.Exact (E.cotangentComplex.baseChange T) (E.toKaehler.baseChange T) := by
    simpa only [LinearMap.baseChange_eq_ltensor] using
      (Module.Flat.lTensor_exact T (Algebra.Extension.exact_cotangentComplex_toKaehler (P := E)))
  have hm := ((regularKernelMiddleEquiv E (T := T)).conj_exact_iff_exact
    (E.cotangentComplex.baseChange T) (E.toKaehler.baseChange T)).mpr h
  exact hm.comp_injective
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B T).toLinearMap
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B T).injective (map_zero _)

omit [Algebra R T] [IsScalarTower R B T] [Algebra.FormallyEtale B T] in
private theorem regularKernelNormalMap_injective [Module.Flat B T]
    [Algebra.FormallySmooth R E.Ring] [Algebra.FormallySmooth R B] :
    Function.Injective (regularKernelNormalMap E (T := T)) := by
  have hf : Function.Injective E.cotangentComplex :=
    (Algebra.Extension.cotangentComplex_injective_iff E).mpr inferInstance
  have hfT : Function.Injective (E.cotangentComplex.baseChange T) := by
    simpa only [LinearMap.baseChange_eq_ltensor] using
      (Module.Flat.lTensor_preserves_injective_linearMap (M := T) E.cotangentComplex hf)
  exact (regularKernelMiddleEquiv E (T := T)).injective.comp hfT

end PointSequence

section ExactFrame
variable {K C M Q : Type*} [CommRing K]
variable [AddCommGroup C] [AddCommGroup M] [AddCommGroup Q]
variable [Module K C] [Module K M] [Module K Q]

private theorem regularKernelFirstBlockBasis
    (f : C →ₗ[K] M) (g : M →ₗ[K] Q) (hfg : Function.Exact f g)
    (hf : Function.Injective f) {I J : Type*}
    (bC : Module.Basis I K C) (bQ : Module.Basis J K Q)
    (v : J → M) (hv : ∀ j, g (v j) = bQ j) :
    ∃ bM : Module.Basis (I ⊕ J) K M,
      (∀ i, bM (Sum.inl i) = f (bC i)) ∧ (∀ j, bM (Sum.inr j) = v j) := by
  let s : Q →ₗ[K] M := bQ.constr K v
  have hs : g ∘ₗ s = LinearMap.id := by
    apply bQ.ext
    intro j
    simp only [LinearMap.comp_apply, s, Module.Basis.constr_basis, LinearMap.id_apply]
    exact hv j
  let e := (hfg.splitSurjectiveEquiv hf) ⟨s, hs⟩
  have heF : f = e.val.symm.toLinearMap ∘ₗ LinearMap.inl K C Q := e.property.1
  have heS : e.val.symm.toLinearMap ∘ₗ LinearMap.inr K C Q = s := by
    exact congrArg Subtype.val ((hfg.splitSurjectiveEquiv hf).symm_apply_apply ⟨s, hs⟩)
  refine ⟨(bC.prod bQ).map e.val.symm, ?_, ?_⟩
  · intro i
    rw [Module.Basis.map_apply, Module.Basis.prod_apply]
    exact (LinearMap.congr_fun heF (bC i)).symm
  · intro j
    rw [Module.Basis.map_apply, Module.Basis.prod_apply]
    change (e.val.symm.toLinearMap ∘ₗ LinearMap.inr K C Q) (bQ j) = v j
    rw [heS]
    exact bQ.constr_basis K v j

end ExactFrame

section NormalFirstBasis
variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

private theorem regularKernelNormalFirstBasis
    (E : Algebra.Extension.{w} R B) (hfg : E.ker.FG)
    [Algebra.FormallySmooth R E.Ring] [Algebra.Smooth R B] (p : PrimeSpectrum B) :
    ∃ (I : Type w) (_ : Finite I) (J : Type v) (_ : Finite J)
      (f : I → E.ker) (a : J → E.Ring)
      (b : Module.Basis (I ⊕ J) (Localization.AtPrime p.asIdeal)
        ((Localization.AtPrime p.asIdeal) ⊗[E.Ring] Ω[E.Ring⁄R])),
      (∀ i, b (Sum.inl i) = (1 : Localization.AtPrime p.asIdeal) ⊗ₜ[E.Ring]
        D R E.Ring (f i).val) ∧
      (∀ j, b (Sum.inr j) = (1 : Localization.AtPrime p.asIdeal) ⊗ₜ[E.Ring]
        D R E.Ring (a j)) ∧
      Submodule.span (Localization.AtPrime p.asIdeal) (Set.range (fun i : I =>
        (1 : Localization.AtPrime p.asIdeal) ⊗ₜ[B] Algebra.Extension.Cotangent.mk (f i))) = ⊤ := by
  let T := Localization.AtPrime p.asIdeal
  let : Algebra.FormallyEtale B T := Algebra.FormallyEtale.of_isLocalization p.asIdeal.primeCompl
  let : Module.Flat B T := inferInstance
  obtain ⟨I, hI, f, bC, hbC⟩ := regularKernelNormalBasis E hfg p
  obtain ⟨J, hJ, aB, bQ, hbQ⟩ := regularKernelTangentBasis (R := R) p
  choose a ha using fun j => E.algebraMap_surjective (aB j)
  let L (j : J) : T ⊗[E.Ring] Ω[E.Ring⁄R] := (1 : T) ⊗ₜ[E.Ring] D R E.Ring (a j)
  have hG (j : J) : regularKernelTangentMap E (L j) = bQ j := by
    rw [regularKernelTangentMap_d, ha]
    exact (hbQ j).symm
  obtain ⟨b, hN, hL⟩ := regularKernelFirstBlockBasis
    (regularKernelNormalMap E (T := T)) (regularKernelTangentMap E (T := T))
    (regularKernelPointExact E (T := T))
    (regularKernelNormalMap_injective E (T := T)) bC bQ L hG
  refine ⟨I, hI, J, hJ, f, a, b, ?_, ?_, ?_⟩
  · intro i
    rw [hN i, hbC i, regularKernelNormalMap_class]
  · intro j
    exact hL j
  · have he : (fun i : I => (1 : T) ⊗ₜ[B] Algebra.Extension.Cotangent.mk (f i)) = bC :=
      funext (fun i => (hbC i).symm)
    rw [he]
    exact bC.span_eq

end NormalFirstBasis

section LocalQuotientBasis
variable {A B M : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [Nontrivial B]
variable [Algebra A B] [AddCommGroup M] [Module A M]
variable [Module.Finite A M] [Module.Flat A M]

private theorem regularKernelLocalQuotientBasis (hAB : Function.Surjective (algebraMap A B))
    {I : Type*} (v : I → M) (b : Module.Basis I B (B ⊗[A] M))
    (hb : ∀ i, b i = (1 : B) ⊗ₜ[A] v i) :
    ∃ bA : Module.Basis I A M, ∀ i, bA i = v i := by
  let K := IsLocalRing.ResidueField A
  have hker : RingHom.ker (algebraMap A B) ≤ RingHom.ker (algebraMap A K) := by
    rw [show RingHom.ker (algebraMap A K) = IsLocalRing.maximalIdeal A from
      IsLocalRing.ker_residue]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top (algebraMap A B))
  let ψ : B →ₐ[A] K := (Algebra.ofId A B).liftOfSurjective hAB (Algebra.ofId A K) hker
  let : Algebra B K := ψ.toRingHom.toAlgebra
  let : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq' ψ.comp_algebraMap.symm
  let bK := (b.baseChange K).map (AlgebraTensorModule.cancelBaseChange A B K K M)
  have hbK (i : I) : bK i = (1 : K) ⊗ₜ[A] v i := by
    change AlgebraTensorModule.cancelBaseChange A B K K M ((b.baseChange K) i) = _
    rw [Module.Basis.baseChange_apply, hb, AlgebraTensorModule.cancelBaseChange_tmul]
    simp only [Algebra.smul_def, map_one, mul_one]
  have hlin : Function.Bijective (Finsupp.linearCombination K
      (fun i => (1 : K) ⊗ₜ[A] v i)) := by
    have hv : (fun i => (1 : K) ⊗ₜ[A] v i) = bK := funext (fun i => (hbK i).symm)
    rw [hv]
    change Function.Bijective (fun a => Finsupp.linearCombination K bK a)
    rw [← Module.Basis.coe_repr_symm]
    exact bK.repr.symm.bijective
  have hA := Module.IsLocalRing.linearCombination_bijective_of_flat v hlin
  let bA : Module.Basis I A M :=
    Module.Basis.ofRepr (LinearEquiv.ofBijective (Finsupp.linearCombination A v) hA).symm
  refine ⟨bA, fun i => ?_⟩
  change Finsupp.linearCombination A v (Finsupp.single i 1) = v i
  rw [Finsupp.linearCombination_single, one_smul]

end LocalQuotientBasis

section EtaleMiddle
variable {R A A' T : Type*} [CommRing R] [CommRing A] [CommRing A'] [CommRing T]
variable [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
variable [Algebra A T] [Algebra A' T] [IsScalarTower A A' T] [Algebra.FormallyEtale A A']

private def regularKernelEtaleMiddleEquiv : T ⊗[A'] Ω[A'⁄R] ≃ₗ[T] T ⊗[A] Ω[A⁄R] :=
  AlgebraTensorModule.congr (.refl T T)
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A A').symm ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange A A' T T Ω[A⁄R]

private theorem regularKernelEtaleMiddleEquiv_d (a : A) :
    regularKernelEtaleMiddleEquiv (R := R) (A := A) (A' := A') (T := T)
      ((1 : T) ⊗ₜ[A'] D R A' (algebraMap A A' a)) =
      (1 : T) ⊗ₜ[A] D R A a := by
  simp only [regularKernelEtaleMiddleEquiv, LinearEquiv.trans_apply, AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
end EtaleMiddle

section StalkNormalFirstBasis
variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

private theorem regularKernelStalkBasis
    (E : Algebra.Extension.{w} R B) (hfg : E.ker.FG)
    [Algebra.Smooth R E.Ring] [Algebra.Smooth R B] (p : PrimeSpectrum B) :
    let q := PrimeSpectrum.comap (algebraMap E.Ring B) p
    ∃ (I : Type w) (_ : Finite I) (J : Type v) (_ : Finite J)
      (f : I → E.ker) (a : J → E.Ring)
      (b : Module.Basis (I ⊕ J) (Localization.AtPrime q.asIdeal)
        Ω[Localization.AtPrime q.asIdeal⁄R]),
      (∀ i, b (Sum.inl i) = D R (Localization.AtPrime q.asIdeal)
        (algebraMap E.Ring (Localization.AtPrime q.asIdeal) (f i).val)) ∧
      (∀ j, b (Sum.inr j) = D R (Localization.AtPrime q.asIdeal)
        (algebraMap E.Ring (Localization.AtPrime q.asIdeal) (a j))) ∧
      Submodule.span (Localization.AtPrime p.asIdeal) (Set.range (fun i : I =>
        (1 : Localization.AtPrime p.asIdeal) ⊗ₜ[B] Algebra.Extension.Cotangent.mk (f i))) = ⊤ := by
  intro q
  let A := E.Ring
  let Aq := Localization.AtPrime q.asIdeal
  let T := Localization.AtPrime p.asIdeal
  let : p.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
  let : Algebra Aq T := Localization.AtPrime.algebraOfLiesOver q.asIdeal p.asIdeal
  let : IsScalarTower A Aq T := inferInstance
  let : Algebra.FormallyEtale A Aq := Algebra.FormallyEtale.of_isLocalization q.asIdeal.primeCompl
  let e := regularKernelEtaleMiddleEquiv (R := R) (A := A) (A' := Aq) (T := T)
  obtain ⟨I, hI, J, hJ, f, a, b₀, hN, hT, hC⟩ :=
    regularKernelNormalFirstBasis E hfg p
  let bq := b₀.map e.symm
  let v : I ⊕ J → Ω[Aq⁄R] := Sum.elim
    (fun i => D R Aq (algebraMap A Aq (f i).val))
    (fun j => D R Aq (algebraMap A Aq (a j)))
  have hbq (k : I ⊕ J) : bq k = (1 : T) ⊗ₜ[Aq] v k := by
    apply e.injective
    change e (e.symm (b₀ k)) = e ((1 : T) ⊗ₜ[Aq] v k)
    rw [e.apply_symm_apply]
    cases k with
    | inl i =>
      change b₀ (Sum.inl i) = regularKernelEtaleMiddleEquiv
        ((1 : T) ⊗ₜ[Aq] D R Aq (algebraMap A Aq (f i).val))
      rw [hN i, regularKernelEtaleMiddleEquiv_d]
    | inr j =>
      change b₀ (Sum.inr j) = regularKernelEtaleMiddleEquiv
        ((1 : T) ⊗ₜ[Aq] D R Aq (algebraMap A Aq (a j)))
      rw [hT j, regularKernelEtaleMiddleEquiv_d]
  have hSurj : Function.Surjective (algebraMap Aq T) := by
    rw [Localization.AtPrime.algebraMap_eq q.asIdeal p.asIdeal]
    exact RingHom.SurjectiveOnStalks.localRingHom_surjective
      (RingHom.surjectiveOnStalks_of_surjective E.algebraMap_surjective) q.asIdeal p.asIdeal rfl
  let : Module.Finite Aq Ω[Aq⁄R] := inferInstance
  let : Module.Flat Aq Ω[Aq⁄R] := inferInstance
  obtain ⟨bA, hbA⟩ := regularKernelLocalQuotientBasis hSurj v bq hbq
  exact ⟨I, hI, J, hJ, f, a, bA, (fun i => hbA (Sum.inl i)), (fun j => hbA (Sum.inr j)), hC⟩

end StalkNormalFirstBasis

section DifferentialSpreading
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable {I : Type*}

private theorem regularKernelSpreadCanonicalMap
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    [Module.Finite A M] [Module.FinitePresentation A N]
    (S : Submonoid A) (l : M →ₗ[A] N) (h : Function.Bijective (LocalizedModule.map S l)) :
    ∃ r ∈ S, ∀ t, r ∣ t → Function.Bijective (LocalizedModule.map (Submonoid.powers t) l) := by
  have hm : (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
      (LocalizedModule.mkLinearMap S N) l : LocalizedModule S M → LocalizedModule S N) =
      (LocalizedModule.map S l : LocalizedModule S M → LocalizedModule S N) := rfl
  have h' : Function.Bijective (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
      (LocalizedModule.mkLinearMap S N) l) := by
    rw [hm]
    exact h
  exact exists_bijective_map_powers S (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S N) l h'

private def regularKernelAwayDifferentialBasis (r : A) (x : I → A)
    (h : Function.Bijective (LocalizedModule.map (Submonoid.powers r)
      (Finsupp.linearCombination A (fun i => D R A (x i))))) :
    Module.Basis I (Localization.Away r) Ω[Localization.Away r⁄R] :=
  let l := Finsupp.linearCombination A (fun i => D R A (x i))
  let b := (Finsupp.basisSingleOne : Module.Basis I A (I →₀ A)).ofIsLocalizedModule
    (Localization.Away r) (Submonoid.powers r)
      (LocalizedModule.mkLinearMap (Submonoid.powers r) (I →₀ A))
  let e₁ := LinearEquiv.ofBijective (LocalizedModule.map (Submonoid.powers r) l) h
  let e₂ := (IsLocalizedModule.iso (Submonoid.powers r)
    (KaehlerDifferential.map R R A (Localization.Away r))).extendScalarsOfIsLocalization
      (Submonoid.powers r) (Localization.Away r)
  b.map (e₁ ≪≫ₗ e₂)

private theorem regularKernelAwayDifferentialBasis_apply (r : A) (x : I → A)
    (h : Function.Bijective (LocalizedModule.map (Submonoid.powers r)
      (Finsupp.linearCombination A (fun i => D R A (x i))))) (i : I) :
    regularKernelAwayDifferentialBasis r x h i =
      D R (Localization.Away r) (algebraMap A (Localization.Away r) (x i)) := by
  change (IsLocalizedModule.iso (Submonoid.powers r)
      (KaehlerDifferential.map R R A (Localization.Away r))).extendScalarsOfIsLocalization
        (Submonoid.powers r) (Localization.Away r)
    ((LocalizedModule.map (Submonoid.powers r)
      (Finsupp.linearCombination A (fun j => D R A (x j))))
        (((Finsupp.basisSingleOne : Module.Basis I A (I →₀ A)).ofIsLocalizedModule
          (Localization.Away r) (Submonoid.powers r)
            (LocalizedModule.mkLinearMap (Submonoid.powers r) (I →₀ A))) i)) = _
  rw [Module.Basis.ofIsLocalizedModule_apply]
  simp only [Finsupp.coe_basisSingleOne]
  change (IsLocalizedModule.iso (Submonoid.powers r)
      (KaehlerDifferential.map R R A (Localization.Away r)))
    ((LocalizedModule.map (Submonoid.powers r)
      (Finsupp.linearCombination A (fun j => D R A (x j))))
        (LocalizedModule.mk (Finsupp.single i 1) 1)) = _
  rw [LocalizedModule.map_mk, Finsupp.linearCombination_single, one_smul,
    IsLocalizedModule.iso_mk_one]
  exact KaehlerDifferential.map_D R R A (Localization.Away r) (x i)

end DifferentialSpreading

section PrincipalCoordinates

private theorem regularKernelCanonicalDifferentialMapBijective
    {R A A' : Type*} [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R A'] [Algebra A A'] [IsScalarTower R A A']
    (S : Submonoid A) [IsLocalization S A'] {I : Type*}
    (x : I → A) (b : Module.Basis I A' Ω[A'⁄R])
    (hb : ∀ i, b i = D R A' (algebraMap A A' (x i))) :
    Function.Bijective (LocalizedModule.map S
      (Finsupp.linearCombination A (fun i => D R A (x i)))) := by
  let l := Finsupp.linearCombination A (fun i => D R A (x i))
  let l₁ : (I →₀ A) →ₗ[A] (I →₀ A') :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A A')
  let l₂ : Ω[A⁄R] →ₗ[A] Ω[A'⁄R] := KaehlerDifferential.map R R A A'
  let ep : (I →₀ A') →ₗ[A'] Ω[A'⁄R] := IsLocalizedModule.mapExtendScalars S l₁ l₂ A' l
  have he : ep = b.repr.symm.toLinearMap := by
    ext i
    trans IsLocalizedModule.map S l₁ l₂ l (l₁ (Finsupp.single i 1))
    · simp [ep, -IsLocalizedModule.map_apply, l₁]
    · simp [l₂, l, hb]
  have h : Function.Bijective (IsLocalizedModule.map S l₁ l₂ l) := by
    change Function.Bijective ep
    rw [he]
    exact b.repr.symm.bijective
  exact (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁ l₂ (l := l)).mp h

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

end PrincipalCoordinates

section LocalQuotientSpan
variable {A B M : Type*} [CommRing A] [IsLocalRing A] [CommRing B] [Nontrivial B]
variable [Algebra A B] [AddCommGroup M] [Module A M] [Module.Finite A M]

private theorem regularKernelLocalQuotientSpan (hAB : Function.Surjective (algebraMap A B))
    {I : Type*} (v : I → M)
    (hv : Submodule.span B (Set.range (fun i => (1 : B) ⊗ₜ[A] v i)) = ⊤) :
    Submodule.span A (Set.range v) = ⊤ := by
  let K := IsLocalRing.ResidueField A
  have hker : RingHom.ker (algebraMap A B) ≤ RingHom.ker (algebraMap A K) := by
    rw [show RingHom.ker (algebraMap A K) = IsLocalRing.maximalIdeal A from
      IsLocalRing.ker_residue]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top (algebraMap A B))
  let ψ : B →ₐ[A] K := (Algebra.ofId A B).liftOfSurjective hAB (Algebra.ofId A K) hker
  let : Algebra B K := ψ.toRingHom.toAlgebra
  let : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq' ψ.comp_algebraMap.symm
  let e := AlgebraTensorModule.cancelBaseChange A B K K M
  have hvK : Submodule.span K (Set.range (fun i => (1 : K) ⊗ₜ[A] v i)) = ⊤ := by
    have hB := congrArg (Submodule.baseChange K) hv
    have h := congrArg (Submodule.map e.toLinearMap) hB
    have he : LinearMap.range e.toLinearMap = ⊤ := LinearMap.range_eq_top.mpr e.surjective
    simp only [Submodule.baseChange_span, Submodule.baseChange_top, Submodule.map_span,
      Submodule.map_top, he, ← Set.range_comp, Function.comp_def, TensorProduct.mk_apply,
      e, LinearEquiv.coe_coe, AlgebraTensorModule.cancelBaseChange_tmul, one_smul] at h
    exact h
  rw [← IsLocalRing.map_tensorProduct_mk_eq_top, Submodule.map_span,
    ← Submodule.restrictScalars_span A K Ideal.Quotient.mk_surjective,
    Submodule.restrictScalars_eq_top_iff, ← Set.range_comp]
  exact hvK

end LocalQuotientSpan

section IdealTensorComparison
variable {R B A' T : Type*} [CommRing R] [CommRing B] [CommRing A'] [CommRing T]
variable [Algebra R B] (E : Algebra.Extension R B)
variable [Algebra E.Ring A'] (M : Submonoid E.Ring) [IsLocalization M A']
variable [Algebra B T] [Algebra E.Ring T] [IsScalarTower E.Ring B T]
variable [Algebra A' T] [IsScalarTower E.Ring A' T]

private theorem regularKernelCotangentEquiv_symm_mk (x : E.ker) :
    E.cotangentEquiv.symm (Algebra.Extension.Cotangent.mk x) = (1 : B) ⊗ₜ[E.Ring] x := by
  apply E.cotangentEquiv.injective
  rw [LinearEquiv.apply_symm_apply, E.contangentEquiv_tmul, one_smul]

private def regularKernelIdealTensorEquiv : T ⊗[B] E.Cotangent ≃ₗ[T]
    T ⊗[A'] (E.ker.map (algebraMap E.Ring A')) :=
  let e₁ := AlgebraTensorModule.congr (.refl T T) E.cotangentEquiv.symm ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange E.Ring B T T E.ker
  let eI := (IsLocalizedModule.isBaseChange M A' (Algebra.idealMap A' E.ker)).equiv
  let e₂ := (AlgebraTensorModule.cancelBaseChange E.Ring A' T T E.ker).symm ≪≫ₗ
    AlgebraTensorModule.congr (.refl T T) eI
  e₁ ≪≫ₗ e₂

private theorem regularKernelIdealTensorEquiv_class (x : E.ker) :
    regularKernelIdealTensorEquiv E M ((1 : T) ⊗ₜ[B] Algebra.Extension.Cotangent.mk x) =
      (1 : T) ⊗ₜ[A'] Algebra.idealMap A' E.ker x := by
  simp only [regularKernelIdealTensorEquiv, LinearEquiv.trans_apply, AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, regularKernelCotangentEquiv_symm_mk,
    AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
    AlgebraTensorModule.cancelBaseChange_symm_tmul, IsBaseChange.equiv_tmul]

end IdealTensorComparison

section LocalIdealGeneration
variable {R B A' T : Type*} [CommRing R] [CommRing B] [CommRing A'] [CommRing T]
variable [Algebra R B] (E : Algebra.Extension R B)
variable [Algebra E.Ring A'] (M : Submonoid E.Ring) [IsLocalization M A']
variable [Algebra B T] [Algebra E.Ring T] [IsScalarTower E.Ring B T]
variable [Algebra A' T] [IsScalarTower E.Ring A' T] [IsLocalRing A'] [Nontrivial T]

include M in
private theorem regularKernelLocalIdealGeneration (hfg : E.ker.FG)
    (hSurj : Function.Surjective (algebraMap A' T)) {I : Type*} (f : I → E.ker)
    (hspan : Submodule.span T (Set.range (fun i : I =>
      (1 : T) ⊗ₜ[B] Algebra.Extension.Cotangent.mk (f i))) = ⊤) :
    E.ker.map (algebraMap E.Ring A') =
      Ideal.span (Set.range (fun i => algebraMap E.Ring A' (f i).val)) := by
  let K := E.ker.map (algebraMap E.Ring A')
  let : Module.Finite A' K := Module.Finite.of_fg (hfg.map (algebraMap E.Ring A'))
  let e := regularKernelIdealTensorEquiv E M (A' := A') (T := T)
  let v (i : I) : K := Algebra.idealMap A' E.ker (f i)
  have hval (i : I) : e.toLinearMap ((1 : T) ⊗ₜ[B] Algebra.Extension.Cotangent.mk (f i)) =
      (1 : T) ⊗ₜ[A'] v i := regularKernelIdealTensorEquiv_class E M (f i)
  have hspanT : Submodule.span T (Set.range (fun i => (1 : T) ⊗ₜ[A'] v i)) = ⊤ := by
    have h := congrArg (Submodule.map e.toLinearMap) hspan
    have he : LinearMap.range e.toLinearMap = ⊤ := LinearMap.range_eq_top.mpr e.surjective
    simpa only [Submodule.map_span, Submodule.map_top, he, ← Set.range_comp,
      Function.comp_def, hval] using h
  have hspanA := regularKernelLocalQuotientSpan hSurj v hspanT
  have h := congrArg (Submodule.map K.subtype) hspanA
  rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at h
  have hv : K.subtype ∘ v = (fun i => algebraMap E.Ring A' (f i).val) := rfl
  rw [hv] at h
  exact h.symm

end LocalIdealGeneration

section IdealSpreading
variable {A : Type*} [CommRing A]

private theorem regularKernelIdealSpreading (p : PrimeSpectrum A)
    (I J : Ideal A) (hI : I.FG) (hJI : J ≤ I)
    (hlocal : Ideal.map (algebraMap A (Localization.AtPrime p.asIdeal)) I ≤
      Ideal.map (algebraMap A (Localization.AtPrime p.asIdeal)) J) :
    ∃ r : A, r ∉ p.asIdeal ∧ ∀ t : A, r ∣ t →
      Ideal.map (algebraMap A (Localization.Away t)) I =
        Ideal.map (algebraMap A (Localization.Away t)) J := by
  classical
  obtain ⟨s, hs⟩ := hI
  have hden (a : s) : ∃ d ∈ p.asIdeal.primeCompl, d * (a : A) ∈ J := by
    apply (IsLocalization.algebraMap_mem_map_algebraMap_iff p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) J (a : A)).mp
    apply hlocal
    apply Ideal.mem_map_of_mem
    rw [← hs]
    exact Submodule.subset_span a.property
  choose d hd hdJ using hden
  let r := ∏ a : s, d a
  have hr : r ∉ p.asIdeal := p.asIdeal.primeCompl.prod_mem (fun a _ => hd a)
  refine ⟨r, hr, ?_⟩
  intro t ht
  have hmap : Ideal.map (algebraMap A (Localization.Away t)) I ≤
      Ideal.map (algebraMap A (Localization.Away t)) J := by
    rw [Ideal.map_le_iff_le_comap, ← hs]
    apply Submodule.span_le.mpr
    intro a ha
    let i : s := ⟨a, ha⟩
    change algebraMap A (Localization.Away t) a ∈
      Ideal.map (algebraMap A (Localization.Away t)) J
    have hu : IsUnit (algebraMap A (Localization.Away t) t) :=
      IsLocalization.map_units (M := Submonoid.powers t) (Localization.Away t)
        ⟨t, Submonoid.mem_powers t⟩
    have hdi : d i ∣ t := (Finset.dvd_prod_of_mem d (Finset.mem_univ i)).trans ht
    have hui : IsUnit (algebraMap A (Localization.Away t) (d i)) :=
      isUnit_of_dvd_unit (map_dvd (algebraMap A (Localization.Away t)) hdi) hu
    have hmem := Ideal.mem_map_of_mem (algebraMap A (Localization.Away t)) (hdJ i)
    rw [map_mul] at hmem
    exact (Submodule.smul_mem_iff_of_isUnit _ hui).mp hmem
  exact le_antisymm hmap (Ideal.map_mono hJI)

end IdealSpreading

section RegularKernelCandidate
variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

private theorem regularKernelJointCoordinates
    (E : Algebra.Extension.{w} R B)
    [Algebra.Smooth R E.Ring] [Algebra.Smooth R B] (p : PrimeSpectrum B) :
    ∃ r : E.Ring, algebraMap E.Ring B r ∉ p.asIdeal ∧
      ∃ (I : Type w) (_ : Finite I) (J : Type v) (_ : Finite J)
        (f : I → E.ker) (a : J → E.Ring),
        (MvPolynomial.aeval (fun k : I ⊕ J => algebraMap E.Ring (Localization.Away r)
          (Sum.elim (fun i => (f i).val) a k)) :
            MvPolynomial (I ⊕ J) R →ₐ[R] Localization.Away r).toRingHom.Etale ∧
        E.ker.map (algebraMap E.Ring (Localization.Away r)) =
          Ideal.span (Set.range (fun i => algebraMap E.Ring (Localization.Away r) (f i).val)) := by
  have hfg : E.ker.FG := Algebra.FinitePresentation.ker_fG_of_surjective
    (IsScalarTower.toAlgHom R E.Ring B) E.algebraMap_surjective
  let q := PrimeSpectrum.comap (algebraMap E.Ring B) p
  let Aq := Localization.AtPrime q.asIdeal
  let T := Localization.AtPrime p.asIdeal
  let : p.asIdeal.LiesOver q.asIdeal := ⟨rfl⟩
  let : Algebra Aq T := Localization.AtPrime.algebraOfLiesOver q.asIdeal p.asIdeal
  let : IsScalarTower E.Ring Aq T := inferInstance
  have hSurj : Function.Surjective (algebraMap Aq T) := by
    rw [Localization.AtPrime.algebraMap_eq q.asIdeal p.asIdeal]
    exact RingHom.SurjectiveOnStalks.localRingHom_surjective
      (RingHom.surjectiveOnStalks_of_surjective E.algebraMap_surjective) q.asIdeal p.asIdeal rfl
  obtain ⟨I, hI, J, hJ, f, a, bq, hN, hT, hC⟩ :=
    regularKernelStalkBasis E hfg p
  let : Finite I := hI
  let : Finite J := hJ
  have hlocalGen := regularKernelLocalIdealGeneration
    E q.asIdeal.primeCompl (A' := Aq) (T := T) hfg hSurj f hC
  let K := Ideal.span (Set.range (fun i => (f i).val))
  have hKI : K ≤ E.ker := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact (f i).property
  have hmapK : K.map (algebraMap E.Ring Aq) =
      Ideal.span (Set.range (fun i => algebraMap E.Ring Aq (f i).val)) := by
    simp only [K, Ideal.map_span, ← Set.range_comp, Function.comp_def]
  have hlocal : E.ker.map (algebraMap E.Ring Aq) ≤ K.map (algebraMap E.Ring Aq) := by
    rw [hlocalGen, hmapK]
  obtain ⟨rG, hrG, hG⟩ := regularKernelIdealSpreading
    q E.ker K hfg hKI hlocal
  let x : I ⊕ J → E.Ring := Sum.elim (fun i => (f i).val) a
  have hbq (k : I ⊕ J) : bq k = D R Aq (algebraMap E.Ring Aq (x k)) := by
    cases k with
    | inl i => exact hN i
    | inr j => exact hT j
  have hc := regularKernelCanonicalDifferentialMapBijective
    q.asIdeal.primeCompl x bq hbq
  let l := Finsupp.linearCombination E.Ring (fun k => D R E.Ring (x k))
  obtain ⟨rD, hrD, hD⟩ := regularKernelSpreadCanonicalMap q.asIdeal.primeCompl l hc
  let r := rD * rG
  have hr : r ∉ q.asIdeal := q.asIdeal.primeCompl.mul_mem hrD hrG
  have hdD : rD ∣ r := ⟨rG, rfl⟩
  have hdG : rG ∣ r := ⟨rD, mul_comm rD rG⟩
  let b := regularKernelAwayDifferentialBasis r x (hD r hdD)
  have hb := regularKernelAwayDifferentialBasis_apply r x (hD r hdD)
  let : Algebra.Smooth E.Ring (Localization.Away r) := Algebra.Smooth.of_isLocalization_Away r
  let : Algebra.Smooth R (Localization.Away r) := Algebra.Smooth.comp R E.Ring (Localization.Away r)
  refine ⟨r, hr, I, hI, J, hJ, f, a, MvPolynomial.etale_aeval_of_basis _ b hb, ?_⟩
  rw [hG r hdG]
  simp only [K, Ideal.map_span, ← Set.range_comp, Function.comp_def]


private theorem regularKernelAevalWeaklyRegular
    {C D : Type*} [CommRing C] [CommRing D] [Algebra C D] {K : Type*}
    (x : K → D) (hEt : (MvPolynomial.aeval x : MvPolynomial K C →ₐ[C] D).toRingHom.Etale)
    (l : List K) (hl : l.Nodup) : RingTheory.Sequence.IsWeaklyRegular D (l.map x) := by
  let P := MvPolynomial K C
  let φ : P →ₐ[C] D := MvPolynomial.aeval x
  let : Algebra P D := φ.toRingHom.toAlgebra
  let : Algebra.Etale P D := hEt
  have h := RingTheory.Sequence.IsWeaklyRegular.of_flat (S := D)
    (MvPolynomial.isWeaklyRegular_X (R := C) l hl)
  have hx (i : K) : algebraMap P D (MvPolynomial.X i) = x i := by
    change (MvPolynomial.aeval x) (MvPolynomial.X i) = x i
    exact MvPolynomial.aeval_X x i
  change RingTheory.Sequence.IsWeaklyRegular D
    ((l.map (MvPolynomial.X : K → P)).map (algebraMap P D)) at h
  have hlit : (l.map (MvPolynomial.X : K → P)).map (algebraMap P D) = l.map x := by
    rw [List.map_map]
    congr 1
    funext i
    exact hx i
  rw [hlit] at h
  exact h

private theorem regularKernelAwayMap_ker {C D : Type*} [CommRing C] [CommRing D]
    (φ : C →+* D) (r : C) :
    RingHom.ker (IsLocalization.Away.map (Localization.Away r)
      (Localization.Away (φ r)) φ r) = (RingHom.ker φ).map (algebraMap C (Localization.Away r)) :=
        by
  simpa only [IsLocalization.Away.map] using
    (IsLocalization.ker_map (S := Localization.Away r) (M := Submonoid.powers r)
      (T := Submonoid.powers (φ r)) (Localization.Away (φ r)) φ (by rw [Submonoid.map_powers]))

private theorem regularKernelExtension (E : Algebra.Extension.{w} R B)
    [Algebra.Smooth R E.Ring] [Algebra.Smooth R B] (p : PrimeSpectrum B) :
    ∃ r : E.Ring, algebraMap E.Ring B r ∉ p.asIdeal ∧
      ∃ s : List (Localization.Away r),
        RingTheory.Sequence.IsRegular (Localization.Away r) s ∧
        RingHom.ker (IsLocalization.Away.map (Localization.Away r)
          (Localization.Away (algebraMap E.Ring B r)) (algebraMap E.Ring B) r) = Ideal.ofList s :=
            by
  classical
  obtain ⟨r, hr, I, hI, J, hJ, f, a, hEt, hGen⟩ := regularKernelJointCoordinates E p
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let lI : List I := Finset.univ.toList
  let lVar : List (I ⊕ J) := lI.map Sum.inl
  let x : I ⊕ J → Localization.Away r := fun k => algebraMap E.Ring (Localization.Away r)
    (Sum.elim (fun i => (f i).val) a k)
  let s : List (Localization.Away r) := lI.map (fun i => algebraMap E.Ring (Localization.Away r) (f
    i).val)
  have hlI : lI.Nodup := Finset.nodup_toList _
  have hlVar : lVar.Nodup := hlI.map Sum.inl_injective
  have hW := regularKernelAevalWeaklyRegular x hEt lVar hlVar
  have hs : lVar.map x = s := by
    simp only [lVar, s, List.map_map, Function.comp_def, x, Sum.elim_inl]
  rw [hs] at hW
  have hList : Ideal.ofList s =
      Ideal.span (Set.range (fun i => algebraMap E.Ring (Localization.Away r) (f i).val)) := by
    unfold Ideal.ofList
    congr 1
    ext z
    simp only [s, lI, Set.mem_ofPred_eq, List.mem_map, Finset.mem_toList, Finset.mem_univ,
      true_and, Set.mem_range]
  let φ := algebraMap E.Ring B
  let φr := IsLocalization.Away.map (Localization.Away r) (Localization.Away (φ r)) φ r
  have hker : RingHom.ker φr = Ideal.ofList s :=
    (regularKernelAwayMap_ker φ r).trans (hGen.trans hList.symm)
  have hpow : Submonoid.powers (φ r) ≤ p.asIdeal.primeCompl.comap (RingHom.id B) := by
    change Submonoid.powers (φ r) ≤ p.asIdeal.primeCompl
    exact Submonoid.powers_le.mpr hr
  let j : Localization.Away (φ r) →+* Localization.AtPrime p.asIdeal :=
    IsLocalization.map (M := Submonoid.powers (φ r)) (T := p.asIdeal.primeCompl)
      (Localization.AtPrime p.asIdeal) (RingHom.id B) hpow
  let : Nontrivial (Localization.Away (φ r)) := j.domain_nontrivial
  have hReg : RingTheory.Sequence.IsRegular (Localization.Away r) s := by
    refine ⟨hW, ?_⟩
    rw [Ideal.smul_eq_mul, Ideal.mul_top, ← hker]
    exact (RingHom.ker_ne_top φr).symm
  exact ⟨r, hr, s, hReg, hker⟩

end RegularKernelCandidate


/-- A smooth surjection has an original regular-kernel list on a principal neighborhood. -/
theorem exists_away_regular_kernel_of_surjective
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.Smooth R A] [Algebra.Smooth R B]
    (φ : A →ₐ[R] B) (hφ : Function.Surjective φ) (p : PrimeSpectrum B) :
    ∃ r : A, φ r ∉ p.asIdeal ∧ ∃ s : List (Localization.Away r),
      RingTheory.Sequence.IsRegular (Localization.Away r) s ∧
      RingHom.ker (IsLocalization.Away.map (Localization.Away r)
        (Localization.Away (φ r)) φ.toRingHom r) = Ideal.ofList s := by
  let E := Algebra.Extension.ofSurjective φ hφ
  let : Algebra.Smooth R E.Ring := inferInstanceAs (Algebra.Smooth R A)
  exact regularKernelExtension E p



end Algebra.Smooth
