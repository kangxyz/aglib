/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.ProperBirational
public import Aglib.AlgebraicGeometry.Spec.CompletionLocalRing
public import Aglib.RingTheory.AdicCompletion.Normalization
public import Aglib.RingTheory.Descent.FormalGluing.Normalization
public import Aglib.RingTheory.Nagata.FiniteTypeSurface
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Support

/-!
# Actual normalization comparison after completion

The affine supplier uses the original completion tensor algebra. Generic
algebraicity and the complete base's dimension-two Nagata theorem give finite
upper normalization. Normality away from the original closed-fibre ideal gives
a power conductor; the original completion quotients then supply the passed
canonical normalization comparison.

The scheme comparison is constructed through the actual generic normalization
lift, with both original projections. Denominator uniqueness identifies its
actual affine section maps with the canonical normalization tensor map.
Target-local isomorphisms give the global comparison, while complete-base
GF2 and faithfully flat descent give finite lower normalization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped TensorProduct nonZeroDivisors

universe u v

namespace AlgebraicGeometry.Scheme.CompletionNormalization

section LocalConductor

variable (S : Type u) (Q : Type v) [CommRing S] [IsDomain S]
  [Field Q] [Algebra S Q] [IsFractionRing S Q]

private theorem normalization_denominator_atPrime
    (p : Ideal S) [p.IsPrime] [IsIntegrallyClosed (Localization.AtPrime p)]
    (b : integralClosure S Q) :
    ∃ s ∉ p, ∃ a : S, algebraMap S (integralClosure S Q) a = s • b := by
  let P := Localization.AtPrime p
  let φ : P →ₐ[S] Q := IsLocalization.liftAlgHom
    (M := p.primeCompl) (f := Algebra.ofId S Q)
    (fun s => IsLocalization.map_units Q ⟨s.val, p.primeCompl_le_nonZeroDivisors s.property⟩)
  let : Algebra P Q := φ.toRingHom.toAlgebra
  let : IsScalarTower S P Q := IsScalarTower.of_algHom φ
  let : IsFractionRing P Q :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl P Q
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    (show _root_.IsIntegral P (b : Q) from b.property.tower_top)
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj p.primeCompl y
  refine ⟨s.val, s.property, a, ?_⟩
  apply Subtype.ext
  have hQ := congrArg (algebraMap P Q) hs
  rw [map_mul, ← IsScalarTower.algebraMap_apply S P Q,
    ← IsScalarTower.algebraMap_apply S P Q, hy] at hQ
  calc
    (algebraMap S (integralClosure S Q) a : Q) = algebraMap S Q a :=
      (integralClosure S Q).val.commutes a
    _ = (b : Q) * algebraMap S Q s.val := hQ.symm
    _ = algebraMap S Q s.val * (b : Q) := mul_comm _ _
    _ = (s.val • b : integralClosure S Q) := by
      rw [Subalgebra.coe_smul, Algebra.smul_def]

/-- A finite actual normalization which is normal away from a finitely
generated ideal has a power conductor. The quotient and its support are the
ones of the original scalar inclusion. -/
theorem exists_normalization_conductor_pow
    [Module.Finite S (integralClosure S Q)] (I : Ideal S) (hI : I.FG)
    (hNormal : ∀ p : PrimeSpectrum S, ¬ I ≤ p.asIdeal →
      IsIntegrallyClosed (Localization.AtPrime p.asIdeal)) :
    ∃ n : ℕ, ∀ s ∈ I ^ n, ∀ b : integralClosure S Q,
      ∃ a : S, algebraMap S (integralClosure S Q) a = s • b := by
  let B := integralClosure S Q
  let T := (Algebra.linearMap S B).range
  let M := B ⧸ T
  let : Module.Finite S M := inferInstance
  have hsupport : Module.support S M ⊆ PrimeSpectrum.zeroLocus (I : Set S) := by
    intro p hp
    by_contra hnot
    have hnotI : ¬ I ≤ p.asIdeal := by
      simpa only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] using hnot
    let : IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := hNormal p hnotI
    have hvanish : p ∉ Module.support S M := by
      apply Module.notMem_support_iff'.mpr
      intro q
      obtain ⟨b, rfl⟩ := T.mkQ_surjective q
      obtain ⟨s, hsp, a, ha⟩ := normalization_denominator_atPrime S Q p.asIdeal b
      refine ⟨s, hsp, ?_⟩
      rw [← map_smul]
      apply (Submodule.Quotient.mk_eq_zero T).mpr
      exact ⟨a, ha⟩
    exact hvanish hp
  have hrad : I ≤ (Module.annihilator S M).radical := by
    apply (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff (Module.annihilator S M) I).mp
    rw [← Module.support_eq_zeroLocus]
    exact hsupport
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hI
  refine ⟨n, ?_⟩
  intro s hs b
  have hz := (Module.mem_annihilator.mp (hn hs)) (T.mkQ b)
  have hmem : s • b ∈ T := by
    apply (Submodule.Quotient.mk_eq_zero T).mp
    change T.mkQ (s • b) = 0
    rw [map_smul]
    exact hz
  exact hmem

end LocalConductor

section AffineCompletion

variable (A C : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [CommRing C] [Algebra A C]

local notation "H" => AdicCompletion (IsLocalRing.maximalIdeal A) A
local notation "D" => H ⊗[A] C

private theorem completion_faithfullyFlat : Module.FaithfullyFlat A H :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The coefficient algebra's action on its original completion tensor is
the actual `includeRight` action. Faithful flatness is derived by base change. -/
theorem tensor_faithfullyFlat :
    letI := Algebra.TensorProduct.rightAlgebra (R := A) (A := H) (B := C)
    Module.FaithfullyFlat C D := by
  let : Module.FaithfullyFlat A H := completion_faithfullyFlat A
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := H) (B := C)
  let e : D ≃ₐ[C] C ⊗[A] H :=
    { (Algebra.TensorProduct.comm A H C).toRingEquiv with
      commutes' c := rfl }
  exact Module.FaithfullyFlat.of_linearEquiv C (C ⊗[A] H) e.toLinearEquiv

variable [IsDomain A] [IsDomain C]
  [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
  [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A] C)]
  [Algebra.FiniteType A C] [Algebra.IsAlgebraic A C]

omit [IsDomain A] [IsDomain C] in
/-- GF2 applies to the actual completed generically algebraic chart.
The source coefficient ring receives no Nagata or excellence hypothesis. -/
theorem tensor_isNagata (hd : ringKrullDim A ≤ 2)
    (hinj : Function.Injective (algebraMap A C)) : IsNagataRing.{u, 0} D := by
  let : IsNoetherianRing H := AdicCompletion.isNoetherianRing A (IsLocalRing.maximalIdeal A)
  let : Module.FaithfullyFlat A H := completion_faithfullyFlat A
  have hdH : ringKrullDim H ≤ 2 :=
    (AdicCompletion.ringKrullDim_maximalIdeal_eq A).le.trans hd
  let : Ring.KrullDimLE 2 H := Ring.krullDimLE_iff.mpr hdH
  have hH : IsNagataRing.{u, 0} H := IsNagataRing.of_complete_local_dimLE_two H
  let : Algebra.FiniteType H D := inferInstance
  let : Algebra.IsAlgebraic H D := inferInstance
  have hi : Function.Injective (algebraMap H D) :=
    Algebra.TensorProduct.includeLeft_injective (R := A) (S := H) (A := H) (B := C) hinj
  exact hH.of_finiteType_isAlgebraic_of_dimLE_two hdH hi

omit [IsDomain A] [IsDomain C] in
/-- The actual upper normalization is finite by complete-base GF2. -/
theorem tensor_normalization_finite (hd : ringKrullDim A ≤ 2)
    (hinj : Function.Injective (algebraMap A C)) :
    Module.Finite D (integralClosure D (FractionRing D)) :=
  integralClosure.finite_of_isNagataRing D (tensor_isNagata A C hd hinj) (FractionRing D)

omit [IsDomain A] [IsDomain C] in
/-- Finiteness of the original chart normalization follows from the actual
upper normalization and faithfully flat injection. This does not yet assert
that normalization commutes with base change. -/
theorem affine_normalization_finite (hd : ringKrullDim A ≤ 2)
    (hinj : Function.Injective (algebraMap A C))
    (K : Type v) [CommRing K] [Algebra C K] [IsFractionRing C K] :
    Module.Finite C (integralClosure C K) := by
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := H) (B := C)
  let : Module.FaithfullyFlat C D := tensor_faithfullyFlat A C
  let : IsNoetherianRing D := (tensor_isNagata A C hd hinj).isNoetherianRing
  let : Module.Finite D (integralClosure D (FractionRing D)) :=
    tensor_normalization_finite A C hd hinj
  exact integralClosure.finite_of_faithfullyFlat C D K (FractionRing D)

omit [IsDomain A] in
/-- The actual canonical affine comparison after completion. The upper
finiteness, power conductor, and coefficient quotient are all derived.
The remaining local normality input is exactly normality off the original
closed-fibre ideal. -/
def affineNormalizationEquiv (hd : ringKrullDim A ≤ 2)
    (hinj : Function.Injective (algebraMap A C))
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) (ha0 : a ≠ 0)
    (K : Type v) [CommRing K] [Algebra C K] [IsFractionRing C K]
    (hNormal : ∀ p : PrimeSpectrum D,
      ¬ ((IsLocalRing.maximalIdeal A).map (algebraMap A C)).map
          (Algebra.TensorProduct.includeRight (R := A) (A := H)).toRingHom ≤ p.asIdeal →
        IsIntegrallyClosed (Localization.AtPrime p.asIdeal)) :
    letI := Algebra.TensorProduct.rightAlgebra (R := A) (A := H) (B := C)
    D ⊗[C] integralClosure C K ≃ₐ[D] integralClosure D (FractionRing D) := by
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := H) (B := C)
  let : Module.FaithfullyFlat C D := tensor_faithfullyFlat A C
  let : Module.Finite D (integralClosure D (FractionRing D)) :=
    tensor_normalization_finite A C hd hinj
  let : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
  let I : Ideal C := (IsLocalRing.maximalIdeal A).map (algebraMap A C)
  have hI : I.FG := I.fg_of_isNoetherianRing
  have hID : (I.map (algebraMap C D)).FG := hI.map (algebraMap C D)
  have hconductor := exists_normalization_conductor_pow D (FractionRing D)
    (I.map (algebraMap C D)) hID hNormal
  let n : ℕ := Classical.choose hconductor
  have hn := Classical.choose_spec hconductor
  let J := I ^ n
  have hpow : ((IsLocalRing.maximalIdeal A) ^ n).map (algebraMap A C) ≤ J := by
    rw [Ideal.map_pow]
  let e : C ⧸ J ≃+* D ⧸ J.map (algebraMap C D) :=
    AdicCompletion.quotientTensorCompletionEquiv (IsLocalRing.maximalIdeal A) C
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing n J hpow
  have he (c : C) : e (Ideal.Quotient.mk J c) =
      Ideal.Quotient.mk (J.map (algebraMap C D)) (algebraMap C D c) :=
    AdicCompletion.quotientTensorCompletionEquiv_mk (IsLocalRing.maximalIdeal A) C
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing n J hpow c
  have ht : (algebraMap A C a) ^ n ∈ J :=
    Ideal.pow_mem_pow (Ideal.mem_map_of_mem (algebraMap A C) ha) n
  have ht0 : (algebraMap A C a) ^ n ≠ 0 :=
    pow_ne_zero n (fun h => ha0 (hinj (by simpa only [map_zero] using h)))
  apply integralClosure.flatBaseChangeEquivOfConductor C D K (FractionRing D)
    J hI.pow ((algebraMap A C a) ^ n) ht ht0 e he
  intro s hs b
  apply hn s
  simpa only [J, Ideal.map_pow] using hs

end AffineCompletion

section ActualComparison

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : Y ⟶ X) [IsDominant f]

/-- The original map from the actual upper generic normalization to the
pullback of the actual lower generic normalization. It is constructed from
the original dominant map and the proved normality of the upper normalization. -/
def normalizationComparison :
    (Y.fromSpecStalk (genericPoint Y)).normalization ⟶
      pullback (X.fromSpecStalk (genericPoint X)).fromNormalization f := by
  let νY := (Y.fromSpecStalk (genericPoint Y)).fromNormalization
  let : IsDominant νY := genericNormalization_isDominant Y
  let g := νY ≫ f
  let hY := genericNormalization_normalStalks Y
  exact pullback.lift (genericNormalizationLift g hY) νY
    (genericNormalizationLift_over g hY)

/-- The comparison's first projection is the original normalization lift. -/
@[reassoc]
theorem normalizationComparison_fst :
    letI := genericNormalization_isDominant Y
    normalizationComparison f ≫
        pullback.fst (X.fromSpecStalk (genericPoint X)).fromNormalization f =
      genericNormalizationLift
        ((Y.fromSpecStalk (genericPoint Y)).fromNormalization ≫ f)
        (genericNormalization_normalStalks Y) := by
  let := genericNormalization_isDominant Y
  exact pullback.lift_fst _ _ _

/-- The comparison's second projection is the actual upper normalization map. -/
@[reassoc (attr := simp)]
theorem normalizationComparison_snd :
    normalizationComparison f ≫
        pullback.snd (X.fromSpecStalk (genericPoint X)).fromNormalization f =
      (Y.fromSpecStalk (genericPoint Y)).fromNormalization := by
  exact pullback.lift_snd _ _ _

end ActualComparison



section ActualBirationalCharts

variable {A : CommRingCat.{u}} {W : Scheme.{u}} (f : W ⟶ Spec A)

local instance [IsDomain A] : Nonempty (⊤ : (Spec A).Opens) :=
  ⟨⟨genericPoint (Spec A), trivial⟩⟩

private def chartScalar (U : W.Opens) : A →+* Γ(W, U) :=
  (f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso A).inv.hom

private theorem chartScalar_over (U : W.Opens) (hU : IsAffineOpen U) :
    hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (chartScalar f U)) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hU le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

private theorem chartScalar_finiteType [LocallyOfFiniteType f]
    (U : W.Opens) (hU : IsAffineOpen U) : (chartScalar f U).FiniteType :=
  (f.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
    (RingHom.FiniteType.of_surjective (Scheme.ΓSpecIso A).inv.hom
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).2)

private theorem chartScalar_injective [IsDomain A] [IsIntegral W]
    [IsDominant f] [QuasiCompact f] (U : W.Opens) [Nonempty U] :
    Function.Injective (chartScalar f U) := by
  let : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  exact (AlgebraicGeometry.map_injective_of_isIntegral W (homOfLE (le_top : U ≤ ⊤))).comp
    ((f.app_injective ⊤).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).1)

private theorem chartScalar_germ [IsDomain A] [IsIntegral W] [IsDominant f]
    (U : W.Opens) [Nonempty U] :
    CommRingCat.ofHom (chartScalar f U) ≫ W.germToFunctionField U =
      (Scheme.ΓSpecIso A).inv ≫ (Spec A).germToFunctionField ⊤ ≫
        CommRingCat.ofHom (Scheme.functionFieldMap f) := by
  let : Nonempty (⊤ : W.Opens) := ⟨⟨genericPoint W, trivial⟩⟩
  have hg : genericPoint W ∈ U :=
    ((genericPoint_spec W).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hres : W.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫
      W.germToFunctionField U = W.germToFunctionField ⊤ :=
    W.presheaf.germ_res (homOfLE (le_top : U ≤ ⊤)) (genericPoint W) hg
  rw [Scheme.functionFieldMap_germ]
  change (Scheme.ΓSpecIso A).inv ≫ f.appTop ≫
      W.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ W.germToFunctionField U =
    (Scheme.ΓSpecIso A).inv ≫ f.appTop ≫ W.germToFunctionField ⊤
  rw [hres]

private theorem chartScalar_germ_apply [IsDomain A] [IsIntegral W] [IsDominant f]
    (U : W.Opens) [Nonempty U] (a : A) :
    W.germToFunctionField U (chartScalar f U a) =
      Scheme.functionFieldMap f (algebraMap A (Spec A).functionField a) := by
  exact congrArg (fun k : A ⟶ W.functionField => k a) (chartScalar_germ f U)

private theorem chartScalar_isAlgebraic [IsDomain A] [IsIntegral W] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (U : W.Opens) [Nonempty U] :
    letI := (chartScalar f U).toAlgebra
    Algebra.IsAlgebraic A Γ(W, U) := by
  let := (chartScalar f U).toAlgebra
  let := hff
  refine ⟨fun b => ?_⟩
  obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso
    (CommRingCat.ofHom (Scheme.functionFieldMap f))).2 (W.germToFunctionField U b)
  obtain ⟨a, s, hs, has⟩ := IsFractionRing.div_surjective A z
  have hs0 : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
  have hsF : Scheme.functionFieldMap f (algebraMap A (Spec A).functionField s) ≠ 0 := by
    apply (map_ne_zero (Scheme.functionFieldMap f)).mpr
    exact (map_ne_zero_iff _ (IsFractionRing.injective A (Spec A).functionField)).mpr hs0
  have hrat : Scheme.functionFieldMap f (algebraMap A (Spec A).functionField a) /
      Scheme.functionFieldMap f (algebraMap A (Spec A).functionField s) =
        W.germToFunctionField U b := by
    rw [← map_div₀, has]
    exact hz
  have hrel : chartScalar f U s * b = chartScalar f U a := by
    apply W.germToFunctionField_injective U
    rw [map_mul, chartScalar_germ_apply, chartScalar_germ_apply]
    simpa only [mul_comm] using ((div_eq_iff hsF).mp hrat).symm
  refine ⟨Polynomial.C s * Polynomial.X - Polynomial.C a, ?_, ?_⟩
  · intro hp
    apply hs0
    have hc := congrArg (fun p : Polynomial A => p.coeff 1) hp
    simpa using hc
  · change Polynomial.aeval b (Polynomial.C s * Polynomial.X - Polynomial.C a) = 0
    simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      RingHom.algebraMap_toAlgebra, sub_eq_zero]
    exact hrel

variable [IsNoetherianRing A] [IsLocalRing A] [IsDomain A] [IsIntegral W]

omit [IsDomain A] [IsIntegral W] in
private theorem completedChart_isDomain
    [IsIntegral (pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u})]
    (U : W.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    letI := (chartScalar f U).toAlgebra
    IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A] Γ(W, U)) := by
  let C := Γ(W, U)
  let := (chartScalar f U).toAlgebra
  let H := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let D := H ⊗[A] C
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := H) (B := C)
  let : Module.FaithfullyFlat C D := tensor_faithfullyFlat A C
  let : Nontrivial D := (FaithfulSMul.algebraMap_injective C D).nontrivial
  have hu : hU.fromSpec ≫ f = Spec.algebraMap A C := chartScalar_over f U hU
  let j := Scheme.LocalRing.completionAffineChartMap (IsLocalRing.maximalIdeal A)
    C f hU.fromSpec hu
  let : IsOpenImmersion j := MorphismProperty.of_isPullback
    (Scheme.LocalRing.completionAffineChartMap_isPullback (IsLocalRing.maximalIdeal A)
      C f hU.fromSpec hu).flip inferInstance
  let : IsIntegral (Spec (.of D)) := isIntegral_of_isOpenImmersion j
  exact (affine_isIntegral_iff (.of D)).mp inferInstance

variable [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
  [IsIntegral (pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u})]
  [IsProper f] [IsDominant f]

private theorem actualNormalization_finite_app
    (hd : ringKrullDim A ≤ 2)
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (U : W.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    (((W.fromSpecStalk (genericPoint W)).fromNormalization).app U).hom.Finite := by
  let C := Γ(W, U)
  let := (chartScalar f U).toAlgebra
  let : Algebra.FiniteType A C := chartScalar_finiteType f U hU
  let : Algebra.IsAlgebraic A C := chartScalar_isAlgebraic f hff U
  let : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A] C) :=
    completedChart_isDomain f U hU
  let γ := W.fromSpecStalk (genericPoint W)
  let K := Γ(Spec W.functionField, γ ⁻¹ᵁ U)
  let := (γ.app U).hom.toAlgebra
  let : IsFractionRing C W.functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen W U hU
  let e : K ≃ₐ[C] W.functionField :=
    { (Scheme.functionFieldSectionsIso W U).commRingCatIsoToRingEquiv with
      commutes' c := by
        exact congr($(Scheme.fromSpecStalk_genericPoint_app_functionFieldSectionsIso W U) c) }
  let : IsFractionRing C K := IsFractionRing.of_algEquiv e.symm
  let : Module.Finite C (integralClosure C K) :=
    affine_normalization_finite A C hd (chartScalar_injective f U) K
  rw [Scheme.Hom.fromNormalization_app _ hU]
  exact (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (γ.normalizationObjIso hU).inv).2).comp
      (RingHom.finite_algebraMap.mpr (inferInstanceAs (Module.Finite C (integralClosure C K))))

/-- The original normalization of a proper birational surface model is finite
when the original completion and actual completed model are integral. Upper
chart finiteness comes from complete-base GF2 and descends through the original
completion map. No normality of the off-fibre locus is needed for this
finiteness-only conclusion. -/
theorem lowerNormalization_isFinite
    (hd : ringKrullDim A ≤ 2)
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f))) :
    IsFinite (W.fromSpecStalk (genericPoint W)).fromNormalization := by
  let γ := W.fromSpecStalk (genericPoint W)
  refine { toIsAffineHom := inferInstance, finite_app := ?_ }
  intro U hU
  by_cases hne : Nonempty U
  · let := hne
    exact actualNormalization_finite_app f hd hff U hU
  · have hbot : U = ⊥ := by
      apply le_antisymm
      · intro x hx
        exact (hne ⟨⟨x, hx⟩⟩).elim
      · exact bot_le
    subst U
    let : Subsingleton Γ(γ.normalization, γ.fromNormalization ⁻¹ᵁ ⊥) := by
      simpa only [Scheme.Hom.preimage_bot] using
        (inferInstanceAs (Subsingleton Γ(γ.normalization, ⊥)))
    exact RingHom.Finite.of_surjective _ (Function.surjective_to_subsingleton _)

end ActualBirationalCharts

section ActualCompletionMap

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- The original local completion map is flat and surjective. -/
theorem completion_flat_surjective :
    Flat (Scheme.LocalRing.completionSpecMap A) ∧
      Surjective (Scheme.LocalRing.completionSpecMap A) := by
  apply (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))).mpr
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr (completion_faithfullyFlat A)

variable {W : Scheme.{u}} [IsIntegral W] (f : W ⟶ Spec (.of A))
  [IsIntegral (pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u})]

/-- The actual upper normalization maps to the literal completed lower
normalization, with the original base and normalization projections. -/
def completionComparison :
    ((pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u}).fromSpecStalk
      (genericPoint
        (pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u}))).normalization ⟶
    pullback ((W.fromSpecStalk (genericPoint W)).fromNormalization ≫ f)
      (Scheme.LocalRing.completionSpecMap A) := by
  let : Surjective (Scheme.LocalRing.completionSpecMap A) := (completion_flat_surjective A).2
  exact normalizationComparison (pullback.fst f (Scheme.LocalRing.completionSpecMap A)) ≫
    (pullbackRightPullbackFstIso f (Scheme.LocalRing.completionSpecMap A)
      (W.fromSpecStalk (genericPoint W)).fromNormalization).hom

/-- The comparison keeps the original map to the completed base. -/
@[reassoc]
theorem completionComparison_snd :
    completionComparison A f ≫ pullback.snd
      ((W.fromSpecStalk (genericPoint W)).fromNormalization ≫ f)
      (Scheme.LocalRing.completionSpecMap A) =
    ((pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u}).fromSpecStalk
      (genericPoint
        (pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u}))).fromNormalization ≫
      pullback.snd f (Scheme.LocalRing.completionSpecMap A) := by
  let : Surjective (Scheme.LocalRing.completionSpecMap A) := (completion_flat_surjective A).2
  simp only [completionComparison, Category.assoc, pullbackRightPullbackFstIso_hom_snd,
    normalizationComparison_snd_assoc]

end ActualCompletionMap


private theorem integralClosure_algHom_ext
    (R K T : Type*) [CommRing R] [IsDomain R]
    [CommRing K] [Algebra R K] [IsFractionRing R K]
    [CommRing T] [IsDomain T] [Algebra R T] [FaithfulSMul R T]
    (f g : integralClosure R K →ₐ[R] T) : f = g := by
  let : Field K := IsFractionRing.toField R
  apply AlgHom.ext
  intro x
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R (x : K)
  have hbR : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbK : algebraMap R K b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hrel : algebraMap R (integralClosure R K) b * x =
      algebraMap R (integralClosure R K) a := by
    apply Subtype.ext
    change algebraMap R K b * (x : K) = algebraMap R K a
    exact (mul_comm _ _).trans ((div_eq_iff hbK).mp hab).symm
  have hf := congrArg f hrel
  have hg := congrArg g hrel
  rw [map_mul, f.commutes, f.commutes] at hf
  rw [map_mul, g.commutes, g.commutes] at hg
  have hbT : algebraMap R T b ≠ 0 := by
    intro h
    apply hbR
    exact FaithfulSMul.algebraMap_injective R T (by simpa only [map_zero] using h)
  exact mul_left_cancel₀ hbT (hf.trans hg.symm)


section CanonicalTensorUniqueness

variable (R : Type u) (S : Type u) (K : Type u) (Q : Type u)
  [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [Algebra R S] [Module.FaithfullyFlat R S]
  [CommRing K] [Algebra R K] [IsFractionRing R K]
  [CommRing Q] [Algebra S Q] [IsFractionRing S Q]

/-- Every S-algebra map on the original normalization tensor has the same
fraction values. This is an equality of the actual map, not a chosen
normalization equivalence. -/
private theorem normalizationTensorAlgHom_unique
    (g : S ⊗[R] integralClosure R K →ₐ[S] integralClosure S Q) :
    g = integralClosure.flatBaseChangeHom R S K Q := by
  let B := integralClosure S Q
  let : IsDomain Q := IsFractionRing.isDomain S
  let : Algebra R B := ((algebraMap S B).comp (algebraMap R S)).toAlgebra
  let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  have hinj : Function.Injective (algebraMap S B) := by
    intro a b hab
    apply IsFractionRing.injective S Q
    exact congrArg (fun z : B => (z : Q)) hab
  let : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).mpr
    (hinj.comp (FaithfulSMul.algebraMap_injective R S))
  let i₁ : integralClosure R K →ₐ[R] B :=
    (g.restrictScalars R).comp Algebra.TensorProduct.includeRight
  let i₂ : integralClosure R K →ₐ[R] B :=
    ((integralClosure.flatBaseChangeHom R S K Q).restrictScalars R).comp
      Algebra.TensorProduct.includeRight
  have hi : i₁ = i₂ := integralClosure_algHom_ext R K B i₁ i₂
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul s x =>
      have hx : g ((1 : S) ⊗ₜ[R] x) =
          integralClosure.flatBaseChangeHom R S K Q ((1 : S) ⊗ₜ[R] x) :=
        AlgHom.congr_fun hi x
      have hs : s ⊗ₜ[R] x = s • ((1 : S) ⊗ₜ[R] x) := by
        simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hs, map_smul, map_smul, hx]
  | add z w hz hw => simp only [map_add, hz, hw]

variable (E P B : Type u) [CommRing E] [CommRing P] [CommRing B]
  [Algebra R E] [Algebra S P] [Algebra S B]

/-- Transfer the conductor theorem to an ACTUAL affine section map. The
three equivalences have independent standard meanings: lower normalization
sections, ordinary affine pullback sections, and upper normalization sections.
None of them is the desired normalization/base-change comparison. -/
private theorem actualSectionMap_bijective_of_conductor
    (eE : E ≃ₐ[R] integralClosure R K)
    (eP : S ⊗[R] E ≃ₐ[S] P)
    (eB : B ≃ₐ[S] integralClosure S Q)
    (φ : P →ₐ[S] B)
    (J : Ideal R) (hJ : J.FG) (t : R) (ht : t ∈ J) (ht0 : t ≠ 0)
    (e : R ⧸ J ≃+* S ⧸ J.map (algebraMap R S))
    (he : ∀ r : R, e (Ideal.Quotient.mk J r) =
      Ideal.Quotient.mk (J.map (algebraMap R S)) (algebraMap R S r))
    (hcond : ∀ s ∈ J.map (algebraMap R S), ∀ b : integralClosure S Q,
      ∃ a : S, algebraMap S (integralClosure S Q) a = s • b) :
    Function.Bijective φ := by
  let eT : S ⊗[R] integralClosure R K ≃ₐ[S] P :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) eE.symm).trans eP
  let g : S ⊗[R] integralClosure R K →ₐ[S] integralClosure S Q :=
    eB.toAlgHom.comp (φ.comp eT.toAlgHom)
  have hg : g = integralClosure.flatBaseChangeHom R S K Q :=
    normalizationTensorAlgHom_unique R S K Q g
  let eN := integralClosure.flatBaseChangeEquivOfConductor
    R S K Q J hJ t ht ht0 e he hcond
  let θ : P ≃ₐ[S] B := eT.symm.trans (eN.trans eB.symm)
  have hφ : φ = θ.toAlgHom := by
    apply AlgHom.ext
    intro p
    apply eB.injective
    have hp := AlgHom.congr_fun hg (eT.symm p)
    change eB (φ p) = eB (eB.symm (eN (eT.symm p)))
    rw [eB.apply_symm_apply]
    change eB (φ p) = integralClosure.flatBaseChangeHom R S K Q (eT.symm p)
    simpa only [g, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      eT.apply_symm_apply] using hp
  rw [hφ]
  exact θ.bijective

/-- The central identification used above, on the original represented
fraction tensor. It is independent of the proof of the conductor bound. -/
private theorem actualSectionMap_tensor_equation
    (eE : E ≃ₐ[R] integralClosure R K)
    (eP : S ⊗[R] E ≃ₐ[S] P)
    (eB : B ≃ₐ[S] integralClosure S Q) (φ : P →ₐ[S] B)
    (s : S) (x : integralClosure R K) :
    eB (φ (eP (s ⊗ₜ[R] eE.symm x))) =
      integralClosure.flatBaseChangeHom R S K Q (s ⊗ₜ[R] x) := by
  let eT : S ⊗[R] integralClosure R K ≃ₐ[S] P :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) eE.symm).trans eP
  let g : S ⊗[R] integralClosure R K →ₐ[S] integralClosure S Q :=
    eB.toAlgHom.comp (φ.comp eT.toAlgHom)
  have hg := normalizationTensorAlgHom_unique R S K Q g
  have hp := AlgHom.congr_fun hg (s ⊗ₜ[R] x)
  change eB (φ (eP (Algebra.TensorProduct.map
    (AlgEquiv.refl : S ≃ₐ[S] S).toAlgHom eE.symm.toAlgHom (s ⊗ₜ[R] x)))) = _ at hp
  rw [Algebra.TensorProduct.map_tmul] at hp
  exact hp

end CanonicalTensorUniqueness


section GenericNormalizationSections

variable (X : Scheme.{u}) [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U)

private def normalizationSectionsAlgEquiv :
    letI := ((X.fromSpecStalk (genericPoint X)).app U).hom.toAlgebra
    letI := ((X.fromSpecStalk (genericPoint X)).fromNormalization.app U).hom.toAlgebra
    Γ((X.fromSpecStalk (genericPoint X)).normalization,
        (X.fromSpecStalk (genericPoint X)).fromNormalization ⁻¹ᵁ U) ≃ₐ[Γ(X, U)]
      integralClosure Γ(X, U)
        Γ(Spec X.functionField, X.fromSpecStalk (genericPoint X) ⁻¹ᵁ U) := by
  let γ := X.fromSpecStalk (genericPoint X)
  let := (γ.app U).hom.toAlgebra
  let := (γ.fromNormalization.app U).hom.toAlgebra
  refine { (γ.normalizationObjIso hU).commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro c
  have h : γ.fromNormalization.app U ≫ (γ.normalizationObjIso hU).hom =
      CommRingCat.ofHom (algebraMap Γ(X, U)
        (integralClosure Γ(X, U) Γ(Spec X.functionField, γ ⁻¹ᵁ U))) := by
    rw [Scheme.Hom.fromNormalization_app _ hU, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  exact ConcreteCategory.congr_hom h c

include hU in
private theorem genericSections_fractionRing [Nonempty U] :
    letI := ((X.fromSpecStalk (genericPoint X)).app U).hom.toAlgebra
    IsFractionRing Γ(X, U)
      Γ(Spec X.functionField, X.fromSpecStalk (genericPoint X) ⁻¹ᵁ U) := by
  let γ := X.fromSpecStalk (genericPoint X)
  let := (γ.app U).hom.toAlgebra
  let : IsFractionRing Γ(X, U) X.functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen X U hU
  let e : Γ(Spec X.functionField, γ ⁻¹ᵁ U) ≃ₐ[Γ(X, U)] X.functionField :=
    { (Scheme.functionFieldSectionsIso X U).commRingCatIsoToRingEquiv with
      commutes' c := by
        exact congr($(Scheme.fromSpecStalk_genericPoint_app_functionFieldSectionsIso X U) c) }
  exact IsFractionRing.of_algEquiv e.symm

end GenericNormalizationSections

section ActualAffineGluing

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (β : Y ⟶ X) [IsDominant β] [IsAffineHom β]

omit [IsAffineHom β] in
private theorem normalizationComparison_isIntegral :
    IsIntegralHom (normalizationComparison β) := by
  let νX := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let π₂ := pullback.snd νX β
  have : IsIntegralHom (normalizationComparison β ≫ π₂) := by
    rw [normalizationComparison_snd]
    infer_instance
  exact IsIntegralHom.of_comp (normalizationComparison β) π₂

omit [IsIntegral X] [IsDominant β] [IsAffineHom β] in
/-- The data required by the proved conductor kernel on an ACTUAL affine
section map. All scalar actions are the original section maps. This predicate
contains no model, normalization equivalence, or desired isomorphism. -/
private def affineConductorCondition (U : X.Opens) : Prop :=
  let C := Γ(X, U)
  let V := β ⁻¹ᵁ U
  let D := Γ(Y, V)
  let Q := Γ(Spec Y.functionField, Y.fromSpecStalk (genericPoint Y) ⁻¹ᵁ V)
  letI := (β.app U).hom.toAlgebra
  letI := ((Y.fromSpecStalk (genericPoint Y)).app V).hom.toAlgebra
  Module.FaithfullyFlat C D ∧
    ∃ J : Ideal C, J.FG ∧ ∃ t : C, t ∈ J ∧ t ≠ 0 ∧
      ∃ e : C ⧸ J ≃+* D ⧸ J.map (algebraMap C D),
        (∀ c : C, e (Ideal.Quotient.mk J c) =
          Ideal.Quotient.mk (J.map (algebraMap C D)) (algebraMap C D c)) ∧
        ∀ d ∈ J.map (algebraMap C D), ∀ b : integralClosure D Q,
          ∃ a : D, algebraMap D (integralClosure D Q) a = d • b

private theorem normalizationComparison_isIso_app_of_conductor
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    (hdata : affineConductorCondition β U) :
    IsIso ((normalizationComparison β).app
      (pullback.snd (X.fromSpecStalk (genericPoint X)).fromNormalization β ⁻¹ᵁ
        (β ⁻¹ᵁ U))) := by
  let γX := X.fromSpecStalk (genericPoint X)
  let γY := Y.fromSpecStalk (genericPoint Y)
  let νX := γX.fromNormalization
  let νY := γY.fromNormalization
  let Z := pullback νX β
  let π₁ : Z ⟶ γX.normalization := pullback.fst νX β
  let π₂ : Z ⟶ Y := pullback.snd νX β
  let α : γY.normalization ⟶ Z := normalizationComparison β
  let V := β ⁻¹ᵁ U
  let UE := νX ⁻¹ᵁ U
  let UP := π₂ ⁻¹ᵁ V
  let UB := νY ⁻¹ᵁ V
  have hV : IsAffineOpen V := hU.preimage β
  have hUE : IsAffineOpen UE := hU.preimage νX
  let : Nonempty V := by
    refine ⟨⟨genericPoint Y, ?_⟩⟩
    change β (genericPoint Y) ∈ U
    rw [Scheme.map_genericPoint_of_isDominant Y β]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hmap : α ≫ π₂ = νY := normalizationComparison_snd β
  have hα : UB = α ⁻¹ᵁ UP :=
    (congrArg (fun k : γY.normalization ⟶ Y => k ⁻¹ᵁ V) hmap).symm
  have hpre : π₁ ⁻¹ᵁ UE = π₂ ⁻¹ᵁ V :=
    congrArg (fun k : Z ⟶ X => k ⁻¹ᵁ U) (pullback.condition (f := νX) (g := β))
  have hUPeq : UP = π₁ ⁻¹ᵁ UE ⊓ π₂ ⁻¹ᵁ V := by
    rw [hpre, inf_idem]
  let C := Γ(X, U)
  let D := Γ(Y, V)
  let E := Γ(γX.normalization, UE)
  let P := Γ(Z, UP)
  let B := Γ(γY.normalization, UB)
  let K := Γ(Spec X.functionField, γX ⁻¹ᵁ U)
  let Q := Γ(Spec Y.functionField, γY ⁻¹ᵁ V)
  let := (β.app U).hom.toAlgebra
  let := (νX.app U).hom.toAlgebra
  let := (νY.app V).hom.toAlgebra
  let := (π₂.app V).hom.toAlgebra
  let := (γX.app U).hom.toAlgebra
  let := (γY.app V).hom.toAlgebra
  let : IsFractionRing C K := genericSections_fractionRing X U hU
  let : IsFractionRing D Q := genericSections_fractionRing Y V hV
  obtain ⟨hFF, J, hJ, t, ht, ht0, e, he, hcond⟩ := hdata
  let : Module.FaithfullyFlat C D := hFF
  let eE : E ≃ₐ[C] integralClosure C K := normalizationSectionsAlgEquiv X U hU
  let eB : B ≃ₐ[D] integralClosure D Q := normalizationSectionsAlgEquiv Y V hV
  let κ := pushoutSection (.of_hasPullback νX β) (show V ≤ β ⁻¹ᵁ U from le_rfl)
    (show UE ≤ νX ⁻¹ᵁ U from le_rfl) hUPeq
  let : IsIso κ := isIso_pushoutSection_of_isAffineOpen
    (.of_hasPullback νX β) le_rfl le_rfl hUPeq hU hV hUE
  let eP₀ : CommRingCat.of (D ⊗[C] E) ≅ Γ(Z, UP) :=
    (CommRingCat.isPushout_tensorProduct C D E).flip.isoPushout ≪≫
      pushout.congrHom νX.app_eq_appLE β.app_eq_appLE ≪≫ asIso κ
  let eP : D ⊗[C] E ≃ₐ[D] P :=
    { eP₀.commRingCatIsoToRingEquiv with
      commutes' d := by
        change (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ eP₀.hom) d =
          (π₂.app V) d
        congr 2
        change CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫
          (CommRingCat.isPushout_tensorProduct C D E).flip.isoPushout.hom ≫
            (pushout.congrHom νX.app_eq_appLE β.app_eq_appLE).hom ≫ κ = π₂.app V
        rw [IsPushout.inr_isoPushout_hom_assoc]
        change pushout.inr (νX.app U) (β.app U) ≫
          (pushout.congrHom νX.app_eq_appLE β.app_eq_appLE).hom ≫ κ = π₂.app V
        rw [pushout.congrHom_hom]
        dsimp only [pushout.map]
        rw [pushout.inr_desc_assoc, Category.id_comp]
        dsimp only [κ, pushoutSection]
        rw [pushout.inr_desc]
        exact π₂.appLE_eq_app }
  have hcoeff : π₂.app V ≫ α.appLE UP UB hα.le = νY.app V := by
    have hcoeff' (q : γY.normalization ⟶ Y) (hq : α ≫ π₂ = q) :
        π₂.app V ≫ α.appLE UP (q ⁻¹ᵁ V)
          (by rw [← hq]; exact le_rfl) = q.app V := by
      subst q
      change π₂.app V ≫ α.appLE UP (α ⁻¹ᵁ UP) le_rfl = π₂.app V ≫ α.app UP
      rw [Scheme.Hom.appLE_eq_app]
    exact hcoeff' νY hmap
  let φ : P →ₐ[D] B :=
    { (α.appLE UP UB hα.le).hom with
      commutes' d := ConcreteCategory.congr_hom hcoeff d }
  have hφ : Function.Bijective φ :=
    actualSectionMap_bijective_of_conductor C D K Q E P B
      eE eP eB φ J hJ t ht ht0 e he hcond
  have hAppLE : IsIso (α.appLE UP UB hα.le) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hφ
  let r := γY.normalization.presheaf.map (eqToHom hα).op
  let : IsIso r := by
    dsimp only [r]
    infer_instance
  have hres : (homOfLE hα.le : UB ⟶ α ⁻¹ᵁ UP) = eqToHom hα :=
    Subsingleton.elim _ _
  let : IsIso (α.app UP ≫ r) := by
    simpa only [Scheme.Hom.appLE, hres] using hAppLE
  exact IsIso.of_isIso_comp_right (α.app UP) r

/-- The original comparison is an isomorphism once the proved conductor
inputs hold on the actual affine section maps. The affine opens used below
cover the target pullback; their maps are the restrictions of one original
comparison, so there is no independent cocycle or gluing choice. -/
private theorem normalizationComparison_isIso_of_affine_conductors
    (hlocal : ∀ U : X.affineOpens, Nonempty U.1 → affineConductorCondition β U.1) :
    IsIso (normalizationComparison β) := by
  let νX := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let π₂ := pullback.snd νX β
  let : IsIntegralHom (normalizationComparison β) := normalizationComparison_isIntegral β
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := .isomorphisms _) fun z => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, _⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (β (π₂ z))) isOpen_univ
  let : Nonempty U := ⟨⟨β (π₂ z), hzU⟩⟩
  let UP := π₂ ⁻¹ᵁ (β ⁻¹ᵁ U)
  have hUP : IsAffineOpen UP := (hU.preimage β).preimage π₂
  let : IsIso ((normalizationComparison β).app UP) :=
    normalizationComparison_isIso_app_of_conductor β U hU (hlocal ⟨U, hU⟩ inferInstance)
  exact ⟨UP, hzU, (isIso_morphismRestrict_iff_isIso_app _ hUP).mpr inferInstance⟩

end ActualAffineGluing


section CompletionChartSections

variable {A : CommRingCat.{u}} [IsNoetherianRing A] [IsLocalRing A]
  {W : Scheme.{u}} (f : W ⟶ Spec A)

/-- The ordinary affine completion chart identifies the ACTUAL upper section
ring with the tensor algebra, as an algebra over the original lower sections.
Only the original affine pullback is used here, not normalization. -/
private def completionChartSectionsEquiv (U : W.Opens) (hU : IsAffineOpen U) :
    letI := (chartScalar f U).toAlgebra
    letI := ((pullback.fst f (Scheme.LocalRing.completionSpecMap A)).app U).hom.toAlgebra
    letI := Algebra.TensorProduct.rightAlgebra
      (R := A) (A := AdicCompletion (IsLocalRing.maximalIdeal A) A) (B := Γ(W, U))
    (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A] Γ(W, U)) ≃ₐ[Γ(W, U)]
      Γ((pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u}),
        pullback.fst f (Scheme.LocalRing.completionSpecMap A) ⁻¹ᵁ U) := by
  let C := Γ(W, U)
  let := (chartScalar f U).toAlgebra
  let H := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let D₀ := H ⊗[A] C
  let Y : Scheme.{u} := pullback f (Scheme.LocalRing.completionSpecMap A)
  let β : Y ⟶ W := pullback.fst f (Scheme.LocalRing.completionSpecMap A)
  let : IsAffineHom β := by
    let : MorphismProperty.IsStableUnderBaseChange
        (@IsAffineHom : MorphismProperty Scheme.{u}) :=
      isAffineHom_isStableUnderBaseChange
    exact MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback f (Scheme.LocalRing.completionSpecMap A)).flip inferInstance
  let V := β ⁻¹ᵁ U
  let := (β.app U).hom.toAlgebra
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := H) (B := C)
  have hV : IsAffineOpen V := hU.preimage β
  have hu : hU.fromSpec ≫ f = Spec.algebraMap A C := chartScalar_over f U hU
  let ρ := Scheme.LocalRing.tensorCompletionSpecMap (IsLocalRing.maximalIdeal A) C
  let j : Spec (.of D₀) ⟶ Y := Scheme.LocalRing.completionAffineChartMap
    (IsLocalRing.maximalIdeal A) C f hU.fromSpec hu
  let : IsOpenImmersion j := MorphismProperty.of_isPullback
    (Scheme.LocalRing.completionAffineChartMap_isPullback (IsLocalRing.maximalIdeal A)
      C f hU.fromSpec hu).flip inferInstance
  have hj : j ≫ β = ρ ≫ hU.fromSpec :=
    Scheme.LocalRing.completionAffineChartMap_fst (IsLocalRing.maximalIdeal A)
      C f hU.fromSpec hu
  have hrange : Set.range j = Set.range V.ι := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      have hp : β (j p) ∈ U := by
        have hpoint := congrArg (fun g : Spec (.of D₀) ⟶ W => g p) hj
        change β (j p) = hU.fromSpec (ρ p) at hpoint
        rw [hpoint]
        change hU.fromSpec (ρ p) ∈ (U : Set W)
        rw [← hU.range_fromSpec]
        exact Set.mem_range_self _
      exact ⟨⟨j p, hp⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      apply Scheme.LocalRing.exists_completionAffineChartPoint
        (IsLocalRing.maximalIdeal A) C f hU.fromSpec hu
      rw [hU.range_fromSpec]
      exact y.property
  let eJ : Spec (.of D₀) ≅ V := IsOpenImmersion.isoOfRangeEq j V.ι hrange
  let m : Spec (.of D₀) ⟶ Spec Γ(Y, V) := eJ.hom ≫ hV.isoSpec.hom
  let eR : Γ(Y, V) ≅ CommRingCat.of D₀ := (Scheme.Spec.preimageIso (asIso m)).unop
  have hm : Spec.map eR.hom = m := by simp [eR, ← Scheme.Spec_map]
  have hmj : m ≫ hV.fromSpec = j := by
    rw [← hV.isoSpec_inv_ι]
    simp only [m, Category.assoc, Iso.hom_inv_id_assoc]
    exact IsOpenImmersion.isoOfRangeEq_hom_fac j V.ι hrange
  have hβ : Spec.map (β.app U) ≫ hU.fromSpec = hV.fromSpec ≫ β := by
    simpa only [Scheme.Hom.app_eq_appLE] using
      (IsAffineOpen.SpecMap_appLE_fromSpec β hU hV le_rfl)
  have hcoeff : β.app U ≫ eR.hom =
      CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := A) (A := H) (B := C)).toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, hm]
    apply (cancel_mono hU.fromSpec).mp
    calc
      (m ≫ Spec.map (β.app U)) ≫ hU.fromSpec = m ≫ hV.fromSpec ≫ β := by
        rw [Category.assoc, hβ]
      _ = j ≫ β := by rw [← Category.assoc, hmj]
      _ = ρ ≫ hU.fromSpec := hj
      _ = _ := by
        simp only [ρ, Scheme.LocalRing.tensorCompletionSpecMap,
          AdicCompletion.tensorComparisonRingHom_eq, AlgHom.toRingHom_eq_coe]
  let r : Γ(Y, V) ≃+* D₀ := eR.commRingCatIsoToRingEquiv
  refine { r.symm with commutes' := ?_ }
  intro c
  apply r.injective
  change r (r.symm (algebraMap C D₀ c)) = r (algebraMap C Γ(Y, V) c)
  rw [r.apply_symm_apply]
  exact (ConcreteCategory.congr_hom hcoeff c).symm

end CompletionChartSections

section TensorPresentedConductor

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (A C D : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  [CommRing C] [IsDomain C] [Algebra A C] [Algebra.FiniteType A C] [Algebra.IsAlgebraic A C]
  [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
  [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A] C)]
  [CommRing D] [IsDomain D] [Algebra C D]

omit [IsDomain A] in
private theorem conductorData_of_tensorPresentation
    (hd : ringKrullDim A ≤ 2) (hinj : Function.Injective (algebraMap A C))
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) (ha0 : a ≠ 0)
    (Q : Type u) [CommRing Q] [Algebra D Q] [IsFractionRing D Q]
    (e₀ : (AdicCompletion (IsLocalRing.maximalIdeal A) A ⊗[A] C) ≃ₐ[C] D)
    (hNormal : ∀ p : PrimeSpectrum D,
      ¬ ((IsLocalRing.maximalIdeal A).map (algebraMap A C)).map (algebraMap C D) ≤ p.asIdeal →
        IsIntegrallyClosed (Localization.AtPrime p.asIdeal)) :
    Module.FaithfullyFlat C D ∧
      ∃ J : Ideal C, J.FG ∧ ∃ t : C, t ∈ J ∧ t ≠ 0 ∧
        ∃ e : C ⧸ J ≃+* D ⧸ J.map (algebraMap C D),
          (∀ c : C, e (Ideal.Quotient.mk J c) =
            Ideal.Quotient.mk (J.map (algebraMap C D)) (algebraMap C D c)) ∧
          ∀ d ∈ J.map (algebraMap C D), ∀ b : integralClosure D Q,
            ∃ c : D, algebraMap D (integralClosure D Q) c = d • b := by
  let H := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let D₀ := H ⊗[A] C
  let := Algebra.TensorProduct.rightAlgebra (R := A) (A := H) (B := C)
  let : Module.FaithfullyFlat C D₀ := tensor_faithfullyFlat A C
  let : Module.FaithfullyFlat C D :=
    Module.FaithfullyFlat.of_linearEquiv C D₀ e₀.symm.toLinearEquiv
  have hN₀ := tensor_isNagata A C hd hinj
  let : Algebra D₀ D := e₀.toRingHom.toAlgebra
  let : Module.Finite D₀ D := RingHom.Finite.of_surjective e₀.toRingHom e₀.surjective
  have hN : IsNagataRing.{u, 0} D := hN₀.of_finite
  let : IsNoetherianRing D := hN.isNoetherianRing
  let : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
  let : Field Q := IsFractionRing.toField D
  let : Module.Finite D (integralClosure D Q) := integralClosure.finite_of_isNagataRing D hN Q
  let I : Ideal C := (IsLocalRing.maximalIdeal A).map (algebraMap A C)
  obtain ⟨n, hn⟩ := exists_normalization_conductor_pow D Q
    (I.map (algebraMap C D)) (I.map (algebraMap C D)).fg_of_isNoetherianRing hNormal
  let J := I ^ n
  have hpow : ((IsLocalRing.maximalIdeal A) ^ n).map (algebraMap A C) ≤ J := by
    rw [Ideal.map_pow]
  let q₀ : C ⧸ J ≃+* D₀ ⧸ J.map (algebraMap C D₀) :=
    AdicCompletion.quotientTensorCompletionEquiv (IsLocalRing.maximalIdeal A) C
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing n J hpow
  have he₀ : e₀.toRingHom.comp (algebraMap C D₀) = algebraMap C D := by
    ext c
    exact e₀.commutes c
  have hmap : J.map (algebraMap C D) = (J.map (algebraMap C D₀)).map e₀.toRingHom := by
    rw [Ideal.map_map, he₀]
  let q₁ := Ideal.quotientEquiv (J.map (algebraMap C D₀)) (J.map (algebraMap C D))
    e₀.toRingEquiv hmap
  have hq₀ (c : C) : q₀ (Ideal.Quotient.mk J c) =
      Ideal.Quotient.mk (J.map (algebraMap C D₀)) (algebraMap C D₀ c) :=
    AdicCompletion.quotientTensorCompletionEquiv_mk (IsLocalRing.maximalIdeal A) C
      (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing n J hpow c
  have hq₁ (d : D₀) : q₁ (Ideal.Quotient.mk (J.map (algebraMap C D₀)) d) =
      Ideal.Quotient.mk (J.map (algebraMap C D)) (e₀ d) :=
    Ideal.quotientEquiv_mk (J.map (algebraMap C D₀)) (J.map (algebraMap C D))
      e₀.toRingEquiv hmap d
  let e : C ⧸ J ≃+* D ⧸ J.map (algebraMap C D) := q₀.trans q₁
  refine ⟨inferInstance, J, J.fg_of_isNoetherianRing, (algebraMap A C a) ^ n,
    Ideal.pow_mem_pow (Ideal.mem_map_of_mem (algebraMap A C) ha) n,
    pow_ne_zero n (fun h => ha0 (hinj (by simpa only [map_zero] using h))), e, ?_, ?_⟩
  · intro c
    dsimp only [e, RingEquiv.trans_apply]
    rw [hq₀, hq₁, e₀.commutes]
  · intro d hd' b
    apply hn d
    simpa only [J, Ideal.map_pow] using hd'

end TensorPresentedConductor


section ActualClosedFibreData

variable {A : CommRingCat.{u}} [IsLocalRing A] {X Y : Scheme.{u}}
  (g : X ⟶ Spec A) (β : Y ⟶ X) (U : X.Opens)

omit [IsLocalRing A] in
private theorem chartScalar_comp :
    chartScalar (β ≫ g) (β ⁻¹ᵁ U) = (β.app U).hom.comp (chartScalar g U) := by
  have he : U ≤ g ⁻¹ᵁ ⊤ := by simp
  have hc := Scheme.Hom.appLE_comp_appLE β g ⊤ U (β ⁻¹ᵁ U) he le_rfl
  have h : CommRingCat.ofHom (chartScalar (β ≫ g) (β ⁻¹ᵁ U)) =
      CommRingCat.ofHom (chartScalar g U) ≫ β.app U := by
    change (Scheme.ΓSpecIso A).inv ≫ (β ≫ g).appLE ⊤ (β ⁻¹ᵁ U) (by simp) =
      ((Scheme.ΓSpecIso A).inv ≫ g.appLE ⊤ U he) ≫ β.app U
    rw [Category.assoc]
    simpa only [Scheme.Hom.appLE_eq_app] using
      congrArg (fun k : Γ(Spec A, ⊤) ⟶ Γ(Y, β ⁻¹ᵁ U) =>
        (Scheme.ΓSpecIso A).inv ≫ k) hc.symm
  exact congrArg (fun k : A ⟶ Γ(Y, β ⁻¹ᵁ U) => k.hom) h

private theorem affineChart_normal_atPrime
    (hNormal : ∀ x : X, ¬ IsLocalRing.maximalIdeal A ≤ (g x).asIdeal →
      IsIntegrallyClosed (X.presheaf.stalk x))
    (hU : IsAffineOpen U) :
    ∀ p : PrimeSpectrum Γ(X, U),
      ¬ (IsLocalRing.maximalIdeal A).map (chartScalar g U) ≤ p.asIdeal →
        IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := by
  intro p hp
  let j := hU.fromSpec
  let : IsOpenImmersion j := by
    dsimp only [j]
    infer_instance
  let : IsIso (j.stalkMap p) :=
    ((IsOpenImmersion.iff_isIso_stalkMap (f := j)).mp
      (inferInstance : IsOpenImmersion j)).2 p
  have hpoint : g (j p) = Spec.map (CommRingCat.ofHom (chartScalar g U)) p :=
    congrArg (fun k : Spec Γ(X, U) ⟶ Spec A => k p) (chartScalar_over g U hU)
  have hnot : ¬ IsLocalRing.maximalIdeal A ≤ (g (j p)).asIdeal := by
    intro hm
    apply hp
    rw [Ideal.map_le_iff_le_comap]
    rw [hpoint] at hm
    exact hm
  let : IsIntegrallyClosed (X.presheaf.stalk (j p)) := hNormal (j p) hnot
  let e : X.presheaf.stalk (j p) ≃+* Localization.AtPrime p.asIdeal :=
    ((asIso (j.stalkMap p)).commRingCatIsoToRingEquiv).trans
      (Spec.stalkIso Γ(X, U) p).commRingCatIsoToRingEquiv
  exact IsIntegrallyClosed.of_equiv e

end ActualClosedFibreData

private theorem exists_nonzero_closedFibre_scalar {A : CommRingCat.{u}}
    [IsLocalRing A] (hd : ringKrullDim A = 2) :
    ∃ a : A, a ∈ IsLocalRing.maximalIdeal A ∧ a ≠ 0 := by
  have hm : IsLocalRing.maximalIdeal A ≠ ⊥ := by
    intro h
    let : Field A := (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h).toField
    have hzero : ringKrullDim A ≤ 0 :=
      Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 0 A)
    rw [hd] at hzero
    norm_num at hzero
  exact Submodule.exists_mem_ne_zero_of_ne_bot hm

section CompletionCapstone

variable {A : CommRingCat.{u}} [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
  {W : Scheme.{u}} [IsIntegral W] (f : W ⟶ Spec A) [IsProper f] [IsDominant f]
  [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
  [IsIntegral (pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u})]

omit [IsDomain A] [IsProper f] [IsDominant f]
  [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A)] in
/-- The other projection is the normalization lift of the original upper
normalization followed by the original completion projection. -/
@[reassoc]
theorem completionComparison_fst :
    let Y : Scheme.{u} := pullback f (Scheme.LocalRing.completionSpecMap A)
    letI := (completion_flat_surjective A).2
    letI := genericNormalization_isDominant Y
    completionComparison A f ≫ pullback.fst
        ((W.fromSpecStalk (genericPoint W)).fromNormalization ≫ f)
        (Scheme.LocalRing.completionSpecMap A) =
      genericNormalizationLift
        ((Y.fromSpecStalk (genericPoint Y)).fromNormalization ≫
          pullback.fst f (Scheme.LocalRing.completionSpecMap A))
        (genericNormalization_normalStalks Y) := by
  let Y : Scheme.{u} := pullback f (Scheme.LocalRing.completionSpecMap A)
  let : Surjective (Scheme.LocalRing.completionSpecMap A) := (completion_flat_surjective A).2
  let := genericNormalization_isDominant Y
  simp only [completionComparison, Category.assoc, pullbackRightPullbackFstIso_hom_fst,
    normalizationComparison_fst]

omit [IsDomain A] [IsProper f] [IsDominant f]
  [IsDomain (AdicCompletion (IsLocalRing.maximalIdeal A) A)] in
/-- The generic arrow is the one built from the original function-field map
of the original composite. No unrelated field marking is introduced. -/
@[reassoc]
theorem completionComparison_generic_fst :
    let Y : Scheme.{u} := pullback f (Scheme.LocalRing.completionSpecMap A)
    let N := (Y.fromSpecStalk (genericPoint Y)).normalization
    letI := (completion_flat_surjective A).2
    letI := genericNormalization_isDominant Y
    N.fromSpecStalk (genericPoint N) ≫ completionComparison A f ≫ pullback.fst
        ((W.fromSpecStalk (genericPoint W)).fromNormalization ≫ f)
        (Scheme.LocalRing.completionSpecMap A) =
      genericNormalizationLiftGeneric
        ((Y.fromSpecStalk (genericPoint Y)).fromNormalization ≫
          pullback.fst f (Scheme.LocalRing.completionSpecMap A)) := by
  let Y : Scheme.{u} := pullback f (Scheme.LocalRing.completionSpecMap A)
  let : Surjective (Scheme.LocalRing.completionSpecMap A) := (completion_flat_surjective A).2
  let := genericNormalization_isDominant Y
  dsimp only
  rw [completionComparison_fst, genericNormalizationLift_generic]

private theorem completion_affineConductorCondition
    (hd : ringKrullDim A = 2)
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (hNormal : ∀ y : (pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u}),
      ¬ IsLocalRing.maximalIdeal A ≤
          (f (pullback.fst f (Scheme.LocalRing.completionSpecMap A) y)).asIdeal →
        IsIntegrallyClosed
          ((pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u}).presheaf.stalk y))
    (U : W.affineOpens) (hne : Nonempty U.1) :
    letI := (completion_flat_surjective A).2
    affineConductorCondition (pullback.fst f (Scheme.LocalRing.completionSpecMap A)) U.1 := by
  let : Nonempty U.1 := hne
  let : Surjective (Scheme.LocalRing.completionSpecMap A) := (completion_flat_surjective A).2
  let Y : Scheme.{u} := pullback f (Scheme.LocalRing.completionSpecMap A)
  let β : Y ⟶ W := pullback.fst f (Scheme.LocalRing.completionSpecMap A)
  let : IsAffineHom β := by
    let : MorphismProperty.IsStableUnderBaseChange
        (@IsAffineHom : MorphismProperty Scheme.{u}) :=
      isAffineHom_isStableUnderBaseChange
    exact MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback f (Scheme.LocalRing.completionSpecMap A)).flip inferInstance
  let V := β ⁻¹ᵁ U.1
  have hV : IsAffineOpen V := U.2.preimage β
  let : Nonempty V := by
    refine ⟨⟨genericPoint Y, ?_⟩⟩
    change β (genericPoint Y) ∈ U.1
    rw [Scheme.map_genericPoint_of_isDominant Y β]
    exact ((genericPoint_spec W).mem_open_set_iff U.1.isOpen).mpr (by simpa using hne)
  let C := Γ(W, U.1)
  let D := Γ(Y, V)
  let H := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let := (chartScalar f U.1).toAlgebra
  let : Algebra.FiniteType A C := chartScalar_finiteType f U.1 U.2
  let : Algebra.IsAlgebraic A C := chartScalar_isAlgebraic f hff U.1
  let : IsDomain (H ⊗[A] C) := completedChart_isDomain f U.1 U.2
  let := (β.app U.1).hom.toAlgebra
  let γY := Y.fromSpecStalk (genericPoint Y)
  let Q := Γ(Spec Y.functionField, γY ⁻¹ᵁ V)
  let := (γY.app V).hom.toAlgebra
  let : IsFractionRing D Q := genericSections_fractionRing Y V hV
  let e₀ := completionChartSectionsEquiv f U.1 U.2
  have hI : ((IsLocalRing.maximalIdeal A).map (algebraMap A C)).map (algebraMap C D) =
      (IsLocalRing.maximalIdeal A).map (chartScalar (β ≫ f) V) := by
    rw [Ideal.map_map, chartScalar_comp]
    rfl
  have hDnormal : ∀ p : PrimeSpectrum D,
      ¬ ((IsLocalRing.maximalIdeal A).map (algebraMap A C)).map (algebraMap C D) ≤ p.asIdeal →
        IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := by
    intro p hp
    apply affineChart_normal_atPrime (β ≫ f) V
      (fun y hy => hNormal y hy) hV p
    rwa [← hI]
  obtain ⟨a, ha, ha0⟩ := exists_nonzero_closedFibre_scalar (A := A) hd
  exact conductorData_of_tensorPresentation A C D hd.le (chartScalar_injective f U.1)
    a ha ha0 Q e₀ hDnormal

/-- On the original proper birational model, finite normalization and the
canonical completion comparison are consequences of the completed chart
finiteness and off-closed-fibre normality. No desired lower finiteness,
normalization comparison, Nagata property of A, or excellence input occurs.

The explicit complete-domain hypothesis is weaker than normal completion;
the intended normalized-blowup consumer supplies it from normal completion.
Normality of the actual completed model off the closed fibre remains explicit. -/
theorem finite_normalization_and_isIso_completionComparison
    (hd : ringKrullDim A = 2)
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (hNormal : ∀ y : (pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u}),
      ¬ IsLocalRing.maximalIdeal A ≤
          (f (pullback.fst f (Scheme.LocalRing.completionSpecMap A) y)).asIdeal →
        IsIntegrallyClosed
          ((pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u}).presheaf.stalk y)) :
    IsFinite (W.fromSpecStalk (genericPoint W)).fromNormalization ∧
      IsIso (completionComparison A f) := by
  refine ⟨lowerNormalization_isFinite f hd.le hff, ?_⟩
  let : Surjective (Scheme.LocalRing.completionSpecMap A) := (completion_flat_surjective A).2
  let β := pullback.fst f (Scheme.LocalRing.completionSpecMap A)
  let : IsAffineHom β := by
    let : MorphismProperty.IsStableUnderBaseChange
        (@IsAffineHom : MorphismProperty Scheme.{u}) :=
      isAffineHom_isStableUnderBaseChange
    exact MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback f (Scheme.LocalRing.completionSpecMap A)).flip inferInstance
  let : IsIso (normalizationComparison β) :=
    normalizationComparison_isIso_of_affine_conductors β
      (completion_affineConductorCondition f hd hff hNormal)
  dsimp only [completionComparison]
  infer_instance

/-- Both the object and forward morphism are the actual normalization and
the actual previously constructed completion comparison. -/
def normalizationCompletionIso
    (hd : ringKrullDim A = 2)
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (hNormal : ∀ y : (pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u}),
      ¬ IsLocalRing.maximalIdeal A ≤
          (f (pullback.fst f (Scheme.LocalRing.completionSpecMap A) y)).asIdeal →
        IsIntegrallyClosed
          ((pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u}).presheaf.stalk y)) :
    ((pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u}).fromSpecStalk
      (genericPoint
        (pullback f (Scheme.LocalRing.completionSpecMap A) : Scheme.{u}))).normalization ≅
    pullback ((W.fromSpecStalk (genericPoint W)).fromNormalization ≫ f)
      (Scheme.LocalRing.completionSpecMap A) := by
  let := (finite_normalization_and_isIso_completionComparison f hd hff hNormal).2
  exact asIso (completionComparison A f)

end CompletionCapstone




end AlgebraicGeometry.Scheme.CompletionNormalization
