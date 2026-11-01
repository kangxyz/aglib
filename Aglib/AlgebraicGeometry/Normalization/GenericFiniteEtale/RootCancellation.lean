/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.OpenRecoveryAffine
public import Aglib.RingTheory.Kummer.RootComplement
public import Aglib.RingTheory.Kummer.NormalizedCancellation
public import Aglib.RingTheory.Localization.FractionRing

/-! # Cancellation for the original finite-etale cover of a parameter complement

The regular root scheme and the literal complement map determine the original
function-field tensor. Open recovery on that regular scheme supplies the
complement condition for algebraic cancellation. Neither normality nor a
comparison of normalization with ramified base change is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Algebra.Kummer
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation

universe u

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  (f : R) (hf : f ∈ IsLocalRing.maximalIdeal R)
  [IsRegularLocalRing (R ⧸ Ideal.span {f})]
  (N : ℕ) (hN : 0 < N) (hreg : IsSMulRegular R f)

local notation "T" => RootAlgebra N f
local notation "θ" => AdjoinRoot.root (rootPolynomial N f)
local notation "U" => Localization.Away f
local notation "V" => Localization.Away θ

include hreg in
omit [IsNoetherianRing R] [IsRegularLocalRing (R ⧸ Ideal.span {f})] in
/-- A regular parameter is nonzero in the original local ring. -/
theorem parameter_ne_zero : f ≠ 0 := by
  intro hz
  exact one_ne_zero (hreg (by simp [hz]))

include hN hreg in
omit [IsLocalRing R] [IsNoetherianRing R]
  [IsRegularLocalRing (R ⧸ Ideal.span {f})] in
/-- The original root remains nonzero over a nontrivial root algebra. -/
theorem root_ne_zero [Nontrivial T] : θ ≠ 0 := by
  intro hz
  exact one_ne_zero ((parameterRoot_root_regular R f N hN hreg) (by simp [hz]))

include hf hN hreg

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual native relative normalization of the original pulled-back
cover's generic source is etale over the regular root scheme. Regularity,
domain and normality are constructed, as are the original function-field
actions and the complement condition. No generic comparison is an input. -/
theorem fromNormalization_etale :
    letI : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
    letI : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
    letI : IsDomain U := Localization.Away.isDomain (parameter_ne_zero R f hreg)
    letI : IsRegularLocalRing T := parameterRoot_isRegularLocalRing R f hf N hN hreg
    letI : IsDomain T := IsRegularLocalRing.isDomain_of_regularLocal T
    letI : IsDomain V := Localization.Away.isDomain (root_ne_zero R f N hN hreg)
    ∀ (Y : Scheme.FiniteEtale (Spec (.of U))) [IsIntegral Y.obj.left]
      [CategoryTheory.PreGaloisCategory.IsGalois Y],
    IsUnit (N : R) → Nat.card (Aut Y) ∣ N →
    Etale (Hom.fromNormalization (OpenRecovery.genericMap (Spec.algebraMap T V)
      ((Scheme.FiniteEtale.baseChange
        (Spec.map (CommRingCat.ofHom (rootComplementHom N f)))).obj Y).obj.hom)) := by
  let : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
  let : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
  let : IsDomain U := Localization.Away.isDomain (parameter_ne_zero R f hreg)
  let : IsRegularLocalRing T := parameterRoot_isRegularLocalRing R f hf N hN hreg
  let : IsDomain T := IsRegularLocalRing.isDomain_of_regularLocal T
  let : IsDomain V := Localization.Away.isDomain (root_ne_zero R f N hN hreg)
  intro Y hYint hYgal hunit hcard
  have hf0 : f ≠ 0 := parameter_ne_zero R f hreg
  let : Algebra U V := (rootComplementHom N f).toAlgebra
  let : IsScalarTower R U V :=
    IsScalarTower.of_algebraMap_eq fun r => (rootComplementHom_algebraMap N f r).symm
  let j := Spec.algebraMap T V
  let g := Spec.algebraMap U V
  let : IsDominant g := by
    constructor
    change DenseRange (PrimeSpectrum.comap (rootComplementHom N f))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp
        (rootComplementHom_injective N f hN hf0)]
    exact bot_le
  let K := (Spec (.of U)).functionField
  let F := (Spec (.of T)).functionField
  let L := Y.obj.left.functionField
  let : Algebra U K := AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of U)
  let : Algebra T F := AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of T)
  let : IsFractionRing U K := AlgebraicGeometry.functionField_isFractionRing_of_affine (.of U)
  let : IsFractionRing T F := AlgebraicGeometry.functionField_isFractionRing_of_affine (.of T)
  let : Algebra R K := ((algebraMap U K).comp (algebraMap R U)).toAlgebra
  let : IsScalarTower R U K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra R F := ((algebraMap T F).comp (algebraMap R T)).toAlgebra
  let : IsScalarTower R T F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra K F := OpenRecovery.baseChangeFieldAlgebra j g
  let : IsScalarTower R K F := OpenRecovery.baseChangeFieldAlgebra_isScalarTower R U T V
  let : IsFractionRing R K := IsFractionRing.of_domain_localization (S := U)
    (Submonoid.powers f)
  let : Algebra K L := GenericGalois.algebra Y
  let : IsIntegrallyClosed T := IsRegularLocalRing.isIntegrallyClosed_of_regularLocal T
  let : ∀ z : Spec (.of T), IsIntegrallyClosed ((Spec (.of T)).presheaf.stalk z) :=
    fun z => (isIntegrallyClosed_and_isDomain_stalk_Spec T z).1
  let : Module.Finite K L := (GenericGalois.functionField_finiteEtale Y).1
  let : _root_.IsGalois K L := GenericGalois.functionField_isGalois Y
  let A := F ⊗[K] L
  let : Algebra.Etale T (Localization.Away (algebraMap T (integralClosure T A) θ)) :=
    OpenRecovery.baseChange_integralClosure_away_etale T θ g Y
  let : Algebra.Etale T (integralClosure T A) := by
    apply parameterRoot_normalization_etale_of_away R f hf N hN hreg K F L hunit
    rwa [GenericGalois.card_functionFieldAut Y]
  let q := OpenRecovery.genericMap j ((Scheme.FiniteEtale.baseChange g).obj Y).obj.hom
  let e := OpenRecovery.baseChangeFieldSpectrumIso j g Y
  have he : e.hom ≫ q = Spec.algebraMap T A := by
    rw [OpenRecovery.baseChangeFieldSpectrumIso_hom_genericMap, Spec.fromSpecStalk_eq']
    change Spec.algebraMap F A ≫ Spec.algebraMap T F = _
    simp only [Spec.algebraMap, ← Spec.map_comp]
    congr 1
  let n := Hom.specIntegralClosureNormalizationIso T A ≪≫
    Hom.normalizationSourceIso e (Spec.algebraMap T A) q he
  have hn : n.hom ≫ q.fromNormalization =
      Spec.algebraMap T (integralClosure T A) := by
    simp only [n, Iso.trans_hom, Category.assoc,
      Hom.normalizationSourceIso_hom_over,
      Hom.specIntegralClosureNormalizationIso_hom_over]
  have hb : Etale (Spec.algebraMap T (integralClosure T A)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  have hq : q.fromNormalization = n.inv ≫ Spec.algebraMap T (integralClosure T A) := by
    rw [← hn]
    simp
  change Etale q.fromNormalization
  rw [hq]
  infer_instance

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation
