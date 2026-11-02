/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RootChart
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.OpenSectionEmbedding

/-! # Original root charts from a genuine lift on the complement

The actual covering field embedding is obtained on the original open using
its native generic fibre. The complete lower power and integral-closure
recognition and the shared original normalization comparison then construct
the chart. No normalization/base-change comparison is an input.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Algebra.Kummer

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
local notation "j₀" => Spec.algebraMap R U

include hf hN hreg

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- At an actual Noetherian regular local stage, a genuine lift on the original root
complement and primitive roots construct the original normalization chart.
The embedding and all generic/source comparisons are constructed internally.
Neighborhood consumers construct this lift from the descended original
root-cover map and ordinary open recovery, not normalization base change. -/
theorem exists_rootChart_of_open_lift_and_primitiveRoots :
    letI : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
    letI : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
    letI : IsDomain U := Localization.Away.isDomain (parameter_ne_zero R f hreg)
    letI : IsRegularLocalRing T := parameterRoot_isRegularLocalRing R f hf N hN hreg
    letI : IsDomain T := IsRegularLocalRing.isDomain_of_regularLocal T
    letI : IsDomain V := Localization.Away.isDomain (root_ne_zero R f N hN hreg)
    ∀ (Y : Scheme.FiniteEtale (Spec (.of U))) [IsIntegral Y.obj.left],
    IsUnit (N : R) →
    let K := (Spec (.of U)).functionField
    let L := Y.obj.left.functionField
    letI : Algebra U K := AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of U)
    letI : Algebra K L := GenericGalois.algebra Y
    letI : Algebra R K := ((algebraMap U K).comp (algebraMap R U)).toAlgebra
    letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
    (primitiveRoots N K).Nonempty →
    ∀ (a : Spec (.of V) ⟶ Y.obj.left),
    a ≫ Y.obj.hom = Spec.map (CommRingCat.ofHom (rootComplementHom N f)) →
    let q := OpenRecovery.genericMap j₀ Y.obj.hom
    ∃ (e : ℕ) (β : L) (hβ : β ^ e = algebraMap R L f),
      0 < e ∧ e ∣ N ∧ IsUnit (e : R) ∧
      ∃ c : Spec (.of (RootAlgebra e f)) ≅ q.normalization,
        c.hom ≫ q.fromNormalization = Spec.algebraMap R (RootAlgebra e f) ∧
        Spec.map (CommRingCat.ofHom (rootEvaluation R L e f β hβ).toRingHom) ≫ c.hom =
          (OpenRecovery.originalFieldSpectrumIso j₀ Y).hom ≫ q.toNormalization := by
  let : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
  let : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
  let : IsDomain U := Localization.Away.isDomain (parameter_ne_zero R f hreg)
  let : IsRegularLocalRing T := parameterRoot_isRegularLocalRing R f hf N hN hreg
  let : IsDomain T := IsRegularLocalRing.isDomain_of_regularLocal T
  let : IsDomain V := Localization.Away.isDomain (root_ne_zero R f N hN hreg)
  intro Y hYint hunit
  let K := (Spec (.of U)).functionField
  let L := Y.obj.left.functionField
  let : Algebra U K := AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of U)
  let : Algebra K L := GenericGalois.algebra Y
  let : Algebra R K := ((algebraMap U K).comp (algebraMap R U)).toAlgebra
  let : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R U K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsFractionRing U K := AlgebraicGeometry.functionField_isFractionRing_of_affine (.of U)
  let : IsFractionRing R K := IsFractionRing.of_domain_localization (S := U)
    (Submonoid.powers f)
  let : Algebra U V := (rootComplementHom N f).toAlgebra
  let : IsScalarTower R U V :=
    IsScalarTower.of_algebraMap_eq fun r => (rootComplementHom_algebraMap N f r).symm
  let j := Spec.algebraMap T V
  let g := Spec.algebraMap U V
  let : IsDominant g := rootComplement_dominant R N f hN (parameter_ne_zero R f hreg)
  let F := (Spec (.of T)).functionField
  let : Algebra T F := AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of T)
  let : IsFractionRing T F := AlgebraicGeometry.functionField_isFractionRing_of_affine (.of T)
  let : Algebra R F := ((algebraMap T F).comp (algebraMap R T)).toAlgebra
  let : IsScalarTower R T F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra K F := OpenRecovery.baseChangeFieldAlgebra j g
  let : IsScalarTower R K F := OpenRecovery.baseChangeFieldAlgebra_isScalarTower R U T V
  dsimp only
  intro hroots a ha
  obtain ⟨i⟩ := OpenRecovery.exists_generic_embedding_of_open_lift j g Y a ha
  obtain ⟨e, β, hβ, he, heN, heunit, c, hc, _⟩ :=
    exists_rootIntegralClosureEquiv_of_embedding_of_primitiveRoots
      R f hf N hN hreg K F L hunit hroots i
  obtain ⟨chart, hbase, hgeneric⟩ := exists_originalRootChart R f Y e β hβ c hc
  exact ⟨e, β, hβ, he, heN, heunit, chart, hbase, hgeneric⟩


end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation
