/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RootEmbedding
public import Aglib.RingTheory.Kummer.StrictHenselianSubextension

/-! # Original generic-source comparisons for root charts

The original covering function field is identified with the actual generic
cover used by native normalization. Both its unchanged covering-source map
and its ambient-base map are retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- The whole affine algebra-chart comparison, before specializing its middle
ring to an integral closure. Both actual structural triangles are retained. -/
theorem exists_specAlgEquivChart
    (R B C L : Type u) [CommRing R] [CommRing B] [CommRing C] [CommRing L]
    [Algebra R B] [Algebra R C] [Algebra R L]
    (c : B ≃ₐ[R] C) (v : B →ₐ[R] L) (w : C →ₐ[R] L)
    (hc : ∀ b, w (c b) = v b) :
    ∃ d : Spec (.of B) ≅ Spec (.of C),
      d.hom ≫ Spec.algebraMap R C = Spec.algebraMap R B ∧
      Spec.map (CommRingCat.ofHom v.toRingHom) ≫ d.hom =
        Spec.map (CommRingCat.ofHom w.toRingHom) := by
  let d : Spec (.of B) ≅ Spec (.of C) :=
    Scheme.Spec.mapIso c.symm.toRingEquiv.toCommRingCatIso.op
  refine ⟨d, ?_, ?_⟩
  · change Spec.map (CommRingCat.ofHom c.symm.toAlgHom.toRingHom) ≫
      Spec.algebraMap R C = Spec.algebraMap R B
    exact Spec.map_algHom_algebraMap c.symm.toAlgHom
  · have hd : v.toRingHom.comp c.symm.toRingHom = w.toRingHom := by
      ext b
      change v (c.symm b) = w b
      simpa only [AlgEquiv.apply_symm_apply] using (hc (c.symm b)).symm
    change Spec.map (CommRingCat.ofHom v.toRingHom) ≫
      Spec.map (CommRingCat.ofHom c.symm.toRingHom) = _
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext hd

/-- Transport a literal integral-closure algebra chart to native normalization,
retaining both its base and original generic-source maps. -/
theorem exists_affineNormalizationChart
    (R B L : Type u) [CommRing R] [CommRing B] [CommRing L]
    [Algebra R B] [Algebra R L] {Z : Scheme.{u}} (q : Z ⟶ Spec (.of R))
    [QuasiCompact q] [QuasiSeparated q]
    (e : Spec (.of L) ≅ Z) (he : e.hom ≫ q = Spec.algebraMap R L)
    (c : B ≃ₐ[R] integralClosure R L) (v : B →ₐ[R] L)
    (hc : ∀ b, (c b : L) = v b) :
    ∃ chart : Spec (.of B) ≅ q.normalization,
      chart.hom ≫ q.fromNormalization = Spec.algebraMap R B ∧
      Spec.map (CommRingCat.ofHom v.toRingHom) ≫ chart.hom =
        e.hom ≫ q.toNormalization := by
  let n := specIntegralClosureNormalizationIso R L ≪≫
    normalizationSourceIso e (Spec.algebraMap R L) q he
  have hn : n.hom ≫ q.fromNormalization = Spec.algebraMap R (integralClosure R L) := by
    simp only [n, Iso.trans_hom, Category.assoc,
      normalizationSourceIso_hom_over, specIntegralClosureNormalizationIso_hom_over]
  have hng : Spec.map (CommRingCat.ofHom (integralClosure R L).val.toRingHom) ≫ n.hom =
      e.hom ≫ q.toNormalization := by
    dsimp only [n]
    rw [Iso.trans_hom, ← Category.assoc,
      specIntegralClosureNormalizationIso_hom_generic, normalizationSourceIso_hom_generic]
  obtain ⟨d, hdb, hdg⟩ := exists_specAlgEquivChart R B (integralClosure R L) L c v
    (integralClosure R L).val hc
  refine ⟨d ≪≫ n, ?_, ?_⟩
  · change (d.hom ≫ n.hom) ≫ q.fromNormalization = _
    rw [Category.assoc, hn]
    exact hdb
  · change _ ≫ (d.hom ≫ n.hom) = _
    rw [← Category.assoc, hdg, hng]

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation

open Algebra.Kummer

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The complete original-source adapter for an algebraic root chart.
The actual covering field and both native normalization triangles are retained. -/
theorem exists_originalRootChart
    (R : Type u) [CommRing R] [IsDomain R] (f : R)
    [IsDomain (Localization.Away f)]
    (Y : Scheme.FiniteEtale (Spec (.of (Localization.Away f)))) [IsIntegral Y.obj.left] :
    let K := (Spec (.of (Localization.Away f))).functionField
    let L := Y.obj.left.functionField
    letI : Algebra (Localization.Away f) K :=
      AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of (Localization.Away f))
    letI : Algebra K L := GenericGalois.algebra Y
    letI : Algebra R K := ((algebraMap (Localization.Away f) K).comp
      (algebraMap R (Localization.Away f))).toAlgebra
    letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
    ∀ (e : ℕ) (β : L) (hβ : β ^ e = algebraMap R L f)
      (c : RootAlgebra e f ≃ₐ[R] integralClosure R L),
      (∀ x, (c x : L) = rootEvaluation R L e f β hβ x) →
      let q := OpenRecovery.genericMap (Spec.algebraMap R (Localization.Away f)) Y.obj.hom
      ∃ chart : Spec (.of (RootAlgebra e f)) ≅ q.normalization,
        chart.hom ≫ q.fromNormalization = Spec.algebraMap R (RootAlgebra e f) ∧
        Spec.map (CommRingCat.ofHom (rootEvaluation R L e f β hβ).toRingHom) ≫ chart.hom =
          (OpenRecovery.originalFieldSpectrumIso
            (Spec.algebraMap R (Localization.Away f)) Y).hom ≫ q.toNormalization := by
  let U := Localization.Away f
  let K := (Spec (.of U)).functionField
  let L := Y.obj.left.functionField
  let : Algebra U K := AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of U)
  let : Algebra K L := GenericGalois.algebra Y
  let : Algebra R K := ((algebraMap U K).comp (algebraMap R U)).toAlgebra
  let : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  dsimp only
  intro e β hβ c hc
  let j := Spec.algebraMap R U
  let q := OpenRecovery.genericMap j Y.obj.hom
  let e₀ := OpenRecovery.originalFieldSpectrumIso j Y
  let : IsDominant Y.obj.hom := GenericGalois.dominant Y
  have he₀ : e₀.hom ≫ q = Spec.algebraMap R L := by
    rw [OpenRecovery.originalFieldSpectrumIso_hom_genericMap,
      ← Category.assoc, fromSpecStalk_genericPoint_naturality Y.obj.hom]
    rw [Spec.fromSpecStalk_eq']
    change (Spec.algebraMap K L ≫ Spec.algebraMap U K) ≫ Spec.algebraMap R U = _
    simp only [Spec.algebraMap, ← Spec.map_comp]
    congr 1
  exact Hom.exists_affineNormalizationChart
    R (RootAlgebra e f) L q e₀ he₀ c (rootEvaluation R L e f β hβ) hc

section General

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
/-- At an actual Noetherian regular local stage, a supplied genuine root-cover
section and primitive roots construct the original normalization chart.
The embedding and all generic/source comparisons are constructed internally.
Neighborhood consumers must descend the section and primitive data first. -/
theorem exists_rootChart_of_section_and_primitiveRoots :
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
    ∀ (s : Spec (.of T) ⟶ (OpenRecovery.genericMap (Spec.algebraMap T V)
      ((Scheme.FiniteEtale.baseChange (Spec.map (CommRingCat.ofHom
        (rootComplementHom N f)))).obj Y).obj.hom).normalization),
    s ≫ (OpenRecovery.genericMap (Spec.algebraMap T V)
      ((Scheme.FiniteEtale.baseChange (Spec.map (CommRingCat.ofHom
        (rootComplementHom N f)))).obj Y).obj.hom).fromNormalization = 𝟙 _ →
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
  intro hroots s hs
  obtain ⟨i⟩ := OpenRecovery.exists_generic_embedding_of_normalization_section T θ g Y s hs
  obtain ⟨e, β, hβ, he, heN, heunit, c, hc, _⟩ :=
    exists_rootIntegralClosureEquiv_of_embedding_of_primitiveRoots
      R f hf N hN hreg K F L hunit hroots i
  obtain ⟨chart, hbase, hgeneric⟩ := exists_originalRootChart R f Y e β hβ c hc
  exact ⟨e, β, hβ, he, heN, heunit, chart, hbase, hgeneric⟩

end General

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)] [IsNoetherianRing R]
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
/-- The original normalization over an explicitly Noetherian strictly Henselian
regular-parameter base has an actual literal root chart. Its exponent is
positive, invertible, and divides the original bound. The chart retains both
the original base map and the original generic-source map. Neither a root
chart nor a generic embedding is a hypothesis. -/
theorem exists_rootChart :
    letI : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
    letI : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
    letI : IsDomain U := Localization.Away.isDomain (parameter_ne_zero R f hreg)
    ∀ (Y : Scheme.FiniteEtale (Spec (.of U))) [IsIntegral Y.obj.left]
      [CategoryTheory.PreGaloisCategory.IsGalois Y],
    IsUnit (N : R) → Nat.card (Aut Y) ∣ N →
    let K := (Spec (.of U)).functionField
    let L := Y.obj.left.functionField
    letI : Algebra U K := AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of U)
    letI : Algebra K L := GenericGalois.algebra Y
    letI : Algebra R K := ((algebraMap U K).comp (algebraMap R U)).toAlgebra
    letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
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
  intro Y hYint hYgal hunit hcard
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
  let : IsRegularLocalRing T := parameterRoot_isRegularLocalRing R f hf N hN hreg
  let : IsDomain T := IsRegularLocalRing.isDomain_of_regularLocal T
  let : IsDomain V := Localization.Away.isDomain (root_ne_zero R f N hN hreg)
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
  obtain ⟨i⟩ := exists_generic_embedding R f hf N hN hreg Y hunit hcard
  obtain ⟨e, β, hβ, he, heN, heunit, c, hc, _⟩ :=
    exists_rootIntegralClosureEquiv_of_embedding R f hf N hN hreg K F L hunit i
  obtain ⟨chart, hbase, hgeneric⟩ := exists_originalRootChart R f Y e β hβ c hc
  exact ⟨e, β, hβ, he, heN, heunit, chart, hbase, hgeneric⟩

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation
