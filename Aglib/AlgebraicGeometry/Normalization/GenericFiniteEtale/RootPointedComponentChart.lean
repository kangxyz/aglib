/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RootOpenChart
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.ComponentRecognition
public import Aglib.AlgebraicGeometry.Spec.IntegralChartPoint

/-! # The pointed root chart on the actual finite normal component

The original open lift constructs the root chart of the original open cover's
native normalization. The actual finite normal component is recognized by its
original open inclusion, not a supplied normalization comparison. Their
composition retains the base, generic source and specified boundary point.
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
/-- Construct the actual component's pointed chart from its original open
cover, genuine root-complement lift and primitive-root data. -/
theorem exists_pointedComponentRootChart :
    letI : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
    letI : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
    letI : IsDomain U := Localization.Away.isDomain (parameter_ne_zero R f hreg)
    letI : IsRegularLocalRing T := parameterRoot_isRegularLocalRing R f hf N hN hreg
    letI : IsDomain T := IsRegularLocalRing.isDomain_of_regularLocal T
    letI : IsDomain V := Localization.Away.isDomain (root_ne_zero R f N hN hreg)
    ∀ (Y : Scheme.FiniteEtale (Spec (.of U))) [IsIntegral Y.obj.left],
    ∀ (C : Scheme.{u}) [IsIntegral C] (_hC : C.NormalStalks)
      (p : C ⟶ Spec (.of R)) [IsFinite p]
      (b : Y.obj.left ⟶ C) [IsOpenImmersion b],
    b ≫ p = Y.obj.hom ≫ j₀ →
    ∀ (x : C), p x = IsLocalRing.closedPoint R →
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
    ∃ (e : ℕ) (β : L) (hβ : β ^ e = algebraMap R L f),
      ∃ he : 0 < e, e ∣ N ∧ IsUnit (e : R) ∧
      ∃ c : Spec (.of (RootAlgebra e f)) ≅ C,
        c.hom ≫ p = Spec.algebraMap R (RootAlgebra e f) ∧
        Spec.map (CommRingCat.ofHom (rootEvaluation R L e f β hβ).toRingHom) ≫ c.hom =
          Y.obj.left.fromSpecStalk (genericPoint Y.obj.left) ≫ b ∧
        letI : IsLocalRing (RootAlgebra e f) := parameterRoot_isLocalRing R f hf e he
        c.hom (IsLocalRing.closedPoint _) = x := by
  let : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
  let : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
  let : IsDomain U := Localization.Away.isDomain (parameter_ne_zero R f hreg)
  let : IsRegularLocalRing T := parameterRoot_isRegularLocalRing R f hf N hN hreg
  let : IsDomain T := IsRegularLocalRing.isDomain_of_regularLocal T
  let : IsDomain V := Localization.Away.isDomain (root_ne_zero R f N hN hreg)
  dsimp only
  intro Y hYint C hCint hC p hp b hbopen hb x hx hunit
  let K := (Spec (.of U)).functionField
  let L := Y.obj.left.functionField
  let : Algebra U K := AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of U)
  let : Algebra K L := GenericGalois.algebra Y
  let : Algebra R K := ((algebraMap U K).comp (algebraMap R U)).toAlgebra
  let : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  intro hroots a ha
  obtain ⟨e, β, hβ, he, heN, heunit, c₀, hbase₀, hgen₀⟩ :=
    exists_rootChart_of_open_lift_and_primitiveRoots R f hf N hN hreg Y hunit hroots a ha
  let : IsIntegrallyClosed R := IsRegularLocalRing.isIntegrallyClosed_of_regularLocal R
  let : ∀ r : Spec (.of R), IsIntegrallyClosed ((Spec (.of R)).presheaf.stalk r) :=
    fun r => (isIntegrallyClosed_and_isDomain_stalk_Spec R r).1
  let c₁ := OpenRecovery.componentRecognitionIso j₀ Y hC p b hb
  let c := c₀ ≪≫ c₁
  have hbase : c.hom ≫ p = Spec.algebraMap R (RootAlgebra e f) := by
    simp only [c, c₁, Iso.trans_hom, Category.assoc,
      OpenRecovery.componentRecognitionIso_hom_over, hbase₀]
  refine ⟨e, β, hβ, he, heN, heunit, c, hbase, ?_, ?_⟩
  · change _ ≫ c₀.hom ≫ c₁.hom = _
    dsimp only [c₁]
    rw [← Category.assoc, hgen₀, Category.assoc, OpenRecovery.componentRecognitionIso_hom_generic,
      ← Category.assoc, OpenRecovery.originalFieldSpectrumIso_hom_toCover]
  · let : IsLocalRing (RootAlgebra e f) := parameterRoot_isLocalRing R f hf e he
    let : Module.Finite R (RootAlgebra e f) := root_finite e he f
    exact integralLocalChart_closedPoint R (RootAlgebra e f) p c hbase x hx

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation
