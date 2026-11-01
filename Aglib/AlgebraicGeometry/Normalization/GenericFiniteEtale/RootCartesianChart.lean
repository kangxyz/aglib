/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RootPointedComponentChart
public import Aglib.AlgebraicGeometry.Spec.RootCartesianOpenLift

/-! # Pointed root charts from the actual Cartesian open cover

A whole-root lift into the original finite normal component constructs its
chart. Integrality of the original covering source and the required open lift
are derived internally from the Cartesian square, not supplied as premises.
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
/-- Construct the pointed chart directly from the unchanged Cartesian cover
and whole-root lift; no integral-cover or normalization-comparison premise. -/
theorem exists_pointedRootChart_of_cartesianLift :
    letI : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
    letI : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
    letI : IsDomain U := Localization.Away.isDomain (parameter_ne_zero R f hreg)
    letI : IsRegularLocalRing T := parameterRoot_isRegularLocalRing R f hf N hN hreg
    letI : IsDomain T := IsRegularLocalRing.isDomain_of_regularLocal T
    letI : IsDomain V := Localization.Away.isDomain (root_ne_zero R f N hN hreg)
    ∀ (Y : Scheme.FiniteEtale (Spec (.of U)))
      (C : Scheme.{u}) [IsIntegral C] (_hC : C.NormalStalks)
      (p : C ⟶ Spec (.of R)) [IsFinite p]
      (b : Y.obj.left ⟶ C),
    IsPullback b Y.obj.hom p j₀ →
    ∀ (a : Spec (.of T) ⟶ C), a ≫ p = Spec.algebraMap R T →
    ∀ (x : C), p x = IsLocalRing.closedPoint R →
    IsUnit (N : R) →
    (primitiveRoots N ((Spec (.of U)).functionField)).Nonempty →
    ∃ hY : IsIntegral Y.obj.left,
    letI : IsIntegral Y.obj.left := hY
    let K := (Spec (.of U)).functionField
    let L := Y.obj.left.functionField
    letI : Algebra U K := AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of U)
    letI : Algebra K L := GenericGalois.algebra Y
    letI : Algebra R K := ((algebraMap U K).comp (algebraMap R U)).toAlgebra
    letI : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
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
  intro Y C hCint hC p hp b H a ha x hx hunit hroots
  let : IsIntegral Y.obj.left := Scheme.Kummer.isIntegral_of_rootComplementLift
    R N f b Y.obj.hom p H a ha
  let : IsOpenImmersion b := MorphismProperty.of_isPullback H.flip inferInstance
  obtain ⟨v, _, hv⟩ := Scheme.Kummer.exists_rootComplementLift_of_isPullback
    R N f b Y.obj.hom p H a ha
  refine ⟨inferInstance, ?_⟩
  exact exists_pointedComponentRootChart R f hf N hN hreg Y C hC p b H.w
    x hx hunit hroots v hv

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation
