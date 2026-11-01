/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RootCartesianChart
public import Aglib.AlgebraicGeometry.Spec.ParameterComplementBaseChange
public import Aglib.CategoryTheory.Limits.Shapes.PullbackSquareBaseChange

/-! # The root chart of the original base-changed finite component

The original covering source and component are base changed literally. Their
Cartesian square supplies the local chart; neither an integral pulled-back
cover nor a normalization comparison is a premise. Normality of the actual
component pullback is supplied by the separate localization theorem.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Algebra.Kummer

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation

universe u

variable (B S : Type u) [CommRing B] [CommRing S] [Algebra B S]
  [IsLocalRing S] [IsNoetherianRing S] (f : B)
  (hf : algebraMap B S f ∈ IsLocalRing.maximalIdeal S)
  [IsRegularLocalRing (S ⧸ Ideal.span {algebraMap B S f})]
  (N : ℕ) (hN : 0 < N) (hreg : IsSMulRegular S (algebraMap B S f))

local notation "fS" => algebraMap B S f
local notation "U" => Localization.Away f
local notation "US" => Localization.Away fS
local notation "TS" => RootAlgebra N fS
local notation "VS" => Localization.Away (AdjoinRoot.root (rootPolynomial N fS))
local notation "g" => Spec.map (CommRingCat.ofHom (parameterComplementBaseChangeHom S f))

include hf hN hreg

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Construct the pointed chart of the literal base-changed component. -/
theorem exists_baseChangedComponentRootChart :
    letI : IsRegularLocalRing S := IsRegularLocalRing.of_quotient_span_singleton S fS hreg
    letI : IsDomain S := IsRegularLocalRing.isDomain_of_regularLocal S
    letI : IsDomain US := Localization.Away.isDomain (parameter_ne_zero S fS hreg)
    letI : IsRegularLocalRing TS := parameterRoot_isRegularLocalRing S fS hf N hN hreg
    letI : IsDomain TS := IsRegularLocalRing.isDomain_of_regularLocal TS
    letI : IsDomain VS := Localization.Away.isDomain (root_ne_zero S fS N hN hreg)
    ∀ (Y : Scheme.FiniteEtale (Spec (.of U))) (C : Scheme.{u})
      (p : C ⟶ Spec (.of B)) (b : Y.obj.left ⟶ C)
      (H : IsPullback b Y.obj.hom p (Spec.algebraMap B U)),
    let CS := pullback p (Spec.algebraMap B S)
    ∀ [IsIntegral CS] (_hC : NormalStalks CS) [IsFinite (pullback.snd p (Spec.algebraMap B S))]
      (a : Spec (.of TS) ⟶ CS),
    a ≫ pullback.snd p (Spec.algebraMap B S) = Spec.algebraMap S TS →
    ∀ (x : CS), pullback.snd p (Spec.algebraMap B S) x = IsLocalRing.closedPoint S →
    IsUnit (N : S) →
    (primitiveRoots N ((Spec (.of US)).functionField)).Nonempty →
    let YS := (Scheme.FiniteEtale.baseChange g).obj Y
    let bS := H.baseChangeSquareMap (Scheme.Kummer.parameterComplementBaseChange_isPullback B S f)
    ∃ hYS : IsIntegral YS.obj.left,
    letI : IsIntegral YS.obj.left := hYS
    let K := (Spec (.of US)).functionField
    let L := YS.obj.left.functionField
    letI : Algebra US K := AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of US)
    letI : Algebra K L := GenericGalois.algebra YS
    letI : Algebra S K := ((algebraMap US K).comp (algebraMap S US)).toAlgebra
    letI : Algebra S L := ((algebraMap K L).comp (algebraMap S K)).toAlgebra
    ∃ (e : ℕ) (β : L) (hβ : β ^ e = algebraMap S L fS),
      ∃ he : 0 < e, e ∣ N ∧ IsUnit (e : S) ∧
      ∃ c : Spec (.of (RootAlgebra e fS)) ≅ CS,
        c.hom ≫ pullback.snd p (Spec.algebraMap B S) = Spec.algebraMap S (RootAlgebra e fS) ∧
        Spec.map (CommRingCat.ofHom (rootEvaluation S L e fS β hβ).toRingHom) ≫ c.hom =
          YS.obj.left.fromSpecStalk (genericPoint YS.obj.left) ≫ bS ∧
        letI : IsLocalRing (RootAlgebra e fS) := parameterRoot_isLocalRing S fS hf e he
        c.hom (IsLocalRing.closedPoint _) = x := by
  let : IsRegularLocalRing S := IsRegularLocalRing.of_quotient_span_singleton S fS hreg
  let : IsDomain S := IsRegularLocalRing.isDomain_of_regularLocal S
  let : IsDomain US := Localization.Away.isDomain (parameter_ne_zero S fS hreg)
  let : IsRegularLocalRing TS := parameterRoot_isRegularLocalRing S fS hf N hN hreg
  let : IsDomain TS := IsRegularLocalRing.isDomain_of_regularLocal TS
  let : IsDomain VS := Localization.Away.isDomain (root_ne_zero S fS N hN hreg)
  dsimp only
  intro Y C p b H hCS hC hp a ha x hx hunit hroots
  let YS := (Scheme.FiniteEtale.baseChange g).obj Y
  let K := Scheme.Kummer.parameterComplementBaseChange_isPullback B S f
  exact exists_pointedRootChart_of_cartesianLift S fS hf N hN hreg YS
    (pullback p (Spec.algebraMap B S)) hC (pullback.snd p (Spec.algebraMap B S))
    (H.baseChangeSquareMap K) (H.baseChangeSquareMap_isPullback K) a ha x hx hunit hroots

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation
