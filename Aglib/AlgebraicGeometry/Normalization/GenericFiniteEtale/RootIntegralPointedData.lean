/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RootNativePoint
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RootPointedRefinement
public import Aglib.AlgebraicGeometry.Spec.GeometricNeighborhoodIntegralStage
public import Aglib.RingTheory.RegularLocalRing.PrimeLocalization
public import Aglib.AlgebraicGeometry.Spec.GeometricNeighborhoodRootLocalPoint

/-! # Integral regular pointed root stages from the original boundary point

The specified point belongs to the original native normalization. Its lift to
the normalized root cover is constructed by the actual integral-closure map.
The finite etale root cover then supplies a pointed section and one primitive
root at the same genuine neighborhood. The original point is retained also
on the actual point localization, without a normalization base-change premise.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite Algebra.Kummer

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An original boundary point supplies the whole pointed finite-stage data.
All lifts are constructed; neither a section nor a comparison is a premise. -/
theorem exists_nativeRootStage_integralPointedData
    (R Ω : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Field Ω] [IsSepClosed Ω] [Algebra R Ω] [IsLocalHom (algebraMap R Ω)]
    (f : R) (hf : f ∈ IsLocalRing.maximalIdeal R)
    [IsRegularLocalRing (R ⧸ Ideal.span {f})]
    (N : ℕ) (hN : 0 < N) (hreg : IsSMulRegular R f) :
    letI : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
    letI : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
    let U := Localization.Away f
    let T := RootAlgebra N f
    let V := Localization.Away (AdjoinRoot.root (rootPolynomial N f))
    letI : IsDomain U := Localization.Away.isDomain (parameter_ne_zero R f hreg)
    letI : IsRegularLocalRing T := parameterRoot_isRegularLocalRing R f hf N hN hreg
    letI : IsDomain T := IsRegularLocalRing.isDomain_of_regularLocal T
    letI : IsDomain V := Localization.Away.isDomain (root_ne_zero R f N hN hreg)
    ∀ (Y : Scheme.FiniteEtale (Spec (.of U))) [IsIntegral Y.obj.left]
      [CategoryTheory.PreGaloisCategory.IsGalois Y],
    IsUnit (N : R) → Nat.card (Aut Y) ∣ N →
    let q₀ := OpenRecovery.genericMap (Spec.algebraMap R U) Y.obj.hom
    let q₁ := OpenRecovery.genericMap (Spec.algebraMap T V)
      ((Scheme.FiniteEtale.baseChange
        (Spec.map (CommRingCat.ofHom (rootComplementHom N f)))).obj Y).obj.hom
    ∀ (x : q₀.normalization), q₀.fromNormalization x = IsLocalRing.closedPoint R →
    ∀ (X₀ : GeometricEtaleNeighborhood R Ω),
    ∃ m : q₁.normalization ⟶ q₀.normalization,
      m ≫ q₀.fromNormalization = q₁.fromNormalization ≫ Spec.algebraMap R T ∧
      ∃ (X : GeometricEtaleNeighborhood R Ω) (_ : X₀ ⟶ X) (z : X.algebra)
        (b : (Scheme.Kummer.rootDiagram R Ω N f).obj (op X) ⟶ q₁.normalization),
        IsDomain X.algebra ∧ IsRegularRing X.algebra ∧ IsPrimitiveRoot z N ∧
        IsPrimitiveRoot (algebraMap X.algebra
          (GeometricEtaleColimit.stageLocalRing R Ω X) z) N ∧
        b ≫ q₁.fromNormalization = (Scheme.Kummer.rootStructure R Ω N f).app (op X) ∧
        let S := GeometricEtaleColimit.stageLocalRing R Ω X
        letI : IsLocalRing (RootAlgebra N (algebraMap R S f)) :=
          parameterRoot_isLocalRing S (algebraMap R S f)
            (map_nonunit (algebraMap R S) f hf) N hN
        (Scheme.Kummer.rootLocalStageMap R Ω N f X ≫ b) ≫ q₁.fromNormalization =
          Spec.map (CommRingCat.ofHom (rootBaseChangeHom S N f).toRingHom) ∧
        (Scheme.Kummer.rootLocalStageMap R Ω N f X ≫ b ≫ m)
          (IsLocalRing.closedPoint _) = x := by
  let : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
  let : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
  let U := Localization.Away f
  let T := RootAlgebra N f
  let V := Localization.Away (AdjoinRoot.root (rootPolynomial N f))
  let : IsDomain U := Localization.Away.isDomain (parameter_ne_zero R f hreg)
  let : IsRegularLocalRing T := parameterRoot_isRegularLocalRing R f hf N hN hreg
  let : IsDomain T := IsRegularLocalRing.isDomain_of_regularLocal T
  let : IsDomain V := Localization.Away.isDomain (root_ne_zero R f N hN hreg)
  dsimp only
  intro Y hY hG hunit hcard
  let q₀ := OpenRecovery.genericMap (Spec.algebraMap R U) Y.obj.hom
  let q₁ := OpenRecovery.genericMap (Spec.algebraMap T V)
    ((Scheme.FiniteEtale.baseChange
      (Spec.map (CommRingCat.ofHom (rootComplementHom N f)))).obj Y).obj.hom
  let : IsIntegrallyClosed T := IsRegularLocalRing.isIntegrallyClosed_of_regularLocal T
  let : ∀ t : Spec (.of T), IsIntegrallyClosed ((Spec (.of T)).presheaf.stalk t) :=
    fun t => (isIntegrallyClosed_and_isDomain_stalk_Spec T t).1
  let : IsFinite q₁.fromNormalization := OpenRecovery.fromNormalization_isFinite _ _
  let : Etale q₁.fromNormalization :=
    fromNormalization_etale R f hf N hN hreg Y hunit hcard
  intro x hx X₀
  obtain ⟨m, hm, _, y, hmy, hy⟩ :=
    exists_nativeNormalizedRootPoint R f hf N hN hreg Y x hx
  let : IsRegularRing R := IsRegularLocalRing.isRegularRing_of_regularLocal R
  let P (X : GeometricEtaleNeighborhood R Ω) := IsDomain X.algebra ∧ IsRegularRing X.algebra
  have hP : ∀ X : GeometricEtaleNeighborhood R Ω, ∃ Y, Nonempty (X ⟶ Y) ∧ P Y := by
    intro X
    obtain ⟨_, _, _, Y, _, k, _, hdom, hregular⟩ :=
      GeometricEtaleNeighborhood.exists_integral_refinement R Ω X
    exact ⟨Y, ⟨k⟩, hdom, hregular⟩
  obtain ⟨a, _, hay, ζ, _, X, k, z, b, hX, _, hz, hzl, hb, hba⟩ :=
    Scheme.Kummer.exists_rootStage_pointedData_refinement R Ω N hN hunit f hf
      q₁.fromNormalization P hP X₀ y hy
  refine ⟨m, hm, X, k, z, b, hX.1, hX.2, hz, hzl, hb, ?_⟩
  let S := GeometricEtaleColimit.stageLocalRing R Ω X
  let : IsLocalRing (RootAlgebra N (algebraMap R S f)) :=
    parameterRoot_isLocalRing S (algebraMap R S f)
      (map_nonunit (algebraMap R S) f hf) N hN
  obtain ⟨hbase, hpoint⟩ := Scheme.Kummer.rootLocalStage_lift_point
    R Ω N hN f hf X q₁.fromNormalization b hb a hba
  refine ⟨hbase, ?_⟩
  change m ((Scheme.Kummer.rootLocalStageMap R Ω N f X ≫ b)
    (IsLocalRing.closedPoint _)) = x
  rw [hpoint, hay, hmy]

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation
