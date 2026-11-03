/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RootPointedPrincipalChart

/-! # The transverse-facing original pointed etale root presentation

This thin consumer keeps the very same principal coefficient ring and actual
root scheme constructed by the full pointed chart theorem. Its map to the
original normalization is etale, retains the entire original base triangle,
and contains the specified original point. No extra scheme or field is chosen;
the stronger chart, generic and two-direction comparisons remain in the producer.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Opposite Algebra.Kummer

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation

universe u

/-- Extract the same genuine principal root presentation at the original point,
with its etale source map and complete original structural equation. -/
theorem exists_etaleRootPresentation_at
    (R Ω : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Field Ω] [IsSepClosed Ω] [Algebra R Ω] [IsLocalHom (algebraMap R Ω)]
    (f : R) (hf : f ∈ IsLocalRing.maximalIdeal R)
    [IsRegularLocalRing (R ⧸ Ideal.span {f})]
    (N : ℕ) (hN : 0 < N) (hreg : IsSMulRegular R f) :
    letI : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
    letI : IsRegularRing R := IsRegularLocalRing.isRegularRing_of_regularLocal R
    letI : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
    letI : ∀ t : Spec (.of R), IsIntegrallyClosed ((Spec (.of R)).presheaf.stalk t) :=
      fun t => @IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _ _
        (regularStalks_spec R t)
    let U := Localization.Away f
    letI : IsDomain U := Localization.Away.isDomain (parameter_ne_zero R f hreg)
    ∀ (Y : Scheme.FiniteEtale (Spec (.of U))) [IsIntegral Y.obj.left]
      [CategoryTheory.PreGaloisCategory.IsGalois Y],
    IsUnit (N : R) → Nat.card (Aut Y) ∣ N →
    let q₀ := OpenRecovery.genericMap (Spec.algebraMap R U) Y.obj.hom
    ∀ (x : q₀.normalization), q₀.fromNormalization x = IsLocalRing.closedPoint R →
    ∀ _X₀ : GeometricEtaleNeighborhood R Ω,
    ∃ (A : CommRingCat.{u}) (aRA : Algebra R A),
    letI : Algebra R A := aRA
    Algebra.Etale R A ∧
    ∃ (n : ℕ), 0 < n ∧ n ∣ N ∧ IsUnit (n : R) ∧
    ∃ η : Spec (.of (RootAlgebra n (algebraMap R A f))) ⟶ q₀.normalization,
      Etale η ∧
      η ≫ q₀.fromNormalization =
        Spec.algebraMap A (RootAlgebra n (algebraMap R A f)) ≫ Spec.algebraMap R A ∧
      ∃ w : Spec (.of (RootAlgebra n (algebraMap R A f))), η w = x := by
  let : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
  let : IsRegularRing R := IsRegularLocalRing.isRegularRing_of_regularLocal R
  let : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
  let U := Localization.Away f
  let : IsDomain U := Localization.Away.isDomain (parameter_ne_zero R f hreg)
  dsimp only
  intro Y hY hG hunit hcard x hx X₀
  have hdata := exists_nativePointedPrincipalRootChart R Ω f hf N hN hreg
    Y hunit hcard x hx X₀
  obtain ⟨X, k, z, hD, hR, hz, hzS, e, a, heB, heG, heE, haB,
    hInt, hNorm, hfin, l, hl, hlS, hlx, hYS, n, β, hβ, hn, hnN, hnunit,
    chart, hbase, hgeneric, hpoint, J, chart', hetaleA, hpointA,
    hbase', hhom, hinv, hpoint'⟩ := hdata
  let := hD
  let := hR
  let B := X.algebra
  let S := GeometricEtaleColimit.stageLocalRing R Ω X
  let TS := RootAlgebra N (algebraMap R S f)
  let : IsLocalRing TS := parameterRoot_isLocalRing S (algebraMap R S f)
    (map_nonunit (algebraMap R S) f hf) N hN
  let V := Localization.Away (algebraMap R B f)
  let : IsDomain V := Localization.Away.isDomain
    (OpenRecovery.parameter_etale_algebraMap_ne_zero R B f (parameter_ne_zero R f hreg))
  let jB := Spec.algebraMap B V
  let g := Spec.map (CommRingCat.ofHom (parameterComplementBaseChangeHom B f))
  let pB := ((baseChange g).obj Y).obj.hom
  let qB := OpenRecovery.genericMap jB pB
  let q₀ := OpenRecovery.genericMap (Spec.algebraMap R U) Y.obj.hom
  let : ∀ t : Spec (.of B), IsIntegrallyClosed ((Spec (.of B)).presheaf.stalk t) := by
    intro t
    let : IsRegularLocalRing ((Spec (.of B)).presheaf.stalk t) := regularStalks_spec B t
    exact IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _
  let : IsFinite qB.fromNormalization := OpenRecovery.fromNormalization_isFinite jB pB
  let : IsLocallyNoetherian qB.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian qB.fromNormalization
  let xB := a (IsLocalRing.closedPoint TS)
  let C := normalComponentOpen qB.normalization (OpenRecovery.genericMap_normalStalks jB pB) xB
  let c := C.ι ≫ qB.fromNormalization
  let M := (Localization.ResiduePoint.ideal X.point.toRingHom).primeCompl
  let A := IsLocalization.PrincipalDiagram.stage M J.left.unop
  let bA := (Scheme.PrincipalNeighborhoodLimit.baseStructure M).app J.left
  let : Etale (Spec.algebraMap R B) := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  let : Etale bA := by
    change Etale (Spec.algebraMap B A)
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  let π : pullback c bA ⟶ q₀.normalization :=
    pullback.fst c bA ≫ C.ι ≫ e.hom ≫ pullback.fst q₀.fromNormalization (Spec.algebraMap R B)
  let η := chart'.hom ≫ π
  have hπ : π ≫ q₀.fromNormalization = pullback.snd c bA ≫ bA ≫ Spec.algebraMap R B := by
    dsimp only [π]
    rw [Category.assoc, Category.assoc, Category.assoc, pullback.condition,
      ← Category.assoc e.hom, heB]
    change pullback.fst c bA ≫ c ≫ Spec.algebraMap R B = _
    rw [← Category.assoc, pullback.condition, Category.assoc]
  have hbaseA : chart'.hom ≫ pullback.snd c bA =
      Spec.algebraMap A (RootAlgebra n (algebraMap R A f)) := hbase'
  have hcoeff : bA ≫ Spec.algebraMap R B = Spec.algebraMap R A :=
    Spec.map_algHom_algebraMap (IsScalarTower.toAlgHom R B A)
  have hη : η ≫ q₀.fromNormalization =
      Spec.algebraMap A (RootAlgebra n (algebraMap R A f)) ≫ Spec.algebraMap R A := by
    calc
      _ = chart'.hom ≫ (π ≫ q₀.fromNormalization) := Category.assoc _ _ _
      _ = chart'.hom ≫ (pullback.snd c bA ≫ bA ≫ Spec.algebraMap R B) :=
        congrArg (fun v => chart'.hom ≫ v) hπ
      _ = (chart'.hom ≫ pullback.snd c bA) ≫ (bA ≫ Spec.algebraMap R B) :=
        (Category.assoc _ _ _).symm
      _ = Spec.algebraMap A (RootAlgebra n (algebraMap R A f)) ≫
          (bA ≫ Spec.algebraMap R B) :=
        congrArg (fun v => v ≫ (bA ≫ Spec.algebraMap R B)) hbaseA
      _ = _ := congrArg (fun v =>
        Spec.algebraMap A (RootAlgebra n (algebraMap R A f)) ≫ v) hcoeff
  have hparam := GeometricEtaleNeighborhood.regularParameter_pointLocalization R Ω X f hf hreg
  let : IsLocalRing (RootAlgebra n (algebraMap R S f)) :=
    parameterRoot_isLocalRing S (algebraMap R S f) hparam.2.2.2.1 n hn
  refine ⟨.of A, inferInstance, hetaleA, n, hn, hnN,
    isUnit_of_dvd_unit hnN.natCast hunit, η, ?_, hη, ?_⟩
  · dsimp only [η, π]
    infer_instance
  · exact ⟨Scheme.Kummer.rootPrincipalComparison n (algebraMap R B f) M S J
      (IsLocalRing.closedPoint (RootAlgebra n (algebraMap R S f))), hpoint'⟩

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation
