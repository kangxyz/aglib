/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RootIntegralPointedData
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RootStageBoundaryLift
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.ParameterPointTransport
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.PointComponentLocalization

/-! # The original point on the localized genuine-stage component

The actual original normalization point supplies the genuine integral regular
stage, its primitive root and the local root lift. Genuine etale normalization
base change transports that lift to the original stage normalization. The
component is selected by this very lift, and its literal localization retains
the original boundary point, without a supplied comparison or section.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Opposite Algebra.Kummer

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation

universe u

/-- The actual localized integral normal component and whole-root lift attached
to the original normalization point, after any prescribed genuine stage. -/
theorem exists_nativeRootPointedComponentData
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
    ∀ X₀ : GeometricEtaleNeighborhood R Ω,
    ∃ (X : GeometricEtaleNeighborhood R Ω) (_ : X₀ ⟶ X) (z : X.algebra)
      (hD : IsDomain X.algebra) (hR : IsRegularRing X.algebra),
    letI := hD
    letI := hR
    let B := X.algebra
    let S := GeometricEtaleColimit.stageLocalRing R Ω X
    let TS := RootAlgebra N (algebraMap R S f)
    letI : IsLocalRing TS := parameterRoot_isLocalRing S (algebraMap R S f)
      (map_nonunit (algebraMap R S) f hf) N hN
    let V := Localization.Away (algebraMap R B f)
    letI : IsDomain V := Localization.Away.isDomain
      (OpenRecovery.parameter_etale_algebraMap_ne_zero R B f (parameter_ne_zero R f hreg))
    let jB := Spec.algebraMap B V
    let g := Spec.map (CommRingCat.ofHom (parameterComplementBaseChangeHom B f))
    letI : IsDominant g := Scheme.Kummer.parameterComplementBaseChange_dominant R B f
      (parameter_ne_zero R f hreg)
    let pB := ((baseChange g).obj Y).obj.hom
    let qB := OpenRecovery.genericMap jB pB
    letI : ∀ t : Spec (.of B), IsIntegrallyClosed ((Spec (.of B)).presheaf.stalk t) :=
      fun t => @IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _ _
        (regularStalks_spec B t)
    letI : IsFinite qB.fromNormalization := OpenRecovery.fromNormalization_isFinite jB pB
    letI : IsLocallyNoetherian qB.normalization :=
      LocallyOfFiniteType.isLocallyNoetherian qB.fromNormalization
    IsPrimitiveRoot z N ∧ IsPrimitiveRoot (algebraMap B S z) N ∧
    ∃ (e : qB.normalization ≅ pullback q₀.fromNormalization (Spec.algebraMap R B))
      (a : Spec (.of TS) ⟶ qB.normalization),
      e.hom ≫ pullback.snd _ _ = qB.fromNormalization ∧
      qB.toNormalization ≫ e.hom ≫ pullback.fst _ _ =
        OpenRecovery.genericPullbackMap g Y.obj.hom ≫ q₀.toNormalization ∧
      OpenRecovery.inclusion jB pB ≫ e.hom ≫ pullback.fst _ _ =
        pullback.fst Y.obj.hom g ≫ OpenRecovery.inclusion (Spec.algebraMap R U) Y.obj.hom ∧
      a ≫ qB.fromNormalization = Spec.algebraMap B TS ∧
      let xB := a (IsLocalRing.closedPoint TS)
      let C := normalComponentOpen qB.normalization (OpenRecovery.genericMap_normalStalks jB pB) xB
      let c := C.ι ≫ qB.fromNormalization
      IsIntegral (pullback c (Spec.algebraMap B S)) ∧
      NormalStalks (pullback c (Spec.algebraMap B S)) ∧
      IsFinite (pullback.snd c (Spec.algebraMap B S)) ∧
      ∃ l : Spec (.of TS) ⟶ pullback c (Spec.algebraMap B S),
        l ≫ pullback.fst _ _ ≫ C.ι = a ∧
        l ≫ pullback.snd _ _ = Spec.algebraMap S TS ∧
        (pullback.fst c (Spec.algebraMap B S) ≫ C.ι ≫ e.hom ≫ pullback.fst _ _)
          (l (IsLocalRing.closedPoint TS)) = x := by
  let : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
  let : IsRegularRing R := IsRegularLocalRing.isRegularRing_of_regularLocal R
  let : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
  let U := Localization.Away f
  let : IsDomain U := Localization.Away.isDomain (parameter_ne_zero R f hreg)
  dsimp only
  intro Y hY hG hunit hcard x hx X₀
  let T := RootAlgebra N f
  let V₀ := Localization.Away (AdjoinRoot.root (rootPolynomial N f))
  let : IsRegularLocalRing T := parameterRoot_isRegularLocalRing R f hf N hN hreg
  let : IsDomain T := IsRegularLocalRing.isDomain_of_regularLocal T
  let : IsDomain V₀ := Localization.Away.isDomain (root_ne_zero R f N hN hreg)
  let q₀ := OpenRecovery.genericMap (Spec.algebraMap R U) Y.obj.hom
  let q₁ := OpenRecovery.genericMap (Spec.algebraMap T V₀)
    ((baseChange (Spec.map (CommRingCat.ofHom (rootComplementHom N f)))).obj Y).obj.hom
  have hstage := exists_nativeRootStage_integralPointedData R Ω f hf N hN hreg
    Y hunit hcard x hx X₀
  obtain ⟨m, hm, X, k, z, b, hD, hR, hz, hzS, hb, _, hpoint⟩ := hstage
  let := hD
  let := hR
  let B := X.algebra
  let S := GeometricEtaleColimit.stageLocalRing R Ω X
  let TS := RootAlgebra N (algebraMap R S f)
  let : IsLocalRing TS := parameterRoot_isLocalRing S (algebraMap R S f)
    (map_nonunit (algebraMap R S) f hf) N hN
  have hboundary := Scheme.Kummer.exists_rootStageBoundaryLift
    R Ω N hN f hf X q₀.fromNormalization q₁.fromNormalization m hm b hb x hpoint
  obtain ⟨d, _, hdB, hdx⟩ := hboundary
  have htransport := OpenRecovery.exists_parameterNormalizedPointLift
    R B TS f (parameter_ne_zero R f hreg) Y d (Spec.algebraMap B TS) hdB x hdx
  obtain ⟨e, a, heB, heG, heE, _, haB, hax⟩ := htransport
  let V := Localization.Away (algebraMap R B f)
  let : IsDomain V := Localization.Away.isDomain
    (OpenRecovery.parameter_etale_algebraMap_ne_zero R B f (parameter_ne_zero R f hreg))
  let jB := Spec.algebraMap B V
  let g := Spec.map (CommRingCat.ofHom (parameterComplementBaseChangeHom B f))
  let pB := ((baseChange g).obj Y).obj.hom
  let qB := OpenRecovery.genericMap jB pB
  let : ∀ t : Spec (.of B), IsIntegrallyClosed ((Spec (.of B)).presheaf.stalk t) := by
    intro t
    let : IsRegularLocalRing ((Spec (.of B)).presheaf.stalk t) := regularStalks_spec B t
    exact IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _
  let : IsFinite qB.fromNormalization := OpenRecovery.fromNormalization_isFinite jB pB
  let : IsLocallyNoetherian qB.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian qB.fromNormalization
  let M := (Localization.ResiduePoint.ideal X.point.toRingHom).primeCompl
  have hM : M ≤ nonZeroDivisors B := Ideal.primeCompl_le_nonZeroDivisors _
  have ha : a ≫ qB.fromNormalization = Spec.algebraMap S TS ≫ Spec.algebraMap B S := by
    rw [haB]
    simp only [Spec.algebraMap, ← Spec.map_comp]
    congr 1
  have hcomponent := OpenRecovery.exists_pointComponentLocalizationLift B S TS M hM jB pB a
    (Spec.algebraMap S TS) ha
  obtain ⟨hInt, hNorm, l, hl, hlS, _⟩ := hcomponent
  refine ⟨X, k, z, hD, hR, hz, hzS, e, a, heB, heG, heE, haB, hInt, hNorm, inferInstance,
    l, hl, hlS, ?_⟩
  have h := congrArg (fun v : Spec (.of TS) ⟶ qB.normalization =>
    (e.hom ≫ pullback.fst q₀.fromNormalization (Spec.algebraMap R B))
      (v (IsLocalRing.closedPoint TS))) hl
  exact h.trans hax

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation
