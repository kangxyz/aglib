/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RootPointedComponentData
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RootBaseChangedComponentChart
public import Aglib.RingTheory.Henselian.StrictHenselization.RegularParameter

/-! # Original boundary points produce actual local component root charts

The specified original normalization point constructs the genuine integral
regular stage, its actual point component and literal localization. The
unchanged Cartesian covering source then produces the root chart internally,
with its base, generic map and same original boundary point retained. Spreading
the chart to a genuine principal neighborhood remains a separate construction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Opposite Algebra.Kummer

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation

universe u

/-- The specified original boundary point supplies the actual local component
root chart, after any prescribed genuine stage, with all original comparisons. -/
theorem exists_nativeRootPointedComponentLocalChart
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
    let := hD
    let := hR
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
          (l (IsLocalRing.closedPoint TS)) = x ∧
        let hparam := GeometricEtaleNeighborhood.regularParameter_pointLocalization R Ω X f hf hreg
        letI : IsNoetherianRing S := hparam.2.1
        letI : IsRegularLocalRing S := hparam.2.2.1
        letI : IsDomain S := IsRegularLocalRing.isDomain_of_regularLocal S
        let US := Localization.Away (algebraMap R S f)
        letI : IsDomain US := Localization.Away.isDomain
          (parameter_ne_zero S (algebraMap R S f) hparam.2.2.2.2.1)
        let Yc := OpenRecovery.pointComponentCover jB pB xB
        let gS := Spec.map (CommRingCat.ofHom
          (parameterComplementBaseChangeHom S (algebraMap R B f)))
        let YS := (baseChange gS).obj Yc
        let bS := (OpenRecovery.pointComponent_isPullback jB pB xB).baseChangeSquareMap
          (Scheme.Kummer.parameterComplementBaseChange_isPullback B S (algebraMap R B f))
        ∃ hYS : IsIntegral YS.obj.left,
        letI : IsIntegral YS.obj.left := hYS
        let K := (Spec (.of US)).functionField
        let L := YS.obj.left.functionField
        letI : Algebra US K := AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of US)
        letI : Algebra K L := GenericGalois.algebra YS
        letI : Algebra S K := ((algebraMap US K).comp (algebraMap S US)).toAlgebra
        letI : Algebra S L := ((algebraMap K L).comp (algebraMap S K)).toAlgebra
        ∃ (n : ℕ) (β : L) (hβ : β ^ n = algebraMap S L (algebraMap R S f)),
          ∃ hn : 0 < n, n ∣ N ∧ IsUnit (n : S) ∧
          ∃ chart : Spec (.of (RootAlgebra n (algebraMap R S f))) ≅
              pullback c (Spec.algebraMap B S),
            chart.hom ≫ pullback.snd c (Spec.algebraMap B S) =
              Spec.algebraMap S (RootAlgebra n (algebraMap R S f)) ∧
            Spec.map (CommRingCat.ofHom
              (rootEvaluation S L n (algebraMap R S f) β hβ).toRingHom) ≫ chart.hom =
              YS.obj.left.fromSpecStalk (genericPoint YS.obj.left) ≫ bS ∧
            letI : IsLocalRing (RootAlgebra n (algebraMap R S f)) :=
              parameterRoot_isLocalRing S (algebraMap R S f) hparam.2.2.2.1 n hn
            chart.hom (IsLocalRing.closedPoint _) = l (IsLocalRing.closedPoint TS) := by
  let : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
  let : IsRegularRing R := IsRegularLocalRing.isRegularRing_of_regularLocal R
  let : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
  let U := Localization.Away f
  let : IsDomain U := Localization.Away.isDomain (parameter_ne_zero R f hreg)
  dsimp only
  intro Y hY hG hunit hcard x hx X₀
  have hdata :=
    exists_nativeRootPointedComponentData R Ω f hf N hN hreg Y hunit hcard x hx X₀
  obtain ⟨X, k, z, hD, hR, hz, hzS, e, a, heB, heG, heE, haB,
    hInt, hNorm, hfin, l, hl, hlS, hlx⟩ := hdata
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
  let := hInt
  let := hfin
  have hparam := GeometricEtaleNeighborhood.regularParameter_pointLocalization R Ω X f hf hreg
  let : IsNoetherianRing S := hparam.2.1
  let : IsRegularLocalRing S := hparam.2.2.1
  let : IsDomain S := IsRegularLocalRing.isDomain_of_regularLocal S
  let : IsRegularLocalRing (S ⧸ Ideal.span {algebraMap R S f}) := hparam.2.2.2.2.2
  let US := Localization.Away (algebraMap R S f)
  let : IsDomain US := Localization.Away.isDomain
    (parameter_ne_zero S (algebraMap R S f) hparam.2.2.2.2.1)
  let K := (Spec (.of US)).functionField
  let : Algebra US K := AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of US)
  let : IsFractionRing US K := AlgebraicGeometry.functionField_isFractionRing_of_affine (.of US)
  let : Algebra S K := ((algebraMap US K).comp (algebraMap S US)).toAlgebra
  have hinj : Function.Injective (algebraMap S K) :=
    (IsFractionRing.injective US K).comp (FaithfulSMul.algebraMap_injective S US)
  have hroots : (primitiveRoots N K).Nonempty :=
    ⟨algebraMap S K (algebraMap B S z), (mem_primitiveRoots hN).mpr
      (hzS.map_of_injective hinj)⟩
  let : Module.Finite S TS := root_finite N hN _
  let : IsLocalHom (algebraMap S TS) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap S TS)).out 5 1).mp
      (IsLocalRing.eq_maximalIdeal (show
        ((IsLocalRing.maximalIdeal TS).comap (algebraMap S TS)).IsMaximal from inferInstance))
  have hxS : pullback.snd c (Spec.algebraMap B S) (l (IsLocalRing.closedPoint TS)) =
      IsLocalRing.closedPoint S := by
    have h := congrArg (fun v : Spec (.of TS) ⟶ Spec (.of S) =>
      v (IsLocalRing.closedPoint TS)) hlS
    exact h.trans AlgebraicGeometry.Spec_closedPoint
  refine ⟨X, k, z, hD, hR, hz, hzS, e, a, heB, heG, heE, haB,
    hInt, hNorm, hfin, l, hl, hlS, hlx, ?_⟩
  exact exists_baseChangedComponentRootChart B S (algebraMap R B f) hparam.2.2.2.1
    N hN hparam.2.2.2.2.1 (OpenRecovery.pointComponentCover jB pB xB)
    C c (OpenRecovery.pointComponentInclusion jB pB xB)
    (OpenRecovery.pointComponent_isPullback jB pB xB) hNorm l hlS
    (l (IsLocalRing.closedPoint TS)) hxS (by simpa using hunit.map (algebraMap R S)) hroots

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation
