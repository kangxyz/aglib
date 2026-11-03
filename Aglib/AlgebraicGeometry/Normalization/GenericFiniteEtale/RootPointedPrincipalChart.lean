/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RootPointedComponentLocalChart
public import Aglib.AlgebraicGeometry.Spec.RootPrincipalNeighborhoodSpreading
public import Aglib.AlgebraicGeometry.Spec.GeometricNeighborhoodPrincipalStages

/-! # The genuine pointed principal root neighborhood

The original normalization point produces its actual local root chart and
spreads it to a literal principal neighborhood of the same genuine stage.
The actual root algebra, coefficient parameter, original component, both
comparison directions, original field-valued point and boundary point remain.
No localization is asserted finitely presented and no replacement stage ring
is chosen. This endpoint concerns the original local base; descent from a base
stalk to a neighborhood of an arbitrary original scheme is separate.
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
theorem exists_nativePointedPrincipalRootChart
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
            chart.hom (IsLocalRing.closedPoint _) = l (IsLocalRing.closedPoint TS) ∧
            let M := (Localization.ResiduePoint.ideal X.point.toRingHom).primeCompl
            ∃ (J : Over (op (∅ : Finset M)))
              (chart' : Spec (.of (RootAlgebra n
                (algebraMap B (IsLocalization.PrincipalDiagram.stage M J.left.unop)
                  (algebraMap R B f)))) ≅
                pullback c ((Scheme.PrincipalNeighborhoodLimit.baseStructure M).app J.left)),
              Algebra.Etale R (IsLocalization.PrincipalDiagram.stage M J.left.unop) ∧
              (GeometricEtaleNeighborhood.principalStagePoint R Ω X J.left.unop).comp
                (algebraMap R (IsLocalization.PrincipalDiagram.stage M J.left.unop)) =
                  algebraMap R Ω ∧
              chart'.hom ≫ pullback.snd c
                ((Scheme.PrincipalNeighborhoodLimit.baseStructure M).app J.left) =
                Spec.algebraMap (IsLocalization.PrincipalDiagram.stage M J.left.unop)
                  (RootAlgebra n (algebraMap B
                    (IsLocalization.PrincipalDiagram.stage M J.left.unop) (algebraMap R B f))) ∧
              Scheme.Kummer.rootPrincipalComparison n (algebraMap R B f) M S J ≫ chart'.hom =
                chart.hom ≫ Scheme.PrincipalNeighborhoodLimit.comparison M S c J ∧
              Scheme.PrincipalNeighborhoodLimit.comparison M S c J ≫ chart'.inv =
                chart.inv ≫ Scheme.Kummer.rootPrincipalComparison n (algebraMap R B f) M S J ∧
              (chart'.hom ≫ pullback.fst c
                  ((Scheme.PrincipalNeighborhoodLimit.baseStructure M).app J.left) ≫
                  C.ι ≫ e.hom ≫ pullback.fst _ _)
                (Scheme.Kummer.rootPrincipalComparison n (algebraMap R B f) M S J
                  (IsLocalRing.closedPoint _)) = x := by
  let : IsRegularLocalRing R := IsRegularLocalRing.of_quotient_span_singleton R f hreg
  let : IsRegularRing R := IsRegularLocalRing.isRegularRing_of_regularLocal R
  let : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
  let U := Localization.Away f
  let : IsDomain U := Localization.Away.isDomain (parameter_ne_zero R f hreg)
  dsimp only
  intro Y hY hG hunit hcard x hx X₀
  have hdata :=
    exists_nativeRootPointedComponentLocalChart R Ω f hf N hN hreg Y hunit hcard x hx X₀
  obtain ⟨X, k, z, hD, hR, hz, hzS, e, a, heB, heG, heE, haB,
    hInt, hNorm, hfin, l, hl, hlS, hlx, hYS, n, β, hβ, hn, hnN, hnunit,
    chart, hbase, hgeneric, hpoint⟩ := hdata
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
  let : IsFinite c := OpenRecovery.pointComponent_isFinite jB pB xB
  let M := (Localization.ResiduePoint.ideal X.point.toRingHom).primeCompl
  have hparam := GeometricEtaleNeighborhood.regularParameter_pointLocalization R Ω X f hf hreg
  let : IsLocalRing (RootAlgebra n (algebraMap R S f)) :=
    parameterRoot_isLocalRing S (algebraMap R S f) hparam.2.2.2.1 n hn
  have hspread := Scheme.Kummer.exists_rootChart_principal_with_comparison
    n (algebraMap R B f) M S c chart hbase
  obtain ⟨J, chart', hbase', hhom, hinv, hproj⟩ := hspread
  refine ⟨X, k, z, hD, hR, hz, hzS, e, a, heB, heG, heE, haB,
    hInt, hNorm, hfin, l, hl, hlS, hlx, hYS, n, β, hβ, hn, hnN, hnunit,
    chart, hbase, hgeneric, hpoint, J, chart',
    GeometricEtaleNeighborhood.principalStage_etale R Ω X J.left.unop,
    GeometricEtaleNeighborhood.principalStagePoint_base R Ω X J.left.unop,
    hbase', hhom, hinv, ?_⟩
  have hp := congrArg (fun v =>
    (v ≫ C.ι ≫ e.hom ≫ pullback.fst _ _) (IsLocalRing.closedPoint
      (RootAlgebra n (algebraMap R S f)))) hproj
  have hlocal : (chart.hom ≫ pullback.fst c (Spec.algebraMap B S) ≫
      C.ι ≫ e.hom ≫ pullback.fst _ _) (IsLocalRing.closedPoint
        (RootAlgebra n (algebraMap R S f))) = x := by
    let projection : pullback c (Spec.algebraMap B S) ⟶
        (OpenRecovery.genericMap (Spec.algebraMap R U) Y.obj.hom).normalization :=
      pullback.fst c (Spec.algebraMap B S) ≫ C.ι ≫ e.hom ≫
        pullback.fst (OpenRecovery.genericMap (Spec.algebraMap R U) Y.obj.hom).fromNormalization
          (Spec.algebraMap R B)
    have hpoint' : @Eq (↑(pullback c (Spec.algebraMap B S) : Scheme.{u}))
        (chart.hom (IsLocalRing.closedPoint (RootAlgebra n (algebraMap R S f))))
        (l (IsLocalRing.closedPoint TS)) := hpoint
    exact (congrArg projection hpoint').trans hlx
  exact hp.trans hlocal

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.RootCancellation
