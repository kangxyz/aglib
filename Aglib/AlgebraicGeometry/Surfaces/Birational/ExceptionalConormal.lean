/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Invertible.StalkKernel
public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalDVR
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonzero
public import Aglib.AlgebraicGeometry.Modules.Invertible.DualTensorEquivalence
public import Aglib.AlgebraicGeometry.Modules.Invertible.ScalarAutomorphisms
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Mate
public import Aglib.AlgebraicGeometry.Curves.Picard.TorsionSections
public import Aglib.AlgebraicGeometry.Curves.LineBundleDegree.Isomorphism
public import Aglib.AlgebraicGeometry.Curves.Picard.NormDegree.OrderFormula
public import Aglib.AlgebraicGeometry.Curves.Picard.Degree.ProperCurveProductFormula
public import Aglib.AlgebraicGeometry.Curves.ProjectiveLine.Geometry
public import Aglib.AlgebraicGeometry.ProjectiveSpace.GlobalFunctions
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Normality
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Regularity
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Dimension
public import Aglib.AlgebraicGeometry.Properties.Normal.Components
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# The original conormal map between exceptional projective lines

The generic point of an integral Cartier divisor has a discrete valuation
ring as its ambient stalk. The proper-birational isomorphism neighborhood of
that point makes the original canonical conormal map nonzero. The final
projective-line comparison uses actual same-field degree invariance.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField.Curve

universe u

namespace AlgebraicGeometry.Scheme

/-- The ambient stalk at the generic point of an integral Cartier divisor is
a discrete valuation ring. The principal maximal ideal comes from the actual
closed-immersion stalk map and the original ideal-module generator. -/
theorem isDiscreteValuationRing_stalk_genericPoint_of_cartier {D B : Scheme.{u}}
    [IsIntegral D] [IsIntegral B] [IsLocallyNoetherian B]
    (j : D ⟶ B) [IsClosedImmersion j]
    (hJ : IsLocallyRankOne B (idealModule j)) :
    IsDiscreteValuationRing (B.presheaf.stalk (j (genericPoint D))) := by
  let η := genericPoint D
  let R := B.presheaf.stalk (j η)
  let : Field (D.presheaf.stalk η) := inferInstanceAs (Field D.functionField)
  obtain ⟨U, hU, hy, a, ha, hker⟩ :=
    exists_affine_regular_idealGenerator_of_isLocallyRankOne j hJ (j η)
  let : Nonempty U := ⟨⟨j η, hy⟩⟩
  let r : R := B.presheaf.germ U (j η) hy a
  have hm : IsLocalRing.maximalIdeal R = Ideal.span {r} := by
    rw [← IsLocalRing.ker_eq_maximalIdeal (j.stalkMap η).hom
      (j.stalkMap_surjective η), ker_stalkMap_eq_map_ker_app j U hU η hy, hker]
    simp only [Ideal.map_span, Set.image_singleton]
    rfl
  have ha0 : a ≠ 0 := by
    intro h
    have he : a • (0 : Γ(B, U)) = a • (1 : Γ(B, U)) := by simp [h]
    exact zero_ne_one (ha he)
  have hr0 : r ≠ 0 := by
    intro h
    apply ha0
    exact germ_injective_of_isIntegral B (j η) hy
      (h.trans (map_zero (B.presheaf.germ U (j η) hy).hom).symm)
  have hm0 : IsLocalRing.maximalIdeal R ≠ ⊥ := by
    intro h
    apply hr0
    have hr : r ∈ IsLocalRing.maximalIdeal R := by
      rw [hm]
      exact Ideal.subset_span (Set.mem_singleton r)
    simpa only [h, Ideal.mem_bot] using hr
  have hp : (IsLocalRing.maximalIdeal R).IsPrincipal := by
    rw [hm]
    infer_instance
  exact ((IsDiscreteValuationRing.TFAE R
    (IsLocalRing.isField_iff_maximalIdeal_eq.not.mpr hm0)).out 5 1).mp hp

private theorem resLE_isIso_of_preimage_eq {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIso f] (U : Y.Opens) (V : X.Opens)
    (hV : V = f ⁻¹ᵁ U) (h : V ≤ f ⁻¹ᵁ U) : IsIso (f.resLE U V h) := by
  subst V
  rw [Hom.resLE_eq_morphismRestrict]
  infer_instance

/-- The canonical first-order ideal map is nonzero when the two original
Cartier divisors are isomorphic in the displayed proper-birational square.
No dimension, normality, or ground-field hypothesis is needed. -/
theorem conormalMap_ne_zero_of_isProper_birational
    {W B E D : Scheme.{u}} [IsIntegral W] [IsIntegral B]
    [IsIntegral E] [IsIntegral D] [IsLocallyNoetherian B]
    (q : W ⟶ B) [IsProper q] [IsDominant q]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap q)))
    (i : E ⟶ W) (j : D ⟶ B) [IsClosedImmersion j]
    (hJ : IsLocallyRankOne B (idealModule j))
    (e : E ≅ D) (h : e.hom ≫ j = i ≫ q) :
    (Modules.pullback i).map (idealPullbackMap j i q e.hom h) ≠ 0 := by
  let := isDiscreteValuationRing_stalk_genericPoint_of_cartier j hJ
  obtain ⟨U, hη, hq⟩ :=
    exists_isIso_restrict_of_isProper_birational_at_valuationRing q hff (j (genericPoint D))
  let V := q ⁻¹ᵁ U
  let T := i ⁻¹ᵁ V
  let ψ := idealPullbackMap j i q e.hom h
  let := hq
  have hT : T = e.hom ⁻¹ᵁ (j ⁻¹ᵁ U) := by
    dsimp only [T, V]
    rw [← Hom.comp_preimage, ← h, Hom.comp_preimage]
  let : IsIso (q.resLE U V le_rfl) := by
    change IsIso (q.resLE U (q ⁻¹ᵁ U) le_rfl)
    rw [Hom.resLE_eq_morphismRestrict]
    infer_instance
  let : IsIso (restrictedSquareSourceMap j i q e.hom h U V le_rfl) := by
    unfold restrictedSquareSourceMap
    exact resLE_isIso_of_preimage_eq e.hom (j ⁻¹ᵁ U) T hT _
  let := idealPullbackMap_isIso_of_iso_square (j ∣_ U) (i ∣_ V)
    (q.resLE U V le_rfl) (restrictedSquareSourceMap j i q e.hom h U V le_rfl)
    (restrictedSquareSourceMap_comm j i q e.hom h U V le_rfl)
  let : IsIso ((Modules.restrictFunctor V.ι).map ψ) :=
    idealPullbackMap_restrict_isIso_of_local j i q e.hom h U V le_rfl
  let : IsIso ((Modules.restrictFunctor T.ι).map ((Modules.pullback i).map ψ)) :=
    (NatIso.isIso_map_iff (Modules.Pullback.OpenRestriction.localPullbackIso i V) ψ).mpr
      (inferInstance : IsIso ((Modules.pullback (i ∣_ V)).map
        ((Modules.restrictFunctor V.ι).map ψ)))
  let : IsIso ((Modules.pullback T.ι).map ((Modules.pullback i).map ψ)) :=
    (NatIso.isIso_map_iff (Modules.restrictFunctorIsoPullback T.ι)
      ((Modules.pullback i).map ψ)).mp inferInstance
  have hηT : genericPoint E ∈ T := by
    rw [hT]
    change j (e.hom (genericPoint E)) ∈ U
    rw [map_genericPoint_of_isDominant E e.hom]
    exact hη
  let : Nonempty T := ⟨⟨genericPoint E, hηT⟩⟩
  let : IsIntegral T.toScheme := isIntegral_of_isOpenImmersion T.ι
  let L : LineBundle T.toScheme :=
    pullbackLineBundle T.ι (pullbackLineBundle i (pullbackLineBundle q ⟨idealModule j, hJ⟩))
  have hn := lineBundleMap_ne_zero_of_mono T.toScheme L
    ((Modules.pullback T.ι).map ((Modules.pullback i).map ψ))
  intro hz
  apply hn
  rw [hz, Functor.map_zero]

private theorem equal_degree_lineMap_isIso
    {k : Type u} [Field k] (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (hdim : topologicalKrullDim X ≤ 1)
    (hprod : Picard.Degree.PrincipalProductFormula X p)
    (hunit : ∀ a : Γ(X, ⊤), a ≠ 0 → IsUnit a)
    (L M : LineBundle X) (φ : L.val ⟶ M.val) (hφ : φ ≠ 0)
    (hd : Picard.Degree.lineBundleDegree X p hdim hprod L =
      Picard.Degree.lineBundleDegree X p hdim hprod M) : IsIso φ := by
  let H := tensorLineBundle X (dualLineBundle X L) M
  let F := (lineBundleDualTensorEquivalence X L).functor
  let ev := dualEvaluationIso X L
  let μ : SheafOfModules.unit X.ringCatSheaf ⟶ H.val := ev.inv ≫ F.map φ
  have hμ : μ ≠ 0 := by
    intro hz
    apply hφ
    apply F.map_injective
    have he := congrArg (fun f => ev.hom ≫ f) hz
    simpa only [μ, Iso.hom_inv_id_assoc, comp_zero, Functor.map_zero] using he
  have hdH : Picard.Degree.lineBundleDegree X p hdim hprod H = 0 := by
    dsimp only [H]
    rw [Picard.Degree.lineBundleDegree_tensor, Picard.Degree.lineBundleDegree_dual, hd,
      neg_add_cancel]
  let s := unitHomGlobalSectionsAddEquiv X H.val μ
  have hs : s ≠ 0 := by
    intro hz
    apply hμ
    exact (unitHomGlobalSectionsAddEquiv X H.val).injective
      (hz.trans (map_zero (unitHomGlobalSectionsAddEquiv X H.val)).symm)
  obtain ⟨t⟩ := Picard.TorsionSections.lineBundle_trivial_of_nonzero_section
    X p hdim hprod H hdH s hs
  let ν := μ ≫ t.hom
  have hν : ν ≠ 0 := by
    intro hz
    apply hμ
    exact (cancel_mono t.hom).mp (hz.trans (zero_comp).symm)
  let a : Γ(X, ⊤) := ν.val.app (op ⊤) (1 : Γ(X, ⊤))
  have ha : a ≠ 0 := by
    intro hz
    apply hν
    apply (unitHomGlobalSectionsAddEquiv X (SheafOfModules.unit X.ringCatSheaf)).injective
    change a = (unitHomGlobalSectionsAddEquiv X (SheafOfModules.unit X.ringCatSheaf)) 0
    exact hz.trans (map_zero
      (unitHomGlobalSectionsAddEquiv X (SheafOfModules.unit X.ringCatSheaf))).symm
  obtain ⟨a', ha'⟩ := hunit a ha
  have hνs : ν = (ScalarAutomorphisms.scalarIso X
      (SheafOfModules.unit X.ringCatSheaf) a').hom := by
    calc
      ν = TrivializedPower.scalarMap X (SheafOfModules.unit X.ringCatSheaf) a :=
        ScalarAutomorphisms.unit_hom_eq_scalar X ν
      _ = _ := by
        change TrivializedPower.scalarMap X _ a = TrivializedPower.scalarMap X _ (a' : Γ(X, ⊤))
        rw [ha']
  let : IsIso ν := hνs ▸ inferInstance
  let : IsIso μ := (isIso_comp_right_iff μ t.hom).mp inferInstance
  let : IsIso (F.map φ) := (isIso_comp_left_iff ev.inv (F.map φ)).mp inferInstance
  exact isIso_of_reflects_iso φ F

private theorem curveProperties_of_overIso {k : Type u} [Field k]
    {X Y : OverField.FScheme k} (e : X ≅ Y) (hY : Properties Y) : Properties X := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← Over.w e.hom]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @SmoothOfRelativeDimension 1) e.hom.left Y.hom).mpr hY.smooth
  · rw [← Over.w e.hom]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @IsProper) e.hom.left Y.hom).mpr hY.proper
  · rw [← Over.w e.hom]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := @GeometricallyConnected) e.hom.left Y.hom).mpr hY.connected

private def actualCurveDegree {k : Type u} [Field k]
    (X : OverField.FScheme k) (hX : Properties X) : PicardGroup X.left →+ ℤ :=
  curveDegree smoothFieldNormality normalComponentsOpen smoothFieldRegularity
    smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula X hX

private theorem actualCurveDegree_pullback_iso {k : Type u} [Field k]
    {X Y : OverField.FScheme k} (e : X ≅ Y) (hX : Properties X) (hY : Properties Y)
    (a : PicardGroup Y.left) :
    actualCurveDegree X hX (pullbackClass e.hom.left a) = actualCurveDegree Y hY a :=
  curveDegree_pullback_iso smoothFieldNormality normalComponentsOpen smoothFieldRegularity
    smoothClosedPointDimension smoothFieldDimension Picard.Degree.properCurveProductFormula
    Picard.NormDegree.finiteMorphismNormOrder e hX hY a

private theorem actualCurveDegree_iso {k : Type u} [Field k]
    {X : OverField.FScheme k} (hX : Properties X) {L M : LineBundle X.left}
    (e : L.val ≅ M.val) :
    actualCurveDegree X hX (classOf X.left L) =
      actualCurveDegree X hX (classOf X.left M) :=
  congrArg (actualCurveDegree X hX) (Quotient.sound ⟨e⟩)

private theorem curve_equal_degree_lineMap_isIso
    {k : Type u} [Field k] (X : OverField.FScheme k) (hX : Properties X)
    (hunit : ∀ a : Γ(X.left, ⊤), a ≠ 0 → IsUnit a)
    (L M : LineBundle X.left) (φ : L.val ⟶ M.val) (hφ : φ ≠ 0)
    (hd : actualCurveDegree X hX (classOf X.left L) =
      actualCurveDegree X hX (classOf X.left M)) : IsIso φ := by
  let := curveProperties_isIntegral smoothFieldNormality normalComponentsOpen hX
  let := curveProperties_isNoetherian hX
  let (x : ClosedPoint X.left) :
      IsDiscreteValuationRing (X.left.presheaf.stalk x.val) :=
    curveProperties_closedPoint_stalk_dvr smoothFieldNormality smoothFieldRegularity
      smoothClosedPointDimension hX x.val x.property
  let := hX.proper
  let := curveProperties_locallyOfFiniteType hX
  exact equal_degree_lineMap_isIso X.left X.hom
    (le_of_eq (curveProperties_dimension smoothFieldDimension hX))
    (Picard.Degree.properCurveProductFormula k X.left X.hom
      (curveProperties_dimension smoothFieldDimension hX)) hunit L M φ hφ hd

private theorem global_isUnit_of_projectiveLine_iso
    {k : Type u} [Field k] {E : Scheme.{u}}
    (e : E ≅ AlgebraicGeometry.ProjectiveSpace k (ULift.{u} (Fin 2)))
    (a : Γ(E, ⊤)) (ha : a ≠ 0) : IsUnit a := by
  let γ : k ≃+* Γ(E, ⊤) :=
    (AlgebraicGeometry.ProjectiveSpace.globalFunctionsRingEquiv k (ULift.{u} (Fin 2))).trans
      (Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv
  have hγ : γ.symm a ≠ 0 := by
    intro h
    apply ha
    exact γ.symm.injective (h.trans γ.symm.map_zero.symm)
  have hu : IsUnit (γ.symm a) := isUnit_iff_ne_zero.mpr hγ
  have hu' : IsUnit (γ (γ.symm a)) := hu.map γ.toMonoidHom
  simpa only [γ.apply_symm_apply] using hu'

/-- If the original two conormals are identified with the same native positive
twist on projective lines over one specified field, the original canonical
conormal map is an isomorphism. The isomorphism between the divisors preserves
their actual maps to that field. No global ideal-pullback isomorphism, nonzero
map, or equality of unweighted degrees is supplied as a premise. -/
theorem conormalMap_isIso_of_isProper_birational_projectiveLine
    {k : Type u} [Field k] {W B E D : Scheme.{u}}
    [IsIntegral W] [IsIntegral B] [IsLocallyNoetherian B]
    (q : W ⟶ B) [IsProper q] [IsDominant q]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap q)))
    (i : E ⟶ W) (j : D ⟶ B) [IsClosedImmersion j]
    (hI : IsLocallyRankOne W (idealModule i))
    (hJ : IsLocallyRankOne B (idealModule j))
    (e : E ≅ D) (h : e.hom ≫ j = i ≫ q)
    (pE : E ⟶ Spec (.of k)) (pD : D ⟶ Spec (.of k))
    (he : e.hom ≫ pD = pE)
    (εE : Over.mk pE ≅
      Over.mk (AlgebraicGeometry.ProjectiveSpace.toSpec k (ULift.{u} (Fin 2))))
    (εD : Over.mk pD ≅
      Over.mk (AlgebraicGeometry.ProjectiveSpace.toSpec k (ULift.{u} (Fin 2))))
    (aE : (Modules.pullback εE.hom.left).obj
        (AlgebraicGeometry.ProjectiveSpace.twistingSheaf k (ULift.{u} (Fin 2)) 1) ≅
      (Modules.pullback i).obj (idealModule i))
    (aD : (Modules.pullback εD.hom.left).obj
        (AlgebraicGeometry.ProjectiveSpace.twistingSheaf k (ULift.{u} (Fin 2)) 1) ≅
      (Modules.pullback j).obj (idealModule j)) :
    IsIso ((Modules.pullback i).map (idealPullbackMap j i q e.hom h)) := by
  let P : OverField.FScheme k :=
    Over.mk (AlgebraicGeometry.ProjectiveSpace.toSpec k (ULift.{u} (Fin 2)))
  have hP : Properties P := curveProperties_of_overIso
    (ProjectiveLine.projectiveLineOverIsoNative k).symm
    (ProjectiveLine.projectiveLine_curveProperties k)
  have hEP : Properties (Over.mk pE) := curveProperties_of_overIso εE hP
  have hDP : Properties (Over.mk pD) := curveProperties_of_overIso εD hP
  let : IsIntegral E :=
    curveProperties_isIntegral smoothFieldNormality normalComponentsOpen hEP
  let : IsIntegral D :=
    curveProperties_isIntegral smoothFieldNormality normalComponentsOpen hDP
  let J : LineBundle B := ⟨idealModule j, hJ⟩
  let I : LineBundle W := ⟨idealModule i, hI⟩
  let ND : LineBundle D := pullbackLineBundle j J
  let NE : LineBundle E := pullbackLineBundle i I
  let L : LineBundle E := pullbackLineBundle i (pullbackLineBundle q J)
  let O1 : LineBundle P.left :=
    AlgebraicGeometry.ProjectiveSpace.twistingLineBundle k (ULift.{u} (Fin 2)) 1
  let e₀ : Over.mk pE ≅ Over.mk pD := Over.isoMk e he
  have hL : actualCurveDegree (Over.mk pE) hEP (classOf E L) =
      actualCurveDegree (Over.mk pD) hDP (classOf D ND) := by
    calc
      _ = actualCurveDegree (Over.mk pE) hEP
          (classOf E (pullbackLineBundle e.hom ND)) :=
        actualCurveDegree_iso hEP
          ((Modules.pullbackSquareIso e.hom i j q h).app (idealModule j))
      _ = _ := actualCurveDegree_pullback_iso e₀ hEP hDP (classOf D ND)
  have hND : actualCurveDegree (Over.mk pD) hDP (classOf D ND) =
      actualCurveDegree P hP (classOf P.left O1) := by
    calc
      _ = actualCurveDegree (Over.mk pD) hDP
          (classOf D (pullbackLineBundle εD.hom.left O1)) :=
        actualCurveDegree_iso hDP aD.symm
      _ = _ := actualCurveDegree_pullback_iso εD hDP hP (classOf P.left O1)
  have hNE : actualCurveDegree (Over.mk pE) hEP (classOf E NE) =
      actualCurveDegree P hP (classOf P.left O1) := by
    calc
      _ = actualCurveDegree (Over.mk pE) hEP
          (classOf E (pullbackLineBundle εE.hom.left O1)) :=
        actualCurveDegree_iso hEP aE.symm
      _ = _ := actualCurveDegree_pullback_iso εE hEP hP (classOf P.left O1)
  apply curve_equal_degree_lineMap_isIso (Over.mk pE) hEP
    (global_isUnit_of_projectiveLine_iso ((Over.forget _).mapIso εE)) L NE
    ((Modules.pullback i).map (idealPullbackMap j i q e.hom h))
  · exact conormalMap_ne_zero_of_isProper_birational q hff i j hJ e h
  · exact hL.trans (hND.trans hNE.symm)

end AlgebraicGeometry.Scheme
