/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.FiniteRadicial
public import Aglib.AlgebraicGeometry.Morphisms.Finite.GenericPreimageOpen
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.FiniteEtaleGenericModel
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.GenericIsomorphism
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FinitePureField

/-! # Actual generic charts along finite radicial maps -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable

universe u

open FinitePresentationDescent

/-- The canonical algebra on the original affine generic stalk. -/
local instance (R : CommRingCat.{u}) [IsDomain R] : Algebra R (Spec R).functionField :=
  StructureSheaf.stalkAlgebra R (genericPoint (Spec R))

/-- The same original generic stalk is the fraction field of the domain. -/
local instance (R : CommRingCat.{u}) [IsDomain R] : IsFractionRing R (Spec R).functionField :=
  @functionField_isFractionRing_of_affine R ‹IsDomain R›

/-- The native fraction-field structural spectrum map is the original generic stalk map. -/
theorem originalFractionFieldMap (R : CommRingCat.{u}) [IsDomain R] :
    Spec.map (CommRingCat.ofHom (algebraMap R (Spec R).functionField)) =
      (Spec R).fromSpecStalk (genericPoint (Spec R)) := by
  rw [Spec.fromSpecStalk_eq']
  rfl

/-- The generic comparison for the total map of an open finite etale model.
The open base is retained, rather than pretending its composite map is finite. -/
def genericModelTotalIso
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (.of K))
    (M : FiniteEtaleGenericModel R K f) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj
      (Over.mk (M.model.f ≫ M.inclusion)) ≅ Over.mk f := by
  have H : IsPullback M.point (𝟙 _) M.inclusion
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    apply IsPullback.flip
    apply IsPullback.of_horiz_isIso_mono
    exact ⟨by simpa using M.point_over.symm⟩
  have HT : IsPullback M.model.p f (M.model.f ≫ M.inclusion)
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
    simpa only [Category.comp_id] using M.model.square.paste_vert H
  exact Over.isoMk HT.isoPullback.symm (by simp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A finite etale source chart descends at the original generic points along a
finite dominant radicial map, with its actual generic over-isomorphism. -/
def genericFieldChart
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [IsFinite f] [UniversallyInjective f]
    (W : FiniteEtale X) :
    Σ T : FiniteEtale (Spec Y.functionField),
      (baseChange (Spec.map (CommRingCat.ofHom (functionFieldMap f)))).obj T ≅
        (baseChange (X.fromSpecStalk (genericPoint X))).obj W := by
  let : Algebra Y.functionField X.functionField := functionFieldMapAlgebra f
  have : Module.Finite Y.functionField X.functionField := functionFieldMap_finite f
  have : IsPurelyInseparable Y.functionField X.functionField :=
    functionFieldMap_isPurelyInseparable f
  let WL := (baseChange (X.fromSpecStalk (genericPoint X))).obj W
  let D := fieldCoverDescent Y.functionField X.functionField WL
  exact D

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A descended generic cover and its open model recover the original source
chart over the actual source generic point. -/
def genericSourceModelIso
    (R : CommRingCat.{u}) [IsDomain R]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec R) [IsDominant f] [IsFinite f] [UniversallyInjective f]
    (W : FiniteEtale X)
    (M : FiniteEtaleGenericModel R (Spec R).functionField
      (genericFieldChart f W).1.obj.hom) :
    (Over.pullback (X.fromSpecStalk (genericPoint X))).obj
        ((Over.pullback f).obj (Over.mk (M.model.f ≫ M.inclusion))) ≅
      (Over.pullback (X.fromSpecStalk (genericPoint X))).obj W.obj := by
  let ηX := X.fromSpecStalk (genericPoint X)
  let ηR := (Spec R).fromSpecStalk (genericPoint (Spec R))
  let k := Spec.map (CommRingCat.ofHom (functionFieldMap f))
  let P := Over.mk (M.model.f ≫ M.inclusion)
  let D := genericFieldChart f W
  have eM : (Over.pullback ηR).obj P ≅ D.1.obj := by
    let eη : (Over.pullback ηR).obj P ≅
        (Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap R (Spec R).functionField)))).obj P :=
      eqToIso (congrArg (fun h : Spec (Spec R).functionField ⟶ Spec R =>
        (Over.pullback h).obj P) (originalFractionFieldMap R).symm)
    exact eη ≪≫ genericModelTotalIso R (Spec R).functionField D.1.obj.hom M
  have eD : (Over.pullback k).obj D.1.obj ≅ (Over.pullback ηX).obj W.obj :=
    (forget _).mapIso D.2
  exact ((Over.pullbackComp ηX f).app P).symm ≪≫
    eqToIso (congrArg (fun h => (Over.pullback h).obj P)
      (fromSpecStalk_genericPoint_naturality f)) ≪≫
    (Over.pullbackComp k ηR).app P ≪≫ (Over.pullback k).mapIso eM ≪≫ eD

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original source chart is the entire pullback of an open target model
after a nonzero principal localization of the original source ring. This
intermediate result does not yet claim that this source open is a target preimage. -/
theorem exists_source_principal_model_iso
    (R A : CommRingCat.{u}) [IsDomain R] [IsNoetherianRing R] [IsDomain A]
    (f : Spec A ⟶ Spec R) [IsDominant f] [IsFinite f] [UniversallyInjective f]
    (W : FiniteEtale (Spec A)) :
    ∃ M : FiniteEtaleGenericModel R (Spec R).functionField
        (genericFieldChart f W).1.obj.hom,
      ∃ a : A, a ≠ 0 ∧ Nonempty
        ((Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap A (Localization.Away a))))).obj
            ((Over.pullback f).obj (Over.mk (M.model.f ≫ M.inclusion))) ≅
         (Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap A (Localization.Away a))))).obj W.obj) := by
  let D := genericFieldChart f W
  let M := finiteEtaleGenericModel R (Spec R).functionField D.1.obj.hom
  let t := M.model.f ≫ M.inclusion
  have : IsAffine M.model.X := isAffine_of_isAffineHom M.model.f
  have : Etale t := inferInstance
  let P := (Over.pullback f).obj (Over.mk t)
  have : LocallyOfFinitePresentation P.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd t f))
  have : QuasiCompact P.hom := inferInstanceAs (QuasiCompact (pullback.snd t f))
  have : QuasiSeparated P.hom := inferInstanceAs (QuasiSeparated (pullback.snd t f))
  have e : (Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap A (Spec A).functionField)))).obj (Over.mk P.hom) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom
        (algebraMap A (Spec A).functionField)))).obj (Over.mk W.obj.hom) := by
    rw [originalFractionFieldMap A]
    exact genericSourceModelIso R f W M
  obtain ⟨a, ha, e⟩ := exists_iso_over_principalLocalization_of_generic_iso
    A (Spec A).functionField P.hom W.obj.hom e
  exact ⟨M, a, ha, e⟩

/-- Restrict an open model to a smaller target open, retaining its actual
cartesian comparison with the total map to the original target. -/
def openModelRestrictionIso
    {B S T U : Scheme.{u}} (t : T ⟶ B) (j : B ⟶ S) [IsOpenImmersion j]
    (i : U ⟶ S) (μ : U ⟶ B) (hμ : μ ≫ j = i) :
    Over.mk (pullback.snd t μ) ≅ (Over.pullback i).obj (Over.mk (t ≫ j)) := by
  have H : IsPullback (𝟙 T) t (t ≫ j) j :=
    IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  have H' : IsPullback (pullback.fst t μ) (pullback.snd t μ) (t ≫ j) i := by
    simpa only [Category.comp_id, hμ] using (IsPullback.of_hasPullback t μ).paste_horiz H
  exact Over.isoMk H'.isoPullback H'.isoPullback_hom_snd

/-- A principal-source comparison restricts to the whole inverse image of any
smaller target open factoring through the source principal localization. -/
def restrictedSourceModelIso
    {X Y B T Q : Scheme.{u}} (f : X ⟶ Y) (t : T ⟶ B) (j : B ⟶ Y)
    [IsOpenImmersion j] (w : Q ⟶ X)
    {P : Scheme.{u}} (p : P ⟶ X)
    (e : (Over.pullback p).obj ((Over.pullback f).obj (Over.mk (t ≫ j))) ≅
      (Over.pullback p).obj (Over.mk w))
    (U : Y.Opens) (μ : U.toScheme ⟶ B) (hμ : μ ≫ j = U.ι)
    (sourceLift : (f ⁻¹ᵁ U).toScheme ⟶ P) (hsourceLift : sourceLift ≫ p = (f ⁻¹ᵁ U).ι) :
    (Over.pullback (f ∣_ U)).obj (Over.mk (pullback.snd t μ)) ≅
      (Over.pullback (f ⁻¹ᵁ U).ι).obj (Over.mk w) := by
  let Z := Over.mk (t ≫ j)
  let Q' := (Over.pullback f).obj Z
  let eV : (Over.pullback (f ⁻¹ᵁ U).ι).obj Q' ≅
      (Over.pullback (f ⁻¹ᵁ U).ι).obj (Over.mk w) :=
    eqToIso (congrArg (fun h => (Over.pullback h).obj Q') hsourceLift.symm) ≪≫
      (Over.pullbackComp sourceLift p).app Q' ≪≫ (Over.pullback sourceLift).mapIso e ≪≫
      ((Over.pullbackComp sourceLift p).app (Over.mk w)).symm ≪≫
      eqToIso (congrArg (fun h => (Over.pullback h).obj (Over.mk w)) hsourceLift)
  exact (Over.pullback (f ∣_ U)).mapIso (openModelRestrictionIso t j U.ι μ hμ) ≪≫
    ((Over.pullbackComp (f ∣_ U) U.ι).app Z).symm ≪≫
    eqToIso (congrArg (fun h => (Over.pullback h).obj Z) (morphismRestrict_ι f U)) ≪≫
    (Over.pullbackComp (f ⁻¹ᵁ U).ι f).app Z ≪≫ eV

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An actual finite etale source chart of a finite dominant radicial map of
integral affine schemes descends on an affine generic target neighborhood.
The comparison is with the entire source inverse image. -/
theorem exists_generic_full_pullback_chart
    (R A : CommRingCat.{u}) [IsDomain R] [IsNoetherianRing R] [IsDomain A]
    (f : Spec A ⟶ Spec R) [IsDominant f] [IsFinite f] [UniversallyInjective f]
    (W : FiniteEtale (Spec A)) :
    ∃ U : (Spec R).Opens, IsAffineOpen U ∧ genericPoint (Spec R) ∈ U ∧
      ∃ T : FiniteEtale U,
        Nonempty ((Over.pullback (f ∣_ U)).obj T.obj ≅
          (Over.pullback (f ⁻¹ᵁ U).ι).obj W.obj) := by
  obtain ⟨M, a, ha, ⟨e⟩⟩ := exists_source_principal_model_iso R A f W
  let p := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a)))
  have : IsOpenImmersion p := inferInstance
  have hpa : genericPoint (Spec A) ∈ p.opensRange := by
    change genericPoint (Spec A) ∈ Set.range p
    change genericPoint (Spec A) ∈ Set.range (PrimeSpectrum.comap (algebraMap A _))
    rw [PrimeSpectrum.localization_away_comap_range _ a, genericPoint_eq_bot_of_affine]
    change a ∉ (⊥ : Ideal A)
    simpa only [Ideal.mem_bot] using ha
  have hj : genericPoint (Spec R) ∈ M.inclusion.opensRange := by
    change genericPoint (Spec R) ∈ Set.range M.inclusion
    refine ⟨M.point (IsLocalRing.closedPoint (Spec R).functionField), ?_⟩
    have hm := M.point_over
    rw [originalFractionFieldMap R] at hm
    have h := congrArg (fun k => k (IsLocalRing.closedPoint (Spec R).functionField)) hm
    exact h.trans (fromSpecStalk_closedPoint (x := genericPoint (Spec R)))
  obtain ⟨U, hUa, hU, hUj, hUp⟩ := exists_affine_open_generic_preimage_subset
    f f.injective p.opensRange hpa M.inclusion.opensRange hj
  have hμrange : Set.range U.ι ⊆ Set.range M.inclusion := by
    rw [Opens.range_ι]
    exact hUj
  let μ := IsOpenImmersion.lift M.inclusion U.ι hμrange
  have hμ : μ ≫ M.inclusion = U.ι := IsOpenImmersion.lift_fac _ _ _
  have hsourceLiftrange : Set.range (f ⁻¹ᵁ U).ι ⊆ Set.range p := by
    rw [Opens.range_ι]
    exact hUp
  let sourceLift := IsOpenImmersion.lift p (f ⁻¹ᵁ U).ι hsourceLiftrange
  have hsourceLift : sourceLift ≫ p = (f ⁻¹ᵁ U).ι := IsOpenImmersion.lift_fac _ _ _
  let T := FiniteEtale.mk (pullback.snd M.model.f μ)
  refine ⟨U, hUa, hU, T, ⟨?_⟩⟩
  exact restrictedSourceModelIso f M.model.f M.inclusion W.obj.hom p e U μ hμ sourceLift hsourceLift

/-- A descended entire-pullback chart is surjective if both the original source
chart and the base morphism are surjective. -/
theorem surjective_chart_of_full_pullback_iso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    (W : FiniteEtale X) [Surjective W.obj.hom]
    (T : FiniteEtale Y)
    (e : (Over.pullback f).obj T.obj ≅ W.obj) : Surjective T.obj.hom := by
  have he : Surjective (pullback.snd T.obj.hom f) := by
    have hcomp : e.inv.left ≫ pullback.snd T.obj.hom f = W.obj.hom := e.inv.w
    have : Surjective (e.inv.left ≫ pullback.snd T.obj.hom f) := by
      rw [hcomp]
      infer_instance
    exact Surjective.of_comp e.inv.left _
  have : Surjective (pullback.fst T.obj.hom f ≫ T.obj.hom) := by
    rw [pullback.condition]
    infer_instance
  exact Surjective.of_comp (pullback.fst T.obj.hom f) _

/-- Surjective version of the actual generic full-pullback chart. -/
theorem exists_generic_surjective_full_pullback_chart
    (R A : CommRingCat.{u}) [IsDomain R] [IsNoetherianRing R] [IsDomain A]
    (f : Spec A ⟶ Spec R) [IsDominant f] [IsFinite f]
    [UniversallyInjective f] [Surjective f]
    (W : FiniteEtale (Spec A)) [Surjective W.obj.hom] :
    ∃ U : (Spec R).Opens, IsAffineOpen U ∧ genericPoint (Spec R) ∈ U ∧
      ∃ T : FiniteEtale U, Surjective T.obj.hom ∧
        Nonempty ((Over.pullback (f ∣_ U)).obj T.obj ≅
          (Over.pullback (f ⁻¹ᵁ U).ι).obj W.obj) := by
  obtain ⟨U, hUa, hU, T, ⟨e⟩⟩ := exists_generic_full_pullback_chart R A f W
  let WV := (baseChange (f ⁻¹ᵁ U).ι).obj W
  have : Surjective WV.obj.hom :=
    inferInstanceAs (Surjective (pullback.snd W.obj.hom (f ⁻¹ᵁ U).ι))
  have : Surjective (f ∣_ U) := by
    let H := isPullback_morphismRestrict f U
    have : Surjective (H.isoPullback.hom ≫ pullback.fst U.ι f) := inferInstance
    simpa only [IsPullback.isoPullback_hom_fst] using this
  exact ⟨U, hUa, hU, T,
    surjective_chart_of_full_pullback_iso (f ∣_ U) WV T e, ⟨e⟩⟩

end AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable
