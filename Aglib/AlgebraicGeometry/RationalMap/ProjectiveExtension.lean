/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.BaseIdeal
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.Principalization
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FieldCoordinates
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.LineSource
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.Naturality
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Epimorphism
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Isomorphism
public import Aglib.AlgebraicGeometry.Modules.Tensor.Linear
public import Aglib.AlgebraicGeometry.Modules.Invertible.FieldMaps
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.FieldSpan

/-!
# Original rational coordinates after actual point principalization

The source module is the literal pullback of the original denominator line.
The original coordinate row is pulled back and composed with the canonical
epimorphism onto the actual inverse-image ideal. The projective map and its
base and twisting-coordinate equations retain that same row and index.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Scheme.RationalCoordinates

variable {X Y : Scheme.{u}}

/-- The original map between the actual closed base-ideal subschemes. -/
def baseIdealSourceMap (J : X.IdealSheafData) (β : Y ⟶ X) :
    (J.comap β).subscheme ⟶ J.subscheme :=
  IdealSheafData.subschemeMap (J.comap β) J β (J.le_map_comap β)

@[reassoc]
theorem baseIdealSourceMap_comm (J : X.IdealSheafData) (β : Y ⟶ X) :
    baseIdealSourceMap J β ≫ J.subschemeι = (J.comap β).subschemeι ≫ β :=
  IdealSheafData.subschemeMap_subschemeι _ _ _ _

/-- This is the actual cartesian square, not an assumed comparison of modules. -/
theorem baseIdealSourceMap_isPullback (J : X.IdealSheafData) (β : Y ⟶ X) :
    IsPullback (baseIdealSourceMap J β) (J.comap β).subschemeι J.subschemeι β := by
  apply IsPullback.flip
  apply AlgebraicGeometry.isPullback_of_isClosedImmersion
    (J.comap β).subschemeι J.subschemeι (baseIdealSourceMap J β) β
    (baseIdealSourceMap_comm J β).symm
  rw [J.ker_subschemeι, (J.comap β).ker_subschemeι]

/-- The canonical map onto the actual inverse-image ideal module. -/
def baseIdealPullbackMap (J : X.IdealSheafData) (β : Y ⟶ X) :
    (Scheme.Modules.pullback β).obj (Hom.idealModule J.subschemeι) ⟶
      Hom.idealModule (J.comap β).subschemeι :=
  Hom.idealPullbackMap J.subschemeι (J.comap β).subschemeι β
    (baseIdealSourceMap J β) (baseIdealSourceMap_comm J β)

/-- This original comparison is epimorphic along every actual morphism. -/
instance baseIdealPullbackMap_epi (J : X.IdealSheafData) (β : Y ⟶ X) :
    Epi (baseIdealPullbackMap J β) :=
  Hom.idealPullbackMap_epi_of_isPullback J.subschemeι (J.comap β).subschemeι β
    (baseIdealSourceMap J β) (baseIdealSourceMap_comm J β)
    (baseIdealSourceMap_isPullback J β)

/-- The actual inclusion triangle of the same canonical epimorphism. -/
@[reassoc]
theorem baseIdealPullbackMap_inclusion (J : X.IdealSheafData) (β : Y ⟶ X) :
    baseIdealPullbackMap J β ≫ Hom.idealInclusion (J.comap β).subschemeι =
      (Scheme.Modules.pullback β).map (Hom.idealInclusion J.subschemeι) ≫
        (pullbackUnitIso β).hom :=
  Hom.idealPullbackMap_inclusion J.subschemeι (J.comap β).subschemeι β
    (baseIdealSourceMap J β) (baseIdealSourceMap_comm J β)

variable (X) [IsIntegral X] {I : Type u} [Fintype I]

/-- The literal pulled denominator module, retaining the original ideal module. -/
abbrev pulledDenominatorModule (f : I → X.functionField) (β : Y ⟶ X) : Y.Modules :=
  (Scheme.Modules.pullback β).obj (denominatorModule X f)

/-- The literal module of the actual inverse-image base ideal. -/
abbrev pulledBaseModule (f : I → X.functionField) (β : Y ⟶ X) : Y.Modules :=
  Hom.idealModule ((baseIdeal X f).comap β).subschemeι

/-- The original coordinate is pulled back and then mapped onto the actual ideal. -/
def pulledCoordinateMap (f : I → X.functionField) (β : Y ⟶ X) (i : I) :
    pulledDenominatorModule X f β ⟶ pulledBaseModule X f β :=
  (Scheme.Modules.pullback β).map (coordinateMap X f i) ≫
    baseIdealPullbackMap (baseIdeal X f) β

/-- The original finite coordinate row stays epimorphic onto the actual image ideal. -/
instance pulledCoordinateFamily_epi (f : I → X.functionField) (β : Y ⟶ X) :
    Epi (Sigma.desc (pulledCoordinateMap X f β)) := by
  let F := Scheme.Modules.pullback β
  let : F.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (Scheme.Modules.pullbackPushforwardAdjunction β)
  have : Epi (F.map (Sigma.desc (coordinateMap X f))) := inferInstance
  have hrow : Epi (Sigma.desc (fun i ↦ F.map (coordinateMap X f i))) := by
    rw [← sigmaComparison_map_desc F (fun _ : I ↦ denominatorModule X f)
      (baseModule X f) (coordinateMap X f)]
    infer_instance
  have heq : Sigma.desc (pulledCoordinateMap X f β) =
      Sigma.desc (fun i ↦ F.map (coordinateMap X f i)) ≫
        baseIdealPullbackMap (baseIdeal X f) β := by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc, pulledCoordinateMap, F]
  rw [heq]
  infer_instance

/-- The pulled row retains the original numerator through the actual ideal inclusion. -/
@[reassoc]
theorem pulledCoordinateMap_inclusion (f : I → X.functionField) (β : Y ⟶ X) (i : I) :
    pulledCoordinateMap X f β i ≫
        Hom.idealInclusion ((baseIdeal X f).comap β).subschemeι =
      (Scheme.Modules.pullback β).map (numeratorMap X f i) ≫ (pullbackUnitIso β).hom := by
  rw [pulledCoordinateMap, Category.assoc, baseIdealPullbackMap_inclusion,
    ← Category.assoc, ← Functor.map_comp]
  exact congrArg (fun e ↦ (Scheme.Modules.pullback β).map e ≫ (pullbackUnitIso β).hom)
    (coordinateMap_inclusion X f i)

/-- At the original coordinate one, the same inclusion is the pulled denominator inclusion. -/
@[reassoc]
theorem pulledCoordinateMap_one_inclusion (f : I → X.functionField)
    (i₀ : I) (hi₀ : f i₀ = 1) (β : Y ⟶ X) :
    pulledCoordinateMap X f β i₀ ≫
        Hom.idealInclusion ((baseIdeal X f).comap β).subschemeι =
      (Scheme.Modules.pullback β).map (denominatorInclusion X f) ≫
        (pullbackUnitIso β).hom := by
  rw [pulledCoordinateMap_inclusion, numeratorMap_eq_inclusion_of_one X f i₀ hi₀]

variable {R : Type u} [CommRing R]

/-- The original row constructs its actual projective map after principalization. -/
def mapAfterPrincipalization (f : I → X.functionField)
    (hD : IsLocallyRankOne X (denominatorModule X f)) (p : X ⟶ Spec (.of R))
    (β : Y ⟶ X) (hJ : Blowup.cartierPullback (baseIdeal X f) β) :
    Y ⟶ ProjectiveSpace R I :=
  ProjectiveSpace.FromSections.LineSource.mapOfFamily
    (pulledDenominatorModule X f β) (pulledBaseModule X f β)
    (pullback_locallyRankOne β _ hD) (β ≫ p) hJ (pulledCoordinateMap X f β)

/-- The actual map keeps the original structural triangle. -/
@[reassoc]
theorem mapAfterPrincipalization_toSpec (f : I → X.functionField)
    (hD : IsLocallyRankOne X (denominatorModule X f)) (p : X ⟶ Spec (.of R))
    (β : Y ⟶ X) (hJ : Blowup.cartierPullback (baseIdeal X f) β) :
    mapAfterPrincipalization X f hD p β hJ ≫ ProjectiveSpace.toSpec R I = β ≫ p :=
  ProjectiveSpace.FromSections.LineSource.mapOfFamily_toSpec _ _ _ _ _ _

/-- The twisting comparison uses the literal pulled denominator and actual image ideal. -/
def mapAfterPrincipalizationTwistingPullbackIso (f : I → X.functionField)
    (hD : IsLocallyRankOne X (denominatorModule X f)) (p : X ⟶ Spec (.of R))
    (β : Y ⟶ X) (hJ : Blowup.cartierPullback (baseIdeal X f) β) :
    (Scheme.Modules.pullback (mapAfterPrincipalization X f hD p β hJ)).obj
        (ProjectiveSpace.twistingSheaf R I 1) ≅
      ProjectiveSpace.FromSections.LineSource.coefficientModule
        (pulledDenominatorModule X f β) (pulledBaseModule X f β) :=
  ProjectiveSpace.FromSections.LineSource.twistingPullbackIso _ _ _ _ _ _

/-- The original indexed coordinate recovers the same pulled numerator map by duality. -/
theorem mapAfterPrincipalization_coordinate_triangle (f : I → X.functionField)
    (hD : IsLocallyRankOne X (denominatorModule X f)) (p : X ⟶ Spec (.of R))
    (β : Y ⟶ X) (hJ : Blowup.cartierPullback (baseIdeal X f) β) (i : I) :
    (dualEvaluationIso Y ⟨pulledDenominatorModule X f β,
      pullback_locallyRankOne β _ hD⟩).hom ≫
        ProjectiveSpace.FromSections.LineSource.pulledCoordinate
          (pulledDenominatorModule X f β) (pulledBaseModule X f β)
          (pullback_locallyRankOne β _ hD) (β ≫ p) hJ (pulledCoordinateMap X f β) i ≫
        (mapAfterPrincipalizationTwistingPullbackIso X f hD p β hJ).hom =
      (lineBundleDualTensorEquivalence Y ⟨pulledDenominatorModule X f β,
        pullback_locallyRankOne β _ hD⟩).functor.map (pulledCoordinateMap X f β i) :=
  ProjectiveSpace.FromSections.LineSource.pulledCoordinate_triangle _ _ _ _ _ _ i

/-- Actual finite point principalization supplies the required pulled row and projective map. -/
theorem exists_pointBlowupChain_coordinateMap [IsNoetherian X]
    (hX : RegularStalks X) (hd : topologicalKrullDim X ≤ 2)
    (f : I → X.functionField) (i₀ : I) (hi₀ : f i₀ = 1) (p : X ⟶ Spec (.of R)) :
    ∃ (Y : Scheme.{u}) (β : Y ⟶ X), Nonempty (Blowup.PointBlowupChain β) ∧
      IsProper β ∧ IsDominant β ∧ BirationalOver β (𝟙 X) ∧ IsIntegral Y ∧
      RegularStalks Y ∧ (∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 2) ∧
      ∃ hJ : Blowup.cartierPullback (baseIdeal X f) β,
        mapAfterPrincipalization X f
          (denominatorModule_isLocallyRankOne X hX f i₀ hi₀) p β hJ ≫
            ProjectiveSpace.toSpec R I = β ≫ p := by
  have hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 2 := by
    rw [Scheme.topologicalKrullDim_eq_iSup_stalk] at hd
    intro x
    exact (le_iSup (fun z : X ↦ ringKrullDim (X.presheaf.stalk z)) x).trans hd
  let : IsArtinianScheme (baseIdeal X f).subscheme :=
    baseIdeal_isArtinian_subscheme X hX hdim f i₀ hi₀
  obtain ⟨Y, β, hc, hp, hdom, hbir, hI, hreg, hdimY, hJ⟩ :=
    Blowup.exists_regular_pointBlowup_principalization hX hdim (baseIdeal X f)
      (baseIdeal_ne_bot X f i₀ hi₀)
  exact ⟨Y, β, hc, hp, hdom, hbir, hI, hreg, hdimY, hJ,
    mapAfterPrincipalization_toSpec X f _ p β hJ⟩

open Scheme.Modules.RationalFunctions

private abbrev fieldScalar {K : Type u} [Field K] (a : K) :
    SheafOfModules.unit (Spec (.of K)).ringCatSheaf ⟶
      SheafOfModules.unit (Spec (.of K)).ringCatSheaf :=
  unitMul (Spec (.of K)) ((Scheme.ΓSpecIso (.of K)).inv.hom a)

/-- The original rational multiplier is the pushforward of multiplication by
that same element of the original function field, including the zero case. -/
theorem multiplier_eq_genericPushforward (a : X.functionField) :
    multiplier X a =
      (Scheme.Modules.pushforward (X.fromSpecStalk (genericPoint X))).map
        (unitMul (Spec X.functionField) ((Scheme.ΓSpecIso X.functionField).inv.hom a)) := by
  classical
  by_cases ha : a = 0
  · subst a
    rw [show multiplier X 0 = 0 by simp [multiplier], map_zero,
      unitMul_zero, Functor.map_zero]
  · rw [multiplier, dite_eq_right ha]
    change (Scheme.Modules.pushforward (X.fromSpecStalk (genericPoint X))).map
      (globalScalarEndomorphism (Spec X.functionField)
        (SheafOfModules.unit (Spec X.functionField).ringCatSheaf)
        ((Scheme.ΓSpecIso X.functionField).inv.hom a)) = _
    rw [globalScalarEndomorphism_unit]

omit [Fintype I] in
/-- Transposing the original numerator equation gives its exact generic
scalar equation through the canonical pullback unit comparison. -/
theorem genericNumeratorMap [Finite I] (f : I → X.functionField) (i : I) :
    (Scheme.Modules.pullback (X.fromSpecStalk (genericPoint X))).map (numeratorMap X f i) ≫
        (pullbackUnitIso (X.fromSpecStalk (genericPoint X))).hom =
      (Scheme.Modules.pullback (X.fromSpecStalk (genericPoint X))).map
          (denominatorInclusion X f) ≫
        (pullbackUnitIso (X.fromSpecStalk (genericPoint X))).hom ≫
        unitMul (Spec X.functionField) ((Scheme.ΓSpecIso X.functionField).inv.hom (f i)) := by
  let j := X.fromSpecStalk (genericPoint X)
  apply ((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, pullbackUnitIso_homEquiv,
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    pullbackUnitIso_homEquiv]
  change numeratorMap X f i ≫ CommonFractionalIdeal.regularMap X =
    denominatorInclusion X f ≫ CommonFractionalIdeal.regularMap X ≫
      (Scheme.Modules.pushforward j).map (fieldScalar (f i))
  exact (numeratorMap_regularMap X f i).trans
    (congrArg (fun t : CommonFractionalIdeal.rationalFunctions X ⟶
        CommonFractionalIdeal.rationalFunctions X ↦
      denominatorInclusion X f ≫ CommonFractionalIdeal.regularMap X ≫ t)
      (multiplier_eq_genericPushforward X (f i)))

omit [Fintype I] in
private theorem denominatorInclusion_ne_zero [Finite I] (f : I → X.functionField) :
    denominatorInclusion X f ≠ 0 := by
  let := Fintype.ofFinite I
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (genericPoint X)) isOpen_univ
  let : Nonempty U := ⟨⟨genericPoint X, hηU⟩⟩
  let U' : X.affineOpens := ⟨U, hU⟩
  let := functionField_isFractionRing_of_isAffineOpen X U hU
  have hD : (denominatorIdeal X f).ideal U' ≠ ⊥ := by
    intro hbot
    apply denominatorIdeal_stalk_ne_bot X f (genericPoint X)
    rw [IdealSheafData.stalkIdeal_eq_map (denominatorIdeal X f) U' (genericPoint X) hηU,
      hbot, Ideal.map_bot]
  rw [denominatorIdeal_ideal X f U'] at hD
  obtain ⟨c, hc, hcn⟩ := (Submodule.ne_bot_iff _).mp hD
  let s := (denominatorSectionsEquiv X f U').symm ⟨c, hc⟩
  have hv : (denominatorInclusion X f).val.app (op U) s = c := by
    calc
      _ = ((denominatorSectionsEquiv X f U' s) : Γ(X, U')) :=
        (denominatorSectionsEquiv_val X f U' s).symm
      _ = c := congrArg Subtype.val ((denominatorSectionsEquiv X f U').apply_symm_apply ⟨c, hc⟩)
  intro hz
  apply hcn
  rw [hz] at hv
  exact hv.symm

omit [Fintype I] in
/-- The actual pulled denominator inclusion is nonzero on the original generic
spectrum, derived from its original nonzero affine ideal sections. -/
theorem genericDenominatorMap_ne_zero [Finite I] (f : I → X.functionField) :
    (Scheme.Modules.pullback (X.fromSpecStalk (genericPoint X))).map
        (denominatorInclusion X f) ≫
      (pullbackUnitIso (X.fromSpecStalk (genericPoint X))).hom ≠ 0 := by
  let j := X.fromSpecStalk (genericPoint X)
  intro hz
  have h := congrArg ((Scheme.Modules.pullbackPushforwardAdjunction j).homEquiv _ _) hz
  rw [Adjunction.homEquiv_naturality_left, pullbackUnitIso_homEquiv,
    Adjunction.homEquiv_unit, Functor.map_zero, comp_zero] at h
  change denominatorInclusion X f ≫ CommonFractionalIdeal.regularMap X = 0 at h
  apply denominatorInclusion_ne_zero X f
  apply (cancel_mono (CommonFractionalIdeal.regularMap X)).mp
  simpa only [zero_comp] using h

private theorem pullback_fieldScalar {K L : Type u} [Field K] [Field L]
    (φ : K →+* L) (a : K) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).map (fieldScalar a) ≫
        (pullbackUnitIso (Spec.map (CommRingCat.ofHom φ))).hom =
      (pullbackUnitIso (Spec.map (CommRingCat.ofHom φ))).hom ≫ fieldScalar (φ a) := by
  let q := Spec.map (CommRingCat.ofHom φ)
  have hs : q.appTop ((Scheme.ΓSpecIso (.of K)).inv.hom a) =
      (Scheme.ΓSpecIso (.of L)).inv.hom (φ a) := by
    exact (ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)) a).symm
  change (Scheme.Modules.pullback q).map
      (unitMul (Spec (.of K)) ((Scheme.ΓSpecIso (.of K)).inv.hom a)) ≫ _ = _
  rw [← globalScalarEndomorphism_unit, pullback_map_globalScalarEndomorphism]
  calc
    _ = (pullbackUnitIso q).hom ≫
        globalScalarEndomorphism (Spec (.of L))
          (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
          (q.appTop ((Scheme.ΓSpecIso (.of K)).inv.hom a)) :=
      ((globalScalarCenter (Spec (.of L))
        (q.appTop ((Scheme.ΓSpecIso (.of K)).inv.hom a))).naturality (pullbackUnitIso q).hom).symm
    _ = (pullbackUnitIso q).hom ≫
        globalScalarEndomorphism (Spec (.of L))
          (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
          ((Scheme.ΓSpecIso (.of L)).inv.hom (φ a)) :=
      congrArg (fun b : Γ(Spec (.of L), ⊤) ↦ (pullbackUnitIso q).hom ≫
        globalScalarEndomorphism (Spec (.of L))
          (SheafOfModules.unit (Spec (.of L)).ringCatSheaf) b) hs
    _ = _ := congrArg (fun t ↦ (pullbackUnitIso q).hom ≫ t)
      (globalScalarEndomorphism_unit (Spec (.of L)) _)


omit [Fintype I] in
/-- The nonzero original generic denominator map is an isomorphism of the
actual line modules over the original function field. -/
theorem genericDenominatorMap_isIso [Finite I] (f : I → X.functionField)
    (hD : IsLocallyRankOne X (denominatorModule X f)) :
    IsIso ((Scheme.Modules.pullback (X.fromSpecStalk (genericPoint X))).map
        (denominatorInclusion X f) ≫
      (pullbackUnitIso (X.fromSpecStalk (genericPoint X))).hom) := by
  exact fieldLineBundleMap_isIso_of_ne_zero X.functionField
    ⟨_, pullback_locallyRankOne (X.fromSpecStalk (genericPoint X)) _ hD⟩
    ⟨_, ProjectiveSpace.FromSections.FieldSpan.unit_rankOne _⟩ _
    (genericDenominatorMap_ne_zero X f)


private def genericPullbackComparison [IsIntegral Y] (β : Y ⟶ X) [IsDominant β] :
    Scheme.Modules.pullback β ⋙
        Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y)) ≅
      Scheme.Modules.pullback (X.fromSpecStalk (genericPoint X)) ⋙
        Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β))) :=
  Scheme.Modules.pullbackComp (Y.fromSpecStalk (genericPoint Y)) β ≪≫
    Scheme.Modules.pullbackCongr (Scheme.fromSpecStalk_genericPoint_naturality β) ≪≫
      (Scheme.Modules.pullbackComp
        (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)))
        (X.fromSpecStalk (genericPoint X))).symm

private theorem genericPullbackComparison_unit [IsIntegral Y]
    (β : Y ⟶ X) [IsDominant β] :
    (genericPullbackComparison X β).hom.app (SheafOfModules.unit X.ringCatSheaf) ≫
        (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)))).map
          (pullbackUnitIso (X.fromSpecStalk (genericPoint X))).hom ≫
        (pullbackUnitIso (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)))).hom =
      (Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y))).map
          (pullbackUnitIso β).hom ≫
        (pullbackUnitIso (Y.fromSpecStalk (genericPoint Y))).hom := by
  simp only [genericPullbackComparison, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Category.assoc]
  rw [← pullbackUnitIso_comp, Iso.inv_hom_id_app_assoc,
    pullbackUnitIso_congr, pullbackUnitIso_comp]

private theorem genericPullbackComparison_toUnit [IsIntegral Y]
    (β : Y ⟶ X) [IsDominant β] (M : X.Modules)
    (t : M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (genericPullbackComparison X β).hom.app M ≫
        (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)))).map
          ((Scheme.Modules.pullback (X.fromSpecStalk (genericPoint X))).map t ≫
            (pullbackUnitIso (X.fromSpecStalk (genericPoint X))).hom) ≫
        (pullbackUnitIso (Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)))).hom =
      (Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y))).map
          ((Scheme.Modules.pullback β).map t ≫ (pullbackUnitIso β).hom) ≫
        (pullbackUnitIso (Y.fromSpecStalk (genericPoint Y))).hom := by
  let F := Scheme.Modules.pullback β
  let G := Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y))
  let E := Scheme.Modules.pullback (X.fromSpecStalk (genericPoint X))
  let q := Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β))
  let H := Scheme.Modules.pullback q
  let e := genericPullbackComparison X β
  let uX := (pullbackUnitIso (X.fromSpecStalk (genericPoint X))).hom
  let uY := (pullbackUnitIso (Y.fromSpecStalk (genericPoint Y))).hom
  let uβ := (pullbackUnitIso β).hom
  let uq := (pullbackUnitIso q).hom
  have hn : G.map (F.map t) ≫ e.hom.app (SheafOfModules.unit X.ringCatSheaf) =
      e.hom.app M ≫ H.map (E.map t) := e.hom.naturality t
  have hu : e.hom.app (SheafOfModules.unit X.ringCatSheaf) ≫ H.map uX ≫ uq =
      G.map uβ ≫ uY := genericPullbackComparison_unit X β
  change e.hom.app M ≫ H.map (E.map t ≫ uX) ≫ uq = G.map (F.map t ≫ uβ) ≫ uY
  calc
    _ = (e.hom.app M ≫ H.map (E.map t)) ≫ (H.map uX ≫ uq) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (G.map (F.map t) ≫ e.hom.app (SheafOfModules.unit X.ringCatSheaf)) ≫
        (H.map uX ≫ uq) := congrArg (fun c ↦ c ≫ (H.map uX ≫ uq)) hn.symm
    _ = G.map (F.map t) ≫ (G.map uβ ≫ uY) := by rw [Category.assoc, hu]
    _ = _ := by rw [Functor.map_comp, Category.assoc]

omit [Fintype I] in
private theorem doubleGenericNumeratorMap [IsIntegral Y] [Finite I]
    (f : I → X.functionField) (β : Y ⟶ X) [IsDominant β] (i : I) :
    (Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y))).map
        ((Scheme.Modules.pullback β).map (numeratorMap X f i) ≫
          (pullbackUnitIso β).hom) ≫
        (pullbackUnitIso (Y.fromSpecStalk (genericPoint Y))).hom =
      (Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y))).map
          ((Scheme.Modules.pullback β).map (denominatorInclusion X f) ≫
            (pullbackUnitIso β).hom) ≫
        (pullbackUnitIso (Y.fromSpecStalk (genericPoint Y))).hom ≫
        fieldScalar (Scheme.functionFieldMap β (f i)) := by
  let q := Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β))
  let H := Scheme.Modules.pullback q
  let E := Scheme.Modules.pullback (X.fromSpecStalk (genericPoint X))
  let e := genericPullbackComparison X β
  let uX := (pullbackUnitIso (X.fromSpecStalk (genericPoint X))).hom
  let uq := (pullbackUnitIso q).hom
  have hn : E.map (numeratorMap X f i) ≫ uX =
      (E.map (denominatorInclusion X f) ≫ uX) ≫ fieldScalar (f i) := by
    exact (genericNumeratorMap X f i).trans
      (Category.assoc (E.map (denominatorInclusion X f)) uX (fieldScalar (f i))).symm
  calc
    _ = e.hom.app (denominatorModule X f) ≫
        H.map (E.map (numeratorMap X f i) ≫ uX) ≫ uq :=
      (genericPullbackComparison_toUnit X β _ (numeratorMap X f i)).symm
    _ = e.hom.app (denominatorModule X f) ≫
        H.map ((E.map (denominatorInclusion X f) ≫ uX) ≫ fieldScalar (f i)) ≫ uq :=
      congrArg (fun t ↦ e.hom.app (denominatorModule X f) ≫ H.map t ≫ uq) hn
    _ = e.hom.app (denominatorModule X f) ≫
        H.map (E.map (denominatorInclusion X f) ≫ uX) ≫
          H.map (fieldScalar (f i)) ≫ uq := by rw [Functor.map_comp, Category.assoc]
    _ = e.hom.app (denominatorModule X f) ≫
        H.map (E.map (denominatorInclusion X f) ≫ uX) ≫
          uq ≫ fieldScalar (Scheme.functionFieldMap β (f i)) := by
      rw [pullback_fieldScalar]
    _ = (e.hom.app (denominatorModule X f) ≫
        H.map (E.map (denominatorInclusion X f) ≫ uX) ≫ uq) ≫
          fieldScalar (Scheme.functionFieldMap β (f i)) := by simp only [Category.assoc]
    _ = _ := congrArg (fun t ↦ t ≫ fieldScalar (Scheme.functionFieldMap β (f i)))
      (genericPullbackComparison_toUnit X β _ (denominatorInclusion X f))

omit [Fintype I] in
private theorem doubleGenericDenominatorMap_isIso [IsIntegral Y] [Finite I]
    (f : I → X.functionField) (hD : IsLocallyRankOne X (denominatorModule X f))
    (β : Y ⟶ X) [IsDominant β] :
    IsIso ((Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y))).map
        ((Scheme.Modules.pullback β).map (denominatorInclusion X f) ≫
          (pullbackUnitIso β).hom) ≫
      (pullbackUnitIso (Y.fromSpecStalk (genericPoint Y))).hom) := by
  let : IsIso ((Scheme.Modules.pullback (X.fromSpecStalk (genericPoint X))).map
        (denominatorInclusion X f) ≫
      (pullbackUnitIso (X.fromSpecStalk (genericPoint X))).hom) :=
    genericDenominatorMap_isIso X f hD
  rw [← genericPullbackComparison_toUnit X β _ (denominatorInclusion X f)]
  infer_instance


private theorem fieldUnit_id_ne_zero (K : Type u) [Field K] :
    (𝟙 (SheafOfModules.unit (Spec (.of K)).ringCatSheaf) :
      SheafOfModules.unit (Spec (.of K)).ringCatSheaf ⟶
        SheafOfModules.unit (Spec (.of K)).ringCatSheaf) ≠ 0 := by
  intro h
  have hv := congrArg (fun t ↦ t.val.app (op ⊤) (1 : Γ(Spec (.of K), ⊤))) h
  change (1 : Γ(Spec (.of K), ⊤)) = 0 at hv
  apply one_ne_zero (α := K)
  simpa only [map_one, map_zero] using congrArg (Scheme.ΓSpecIso (.of K)).hom.hom hv

private theorem iso_to_fieldUnit_ne_zero {K : Type u} [Field K]
    {M : (Spec (.of K)).Modules}
    (t : M ⟶ SheafOfModules.unit (Spec (.of K)).ringCatSheaf) [IsIso t] : t ≠ 0 := by
  intro hz
  apply fieldUnit_id_ne_zero K
  calc
    _ = inv t ≫ t := (IsIso.inv_hom_id t).symm
    _ = 0 := (congrArg (fun v ↦ inv t ≫ v) hz).trans (by simp only [comp_zero])

private abbrev genericBaseInclusion [IsIntegral Y]
    (f : I → X.functionField) (β : Y ⟶ X) :
    (Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y))).obj
        (pulledBaseModule X f β) ⟶
      SheafOfModules.unit (Spec Y.functionField).ringCatSheaf :=
  (Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y))).map
      (Hom.idealInclusion ((baseIdeal X f).comap β).subschemeι) ≫
    (pullbackUnitIso (Y.fromSpecStalk (genericPoint Y))).hom

private theorem genericCoordinateMap_inclusion [IsIntegral Y]
    (f : I → X.functionField) (β : Y ⟶ X) (i : I) :
    (Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y))).map
        (pulledCoordinateMap X f β i) ≫ genericBaseInclusion X f β =
      (Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y))).map
          ((Scheme.Modules.pullback β).map (numeratorMap X f i) ≫
            (pullbackUnitIso β).hom) ≫
        (pullbackUnitIso (Y.fromSpecStalk (genericPoint Y))).hom := by
  change (Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y))).map
      (pulledCoordinateMap X f β i) ≫
    (Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y))).map
      (Hom.idealInclusion ((baseIdeal X f).comap β).subschemeι) ≫ _ = _
  rw [← Category.assoc, ← Functor.map_comp]
  exact congrArg (fun t ↦
    (Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y))).map t ≫
      (pullbackUnitIso (Y.fromSpecStalk (genericPoint Y))).hom)
    (pulledCoordinateMap_inclusion X f β i)

private theorem genericCoordinateMap_one_inclusion [IsIntegral Y]
    (f : I → X.functionField) (i₀ : I) (hi₀ : f i₀ = 1) (β : Y ⟶ X) :
    (Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y))).map
        (pulledCoordinateMap X f β i₀) ≫ genericBaseInclusion X f β =
      (Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y))).map
          ((Scheme.Modules.pullback β).map (denominatorInclusion X f) ≫
            (pullbackUnitIso β).hom) ≫
        (pullbackUnitIso (Y.fromSpecStalk (genericPoint Y))).hom := by
  rw [genericCoordinateMap_inclusion, numeratorMap_eq_inclusion_of_one X f i₀ hi₀]

private theorem genericCoordinateMap_selected_isIso [IsIntegral Y]
    (f : I → X.functionField) (hD : IsLocallyRankOne X (denominatorModule X f))
    (i₀ : I) (hi₀ : f i₀ = 1) (β : Y ⟶ X) [IsDominant β]
    (hJ : Blowup.cartierPullback (baseIdeal X f) β) :
    IsIso ((Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y))).map
      (pulledCoordinateMap X f β i₀)) := by
  let G := Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y))
  let d₀ := G.map (pulledCoordinateMap X f β i₀)
  let σ := G.map ((Scheme.Modules.pullback β).map (denominatorInclusion X f) ≫
      (pullbackUnitIso β).hom) ≫ (pullbackUnitIso (Y.fromSpecStalk (genericPoint Y))).hom
  let : IsIso σ := doubleGenericDenominatorMap_isIso X f hD β
  have hd : d₀ ≠ 0 := by
    intro hz
    apply iso_to_fieldUnit_ne_zero σ
    have hf : d₀ ≫ genericBaseInclusion X f β = σ :=
      genericCoordinateMap_one_inclusion X f i₀ hi₀ β
    exact hf.symm.trans ((congrArg (fun v ↦ v ≫ genericBaseInclusion X f β) hz).trans
      (by simp only [zero_comp]))
  exact fieldLineBundleMap_isIso_of_ne_zero Y.functionField
    ⟨_, pullback_locallyRankOne (Y.fromSpecStalk (genericPoint Y)) _
      (pullback_locallyRankOne β _ hD)⟩
    ⟨_, pullback_locallyRankOne (Y.fromSpecStalk (genericPoint Y)) _ hJ⟩ d₀ hd

private theorem genericBaseInclusion_isIso [IsIntegral Y]
    (f : I → X.functionField) (hD : IsLocallyRankOne X (denominatorModule X f))
    (i₀ : I) (hi₀ : f i₀ = 1) (β : Y ⟶ X) [IsDominant β]
    (hJ : Blowup.cartierPullback (baseIdeal X f) β) :
    IsIso (genericBaseInclusion X f β) := by
  let d₀ := (Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y))).map
    (pulledCoordinateMap X f β i₀)
  let : IsIso d₀ := genericCoordinateMap_selected_isIso X f hD i₀ hi₀ β hJ
  have : IsIso (d₀ ≫ genericBaseInclusion X f β) := by
    rw [genericCoordinateMap_one_inclusion X f i₀ hi₀ β]
    exact doubleGenericDenominatorMap_isIso X f hD β
  exact IsIso.of_isIso_comp_left d₀ (genericBaseInclusion X f β)

private theorem genericCoordinateMap_scalar [IsIntegral Y]
    (f : I → X.functionField) (hD : IsLocallyRankOne X (denominatorModule X f))
    (i₀ : I) (hi₀ : f i₀ = 1) (β : Y ⟶ X) [IsDominant β]
    (hJ : Blowup.cartierPullback (baseIdeal X f) β) (i : I) :
    (Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y))).map
        (pulledCoordinateMap X f β i) =
      (Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y))).map
          (pulledCoordinateMap X f β i₀) ≫
        globalScalarEndomorphism (Spec Y.functionField)
          ((Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y))).obj
            (pulledBaseModule X f β))
          ((Scheme.ΓSpecIso Y.functionField).inv.hom (Scheme.functionFieldMap β (f i))) := by
  let G := Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y))
  let t := genericBaseInclusion X f β
  let d₀ := G.map (pulledCoordinateMap X f β i₀)
  let a := (Scheme.ΓSpecIso Y.functionField).inv.hom (Scheme.functionFieldMap β (f i))
  let : IsIso t := genericBaseInclusion_isIso X f hD i₀ hi₀ β hJ
  have hn : globalScalarEndomorphism (Spec Y.functionField)
        (G.obj (pulledBaseModule X f β)) a ≫ t =
      t ≫ fieldScalar (Scheme.functionFieldMap β (f i)) :=
    ((globalScalarCenter (Spec Y.functionField) a).naturality t).symm.trans
      (congrArg (fun s ↦ t ≫ s) (globalScalarEndomorphism_unit (Spec Y.functionField) a))
  apply (cancel_mono t).mp
  calc
    _ = (Scheme.Modules.pullback (Y.fromSpecStalk (genericPoint Y))).map
          ((Scheme.Modules.pullback β).map (numeratorMap X f i) ≫
            (pullbackUnitIso β).hom) ≫
        (pullbackUnitIso (Y.fromSpecStalk (genericPoint Y))).hom :=
      genericCoordinateMap_inclusion X f β i
    _ = (d₀ ≫ t) ≫ fieldScalar (Scheme.functionFieldMap β (f i)) :=
      (doubleGenericNumeratorMap X f β i).trans
        (congrArg (fun z ↦ z ≫ fieldScalar (Scheme.functionFieldMap β (f i)))
          (genericCoordinateMap_one_inclusion X f i₀ hi₀ β).symm)
    _ = d₀ ≫ (globalScalarEndomorphism (Spec Y.functionField)
        (G.obj (pulledBaseModule X f β)) a ≫ t) := by rw [hn, Category.assoc]
    _ = _ := (Category.assoc _ _ _).symm


private theorem pulledLineSourceFamily_iso_field
    {Z : Scheme.{u}} {K : Type u} [Field K] {ι : Type u}
    (D J : Z.Modules) (hD : IsLocallyRankOne Z D) (g : Spec (.of K) ⟶ Z)
    (d : ι → (D ⟶ J)) (i₀ : ι) (a : ι → K)
    (hselected : IsIso ((Scheme.Modules.pullback g).map (d i₀)))
    (hscalar : ∀ i, (Scheme.Modules.pullback g).map (d i) =
      (Scheme.Modules.pullback g).map (d i₀) ≫
        globalScalarEndomorphism (Spec (.of K)) ((Scheme.Modules.pullback g).obj J)
          ((Scheme.ΓSpecIso (.of K)).inv.hom (a i))) :
    ∃ e : (Scheme.Modules.pullback g).obj
        (ProjectiveSpace.FromSections.LineSource.coefficientModule D J) ≅
        SheafOfModules.unit (Spec (.of K)).ringCatSheaf,
      ∀ i, ProjectiveSpace.FromSections.pulledFamily g
          (fun j ↦ ProjectiveSpace.FromSections.LineSource.sectionOfHom D J hD (d j)) i ≫
        e.hom = ProjectiveSpace.FromSections.FieldSpan.family a i := by
  let S := Spec (.of K)
  let F := Scheme.Modules.pullback g
  let E := F.obj (dualSheaf Z D)
  let H := moduleTensorLeftFunctor S E
  let M := ProjectiveSpace.FromSections.LineSource.coefficientModule D J
  let αD := pullbackTensorMap g (dualSheaf Z D) D
  let αJ := pullbackTensorMap g (dualSheaf Z D) J
  let c := (pullbackUnitIso g).inv ≫ F.map (dualEvaluationIso Z ⟨D, hD⟩).inv ≫ αD
  let s := ProjectiveSpace.FromSections.pulledFamily g
    (fun j ↦ ProjectiveSpace.FromSections.LineSource.sectionOfHom D J hD (d j))
  let : IsIso αD := Scheme.Modules.Pullback.Tensor.pullbackTensorMap_isIso g (dualSheaf Z D) D
  let : IsIso αJ := Scheme.Modules.Pullback.Tensor.pullbackTensorMap_isIso g (dualSheaf Z D) J
  let : IsIso c := inferInstance
  let : IsIso (F.map (d i₀)) := hselected
  have htriangle (i : ι) : s i ≫ αJ = c ≫ H.map (F.map (d i)) := by
    have hn : F.map ((lineBundleDualTensorEquivalence Z ⟨D, hD⟩).functor.map (d i)) ≫ αJ =
        αD ≫ H.map (F.map (d i)) := by
      change F.map (tensorSheafMap Z (𝟙 (dualSheaf Z D)) (d i)) ≫ αJ =
        αD ≫ tensorSheafMap S (𝟙 E) (F.map (d i))
      exact (pullbackTensorMap_naturality g (𝟙 (dualSheaf Z D)) (d i)).trans
        (congrArg (fun t : F.obj (dualSheaf Z D) ⟶ F.obj (dualSheaf Z D) ↦
          αD ≫ tensorSheafMap S t (F.map (d i))) (F.map_id (dualSheaf Z D)))
    calc
      _ = (pullbackUnitIso g).inv ≫ F.map (dualEvaluationIso Z ⟨D, hD⟩).inv ≫
          (F.map ((lineBundleDualTensorEquivalence Z ⟨D, hD⟩).functor.map (d i)) ≫ αJ) := by
        simp only [s, ProjectiveSpace.FromSections.pulledFamily,
          ProjectiveSpace.FromSections.pullbackSection,
          ProjectiveSpace.FromSections.LineSource.sectionOfHom, F, Functor.map_comp, Category.assoc]
      _ = c ≫ H.map (F.map (d i)) := by rw [hn]; simp only [c, Category.assoc]
  let : IsIso (s i₀) := by
    have : IsIso (s i₀ ≫ αJ) := by rw [htriangle]; infer_instance
    exact IsIso.of_isIso_comp_right (s i₀) αJ
  have hsections (i : ι) : s i = s i₀ ≫
      globalScalarEndomorphism S (F.obj M) ((Scheme.ΓSpecIso (.of K)).inv.hom (a i)) := by
    let b := (Scheme.ΓSpecIso (.of K)).inv.hom (a i)
    have hmap : H.map (F.map (d i)) = H.map (F.map (d i₀)) ≫
        globalScalarEndomorphism S (H.obj (F.obj J)) b := by
      calc
        _ = H.map (F.map (d i₀) ≫ globalScalarEndomorphism S (F.obj J) b) :=
          congrArg H.map (hscalar i)
        _ = H.map (F.map (d i₀)) ≫ H.map (globalScalarEndomorphism S (F.obj J) b) :=
          H.map_comp _ _
        _ = _ := congrArg (fun t ↦ H.map (F.map (d i₀)) ≫ t)
          (moduleTensorLeftFunctor_map_globalScalarEndomorphism S E (F.obj J) b)
    have hn : globalScalarEndomorphism S (F.obj M) b ≫ αJ =
        αJ ≫ globalScalarEndomorphism S (H.obj (F.obj J)) b :=
      ((globalScalarCenter S b).naturality αJ).symm
    apply (cancel_mono αJ).mp
    calc
      _ = c ≫ H.map (F.map (d i)) := htriangle i
      _ = c ≫ (H.map (F.map (d i₀)) ≫
          globalScalarEndomorphism S (H.obj (F.obj J)) b) := congrArg (fun t ↦ c ≫ t) hmap
      _ = (s i₀ ≫ αJ) ≫ globalScalarEndomorphism S (H.obj (F.obj J)) b :=
        (Category.assoc c (H.map (F.map (d i₀)))
          (globalScalarEndomorphism S (H.obj (F.obj J)) b)).symm.trans
          (congrArg (fun t ↦ t ≫ globalScalarEndomorphism S (H.obj (F.obj J)) b)
            (htriangle i₀).symm)
      _ = s i₀ ≫ (globalScalarEndomorphism S (F.obj M) b ≫ αJ) := by
        rw [hn, Category.assoc]
      _ = _ := (Category.assoc _ _ _).symm
  refine ⟨(asIso (s i₀)).symm, ?_⟩
  intro i
  let b := (Scheme.ΓSpecIso (.of K)).inv.hom (a i)
  have hn : globalScalarEndomorphism S (SheafOfModules.unit S.ringCatSheaf) b ≫ s i₀ =
      s i₀ ≫ globalScalarEndomorphism S (F.obj M) b :=
    ((globalScalarCenter S b).naturality (s i₀)).symm
  change s i ≫ inv (s i₀) = _
  calc
    _ = (s i₀ ≫ globalScalarEndomorphism S (F.obj M) b) ≫ inv (s i₀) :=
      congrArg (fun t ↦ t ≫ inv (s i₀)) (hsections i)
    _ = (globalScalarEndomorphism S (SheafOfModules.unit S.ringCatSheaf) b ≫ s i₀) ≫
        inv (s i₀) := congrArg (fun t ↦ t ≫ inv (s i₀)) hn.symm
    _ = globalScalarEndomorphism S (SheafOfModules.unit S.ringCatSheaf) b := by
      rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    _ = _ := globalScalarEndomorphism_unit S b


/-- The actual map constructed from the pulled original row recovers the
original native chart map after the canonical function-field transport. -/
theorem mapAfterPrincipalization_generic [IsIntegral Y]
    (f : I → X.functionField) (hD : IsLocallyRankOne X (denominatorModule X f))
    (p : X ⟶ Spec (.of R)) (β : Y ⟶ X) [IsDominant β]
    (hJ : Blowup.cartierPullback (baseIdeal X f) β)
    (i₀ : I) (φ : ProjectiveSpace.coordinateRing R I i₀ →+* X.functionField)
    (hf : ∀ i, f i = φ (ProjectiveSpace.coordinateRatio R I i₀ i))
    (hbase : (Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X i₀)
        (MvPolynomial.isHomogeneous_X R i₀) Nat.zero_lt_one) ≫
      ProjectiveSpace.toSpec R I = (X.fromSpecStalk (genericPoint X)) ≫ p) :
    (Y.fromSpecStalk (genericPoint Y)) ≫ mapAfterPrincipalization X f hD p β hJ =
      Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)) ≫
        Spec.map (CommRingCat.ofHom φ) ≫
          Proj.awayι (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X i₀)
            (MvPolynomial.isHomogeneous_X R i₀) Nat.zero_lt_one := by
  let j := Y.fromSpecStalk (genericPoint Y)
  let α := Scheme.functionFieldMap β
  let a := fun i ↦ α (f i)
  let φY := α.comp φ
  let bR := φY.comp (ProjectiveSpace.coordinateRingCoefficient R I i₀)
  let ιP := Proj.awayι (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X i₀)
    (MvPolynomial.isHomogeneous_X R i₀) Nat.zero_lt_one
  let D := pulledDenominatorModule X f β
  let J := pulledBaseModule X f β
  let hDY := pullback_locallyRankOne β (denominatorModule X f) hD
  let d := pulledCoordinateMap X f β
  let M := ProjectiveSpace.FromSections.LineSource.coefficientModule D J
  let hM := ProjectiveSpace.FromSections.LineSource.coefficientModule_locallyRankOne D J hDY hJ
  let s := fun i ↦ ProjectiveSpace.FromSections.LineSource.sectionOfHom D J hDY (d i)
  have hi₀ : f i₀ = 1 := (hf i₀).trans (by
    rw [ProjectiveSpace.coordinateRatio_self, map_one])
  obtain ⟨e, he⟩ := pulledLineSourceFamily_iso_field D J hDY j d i₀ a
    (genericCoordinateMap_selected_isIso X f hD i₀ hi₀ β hJ)
    (genericCoordinateMap_scalar X f hD i₀ hi₀ β hJ)
  have ha₀ : a i₀ ≠ 0 := by
    change α (f i₀) ≠ 0
    rw [hi₀, map_one]
    exact one_ne_zero
  let : Epi (Sigma.desc (ProjectiveSpace.FromSections.FieldSpan.family a)) :=
    ProjectiveSpace.FromSections.FieldSpan.family_epi_of_nonzero a i₀ ha₀
  have hmap : j ≫ mapAfterPrincipalization X f hD p β hJ =
      ProjectiveSpace.FromSections.mapOfFiniteFamily (j ≫ (β ≫ p))
        (SheafOfModules.unit (Spec Y.functionField).ringCatSheaf)
        (ProjectiveSpace.FromSections.FieldSpan.unit_rankOne _)
        (ProjectiveSpace.FromSections.FieldSpan.family a) := by
    change j ≫ ProjectiveSpace.FromSections.mapOfFiniteFamily (β ≫ p) M hM s = _
    refine (ProjectiveSpace.FromSections.mapOfFiniteFamily_pullback_iso j (β ≫ p) M hM s
      (SheafOfModules.unit (Spec Y.functionField).ringCatSheaf) e).trans ?_
    apply ProjectiveSpace.FromSections.mapOfFiniteFamily_iso _ _ _ _ _ _ _ (Iso.refl _)
    intro i
    exact (Category.comp_id _).trans (he i)
  have hφY : Spec.map (CommRingCat.ofHom φY) =
      Spec.map (CommRingCat.ofHom α) ≫ Spec.map (CommRingCat.ofHom φ) :=
    Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom α)
  have hb : Spec.map (CommRingCat.ofHom bR) = j ≫ (β ≫ p) := by
    calc
      _ = Spec.map (CommRingCat.ofHom φY) ≫ ιP ≫ ProjectiveSpace.toSpec R I := by
        rw [ProjectiveSpace.coordinateChart_toSpec]
        exact Spec.map_comp (CommRingCat.ofHom
          (ProjectiveSpace.coordinateRingCoefficient R I i₀)) (CommRingCat.ofHom φY)
      _ = Spec.map (CommRingCat.ofHom α) ≫
          ((Spec.map (CommRingCat.ofHom φ) ≫ ιP) ≫ ProjectiveSpace.toSpec R I) := by
        rw [hφY, Category.assoc, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom α) ≫ ((X.fromSpecStalk (genericPoint X)) ≫ p) :=
        congrArg (fun q ↦ Spec.map (CommRingCat.ofHom α) ≫ q) hbase
      _ = _ := by
        rw [← Category.assoc, ← Scheme.fromSpecStalk_genericPoint_naturality β, Category.assoc]
  have hfield := ProjectiveSpace.FromSections.FieldSpan.mapOfFiniteFamily_eq_chart_of_values
    bR a i₀ φY (fun _ ↦ rfl) (fun i ↦ congrArg α (hf i))
  calc
    _ = ProjectiveSpace.FromSections.mapOfFiniteFamily (j ≫ (β ≫ p))
        (SheafOfModules.unit (Spec Y.functionField).ringCatSheaf)
        (ProjectiveSpace.FromSections.FieldSpan.unit_rankOne _)
        (ProjectiveSpace.FromSections.FieldSpan.family a) := hmap
    _ = ProjectiveSpace.FromSections.mapOfFiniteFamily (Spec.map (CommRingCat.ofHom bR))
        (SheafOfModules.unit (Spec Y.functionField).ringCatSheaf)
        (ProjectiveSpace.FromSections.FieldSpan.unit_rankOne _)
        (ProjectiveSpace.FromSections.FieldSpan.family a) := congrArg
      (fun q ↦ ProjectiveSpace.FromSections.mapOfFiniteFamily q
        (SheafOfModules.unit (Spec Y.functionField).ringCatSheaf)
        (ProjectiveSpace.FromSections.FieldSpan.unit_rankOne _)
        (ProjectiveSpace.FromSections.FieldSpan.family a)) hb.symm
    _ = Spec.map (CommRingCat.ofHom φY) ≫ ιP := hfield
    _ = _ := by rw [hφY, Category.assoc]

omit [Fintype I] in
/-- An original generic projective map extends after a finite chain of the
actual regular point blowups, with its original base and generic triangles. -/
theorem exists_pointBlowupChain_projectiveExtension [IsNoetherian X] [Finite I]
    (hX : RegularStalks X) (hd : topologicalKrullDim X ≤ 2)
    (p : X ⟶ Spec (.of R)) (gη : Spec X.functionField ⟶ ProjectiveSpace R I)
    (hgη : gη ≫ ProjectiveSpace.toSpec R I = (X.fromSpecStalk (genericPoint X)) ≫ p) :
    ∃ (Y : Scheme.{u}) (β : Y ⟶ X) (c : Blowup.PointBlowupChain β),
      letI : IsIntegral Y := c.isIntegral inferInstance
      letI : IsDominant β := c.isDominant inferInstance
      ∃ h : Y ⟶ ProjectiveSpace R I,
        IsProper β ∧ BirationalOver β (𝟙 X) ∧ RegularStalks Y ∧
        (∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 2) ∧
        h ≫ ProjectiveSpace.toSpec R I = β ≫ p ∧
        (Y.fromSpecStalk (genericPoint Y)) ≫ h =
          Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)) ≫ gη := by
  classical
  let := Fintype.ofFinite I
  obtain ⟨i₀, φ, hφ⟩ := ProjectiveSpace.exists_coordinateChart_factorization gη
  let f := ProjectiveSpace.chartHomCoordinates i₀ φ
  have hi₀ : f i₀ = 1 := ProjectiveSpace.chartHomCoordinates_self i₀ φ
  have hD := denominatorModule_isLocallyRankOne X hX f i₀ hi₀
  have hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 2 := by
    rw [Scheme.topologicalKrullDim_eq_iSup_stalk] at hd
    intro x
    exact (le_iSup (fun z : X ↦ ringKrullDim (X.presheaf.stalk z)) x).trans hd
  let : IsArtinianScheme (baseIdeal X f).subscheme :=
    baseIdeal_isArtinian_subscheme X hX hdim f i₀ hi₀
  obtain ⟨Y, β, ⟨c⟩, hp, _, hbir, _, hreg, hdimY, hJ⟩ :=
    Blowup.exists_regular_pointBlowup_principalization hX hdim (baseIdeal X f)
      (baseIdeal_ne_bot X f i₀ hi₀)
  let : IsIntegral Y := c.isIntegral inferInstance
  let : IsDominant β := c.isDominant inferInstance
  let h := mapAfterPrincipalization X f hD p β hJ
  refine ⟨Y, β, c, h, hp, hbir, hreg, hdimY,
    mapAfterPrincipalization_toSpec X f hD p β hJ, ?_⟩
  have hbase : (Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X i₀)
        (MvPolynomial.isHomogeneous_X R i₀) Nat.zero_lt_one) ≫
      ProjectiveSpace.toSpec R I = (X.fromSpecStalk (genericPoint X)) ≫ p := by
    rw [hφ, hgη]
  calc
    _ = Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)) ≫
        (Spec.map (CommRingCat.ofHom φ) ≫
          Proj.awayι (MvPolynomial.homogeneousSubmodule I R) (MvPolynomial.X i₀)
            (MvPolynomial.isHomogeneous_X R i₀) Nat.zero_lt_one) :=
      mapAfterPrincipalization_generic X f hD p β hJ i₀ φ (fun _ ↦ rfl) hbase
    _ = _ := congrArg (fun q ↦
      Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)) ≫ q) hφ

end AlgebraicGeometry.Scheme.RationalCoordinates
