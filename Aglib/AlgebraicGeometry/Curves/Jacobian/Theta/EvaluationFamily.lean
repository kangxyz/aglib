/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.Theta.DistinctOpen
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.SquareConcentration
public import Aglib.AlgebraicGeometry.Curves.Abel.EvaluationDegree

/-!
# Actual evaluation on the canonical curve family over the retained open

Equip the EXISTING rank-one/non-repeated open with its original structure
map and pull back the SAME universal rigidified pair. The original
cartesian family square and the native rank-one open supply cohomological
concentration on this canonical X×V. The existing evaluation constructor
then defines one actual relative Cartier divisor, finite and flat over V.

The construction and whole class-recovery equation precede geometric
point evaluation. No theta incidence equality, fibre-reducedness or
polarization assertion is supplied as a premise.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Scheme Scheme.Modules Scheme.Modules.Hom Scheme.Modules.Invertible
open Scheme.Cohomology Scheme.RelativePicard Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve

variable {k : Type u} [Field k] {X : FScheme k} (hX : Properties X)
  (o : Spec (.of k) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _)
  (P : LocallyNoetherianOver (Spec (.of k)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙
    (fppfPicardSheaf X.hom).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  [LocallyOfFiniteType P.obj.hom] [IsSeparated P.obj.hom]

/-- The original retained open with its original structure map over k. -/
def thetaParameterOver : FScheme k := by
  let := picardCommGrpObj X.hom P R
  exact Over.mk ((rankOneNonRepeatedOpen hX o ho P R).ι ≫ (identityComponentOver P.obj).hom)

/-- Its original inclusion into the same Jacobian, as a morphism over k. -/
def thetaParameterι :
    letI := picardCommGrpObj X.hom P R
    thetaParameterOver hX o ho P R ⟶ identityComponentOver P.obj := by
  let := picardCommGrpObj X.hom P R
  exact Over.homMk (rankOneNonRepeatedOpen hX o ho P R).ι rfl

/-- The original universal degree-g pair restricted by that actual inclusion. -/
def thetaUniversalPair : RigidifiedPair X.hom o ho (thetaParameterOver hX o ho P R) := by
  let := picardCommGrpObj X.hom P R
  exact RigidifiedPair.map (thetaParameterι hX o ho P R)
    (degreeUniversalPair hX o ho P R (coherentGenus k X))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
local instance thetaParameterLocallyNoetherian :
    IsLocallyNoetherian (thetaParameterOver hX o ho P R).left := by
  let := picardCommGrpObj X.hom P R
  have : IsLocallyNoetherian (identityComponentOver P.obj).left :=
    LocallyOfFiniteType.isLocallyNoetherian (identityComponentOver P.obj).hom
  exact isLocallyNoetherian_of_isOpenImmersion (rankOneNonRepeatedOpen hX o ho P R).ι

local instance thetaFamilyProper :
    IsProper (pullback.snd X.hom (thetaParameterOver hX o ho P R).hom) := by
  let := hX.proper
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
local instance thetaFamilyRelativeDimension :
    SmoothOfRelativeDimension 1 (pullback.snd X.hom (thetaParameterOver hX o ho P R).hom) := by
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{u} 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  exact MorphismProperty.pullback_snd _ _ hX.smooth

local instance thetaFamilySmooth :
    Smooth (pullback.snd X.hom (thetaParameterOver hX o ho P R).hom) :=
  SmoothOfRelativeDimension.smooth 1 _

local instance thetaFamilyConnected :
    GeometricallyConnected (pullback.snd X.hom (thetaParameterOver hX o ho P R).hom) := by
  let := hX.connected
  infer_instance

/-- The original retained open is locally Noetherian. -/
theorem thetaParameter_isLocallyNoetherian :
    IsLocallyNoetherian (thetaParameterOver hX o ho P R).left := inferInstance

/-- The canonical family is proper by the original curve's properness. -/
theorem thetaFamily_isProper :
    IsProper (pullback.snd X.hom (thetaParameterOver hX o ho P R).hom) := inferInstance

/-- The canonical family retains actual smooth relative dimension one. -/
theorem thetaFamily_smoothOfRelativeDimension :
    SmoothOfRelativeDimension 1 (pullback.snd X.hom (thetaParameterOver hX o ho P R).hom) :=
  inferInstance

/-- The original geometrically connected curve fibres are retained. -/
theorem thetaFamily_geometricallyConnected :
    GeometricallyConnected (pullback.snd X.hom (thetaParameterOver hX o ho P R).hom) :=
  inferInstance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Actual rank-one concentration on the canonical X×V, transported by
the original family pullback square and the original coefficient maps. -/
theorem thetaUniversalPair_concentrated :
    FibreCohomologyConcentrated (pullback.snd X.hom (thetaParameterOver hX o ho P R).hom)
      (thetaUniversalPair hX o ho P R).bundle.val 1 := by
  let := picardCommGrpObj X.hom P R
  let := hX.smooth
  let := hX.proper
  let := hX.connected
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{u} 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  let J := identityComponentOver P.obj
  have : IsLocallyNoetherian J.left := LocallyOfFiniteType.isLocallyNoetherian J.hom
  let U := degreeUniversalRankOneOpen hX o ho P R (coherentGenus k X)
  let V := rankOneNonRepeatedOpen hX o ho P R
  let a := J.left.homOfLE (rankOneNonRepeatedOpen_le_rankOne hX o ho P R)
  have ha : a ≫ U.ι = V.ι := Scheme.homOfLE_ι _ _
  let f := pullback.snd X.hom J.hom
  have : SmoothOfRelativeDimension 1 f := MorphismProperty.pullback_snd _ _ hX.smooth
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  let M := (degreeUniversalPair hX o ho P R (coherentGenus k X)).bundle
  let MU := pullbackLineBundle (pullback.fst f U.ι) M
  have hMU : FibreCohomologyConcentrated (pullback.snd f U.ι) MU.val 1 :=
    Abel.rankOneConcentration f M
  let p := pullback.snd X.hom (thetaParameterOver hX o ho P R).hom
  let b : pullback X.hom (thetaParameterOver hX o ho P R).hom ⟶ pullback X.hom J.hom :=
    (familyScheme X.hom).map (thetaParameterι hX o ho P R)
  have H : IsPullback b p f V.ι := by
    have hb : b = Hom.familyMap X.hom J.hom (thetaParameterOver hX o ho P R).hom
        V.ι rfl := Abel.BoundedFamily.familyScheme_map_eq_familyMap X.hom
      (thetaParameterι hX o ho P R)
    rw [hb]
    exact Hom.familyMap_isPullback X.hom J.hom (thetaParameterOver hX o ho P R).hom V.ι rfl
  have H' : IsPullback b p f (a ≫ U.ι) := by rw [ha]; exact H
  let HU := IsPullback.of_hasPullback f U.ι
  let c := HU.lift b (p ≫ a) (by rw [H'.w, Category.assoc])
  have HC : IsPullback c p (pullback.snd f U.ι) a := H'.of_right' HU
  have hc : c ≫ pullback.fst f U.ι = b := HU.lift_fst _ _ _
  let C : (Scheme.Modules.pullback c).obj MU.val ≅
      (thetaUniversalPair hX o ho P R).bundle.val :=
    (Scheme.Modules.pullbackComp c (pullback.fst f U.ι)).app M.val ≪≫
      (Scheme.Modules.pullbackCongr hc).app M.val
  exact FibreCohomologyConcentrated.of_isPullback HC MU.val
    (thetaUniversalPair hX o ho P R).bundle.val C 1 hMU

/-- The existing evaluation contraction applied to this actual canonical
curve family, with its proved concentration. -/
def thetaEvaluationContraction :
    (evaluationIdealLineBundle (pullback.snd X.hom (thetaParameterOver hX o ho P R).hom)
      (thetaUniversalPair hX o ho P R).bundle (thetaUniversalPair_concentrated hX o ho P R)).val ⟶
        (show (pullback X.hom (thetaParameterOver hX o ho P R).hom).Modules from
          SheafOfModules.unit (pullback X.hom (thetaParameterOver hX o ho P R).hom).ringCatSheaf) :=
  evaluationContraction (pullback.snd X.hom (thetaParameterOver hX o ho P R).hom)
    (thetaUniversalPair hX o ho P R).bundle (thetaUniversalPair_concentrated hX o ho P R)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original canonical evaluation contraction is monic. -/
theorem mono_thetaEvaluationContraction : Mono (thetaEvaluationContraction hX o ho P R) := by
  let p := pullback.snd X.hom (thetaParameterOver hX o ho P R).hom
  let L := (thetaUniversalPair hX o ho P R).bundle
  let hL := thetaUniversalPair_concentrated hX o ho P R
  have hr := Abel.evaluationContraction_geometric_regular p L hL
    smoothFieldNormality normalComponentsOpen (fun K _ _ t =>
      Abel.rankOneFamily_fibre_properties p K t)
  exact (fibrewiseRegularLineBundle _ _ p (evaluationIdealLineBundle p L hL)
    (evaluationContraction p L hL) inferInstance inferInstance hr).1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The positive line bundle of the one actual evaluation zero scheme,
formed from its original kernel ideal. -/
def thetaEvaluationPositiveLineBundle :
    LineBundle (pullback X.hom (thetaParameterOver hX o ho P R).hom) := by
  have : Mono (thetaEvaluationContraction hX o ho P R) :=
    mono_thetaEvaluationContraction hX o ho P R
  exact dualLineBundle _ (zeroIdealLineBundle
    (evaluationIdealLineBundle (pullback.snd X.hom (thetaParameterOver hX o ho P R).hom)
      (thetaUniversalPair hX o ho P R).bundle (thetaUniversalPair_concentrated hX o ho P R))
    (thetaEvaluationContraction hX o ho P R))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Whole original class recovery: the given universal bundle is the
positive evaluation-divisor bundle tensored with its actual base correction. -/
theorem thetaEvaluation_class_recovery :
    classOf _ (thetaUniversalPair hX o ho P R).bundle =
      classOf _ (thetaEvaluationPositiveLineBundle hX o ho P R) +
        pullbackClass (pullback.snd X.hom (thetaParameterOver hX o ho P R).hom)
          (classOf _ (directImageLineBundle
            (pullback.snd X.hom (thetaParameterOver hX o ho P R).hom)
            (thetaUniversalPair hX o ho P R).bundle
            (thetaUniversalPair_concentrated hX o ho P R))) := by
  let p := pullback.snd X.hom (thetaParameterOver hX o ho P R).hom
  let L := (thetaUniversalPair hX o ho P R).bundle
  let hL := thetaUniversalPair_concentrated hX o ho P R
  have : Mono (evaluationContraction p L hL) := mono_thetaEvaluationContraction hX o ho P R
  exact Abel.evaluationZero_class_recovery p L hL

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual evaluation divisor is finite flat and locally finitely
presented over the original retained open. -/
theorem thetaEvaluation_finite_flat :
    IsFinite (zeroInclusion (thetaEvaluationContraction hX o ho P R) ≫
      pullback.snd X.hom (thetaParameterOver hX o ho P R).hom) ∧
    Flat (zeroInclusion (thetaEvaluationContraction hX o ho P R) ≫
      pullback.snd X.hom (thetaParameterOver hX o ho P R).hom) ∧
    LocallyOfFinitePresentation (zeroInclusion (thetaEvaluationContraction hX o ho P R) ≫
      pullback.snd X.hom (thetaParameterOver hX o ho P R).hom) := by
  let p := pullback.snd X.hom (thetaParameterOver hX o ho P R).hom
  exact Abel.evaluationZero_finite_flat smoothFieldNormality normalComponentsOpen
    fibrewiseRegularLineBundle smoothRelativeCartierLocality p
    (thetaUniversalPair hX o ho P R).bundle (thetaUniversalPair_concentrated hX o ho P R)
    (fun K _ _ t => Abel.rankOneFamily_fibre_properties p K t)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same original zero immersion is a relative effective Cartier
divisor, with every monicity and flatness premise proved. -/
theorem thetaEvaluation_isRelativeEffectiveCartier :
    Hom.IsRelativeEffectiveCartier (zeroInclusion (thetaEvaluationContraction hX o ho P R))
      (pullback.snd X.hom (thetaParameterOver hX o ho P R).hom) := by
  have : Mono (thetaEvaluationContraction hX o ho P R) :=
    mono_thetaEvaluationContraction hX o ho P R
  exact {
    isClosedImmersion := zeroInclusion_isClosedImmersion _
    isLocallyRankOne := (zeroIdealLineBundle
      (evaluationIdealLineBundle (pullback.snd X.hom (thetaParameterOver hX o ho P R).hom)
        (thetaUniversalPair hX o ho P R).bundle (thetaUniversalPair_concentrated hX o ho P R))
      (thetaEvaluationContraction hX o ho P R)).property
    flat := (thetaEvaluation_finite_flat hX o ho P R).2.1 }

end AlgebraicGeometry.Scheme.OverField.Curve
