/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Blowup.ProjectiveCenter
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Blowup.NodeAtlas
public import Aglib.AlgebraicGeometry.Morphisms.Etale.PointShrinking

/-!
Native extraction from the R5 local-model source
`PointedResolution.Blowup.Comparison`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`95e4c37ca6fd35078646a8fbe06753927ec2d227cc676d5eb46c4fd6f02237b5`.
Actual comparison maps, uniqueness/cartesian/properness and residue triangles for supplied common
  critical chart and exact power-node equation. Two discriminant-thickness-to-first-blowup bridge
  constructors are retained separately; no universal family is supplied here.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

/-!
# The canonical first-blowup comparison for the original affine and projective Weierstrass node
  through the same common chart.

The declarations retain their original qualified interfaces and mathematical
inputs; the source-coverage comments below retain their original boundaries.
-/

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode
open WeierstrassCurve
universe u

section CommonChartBlowupComparison


/-!
# First blowups of the original affine Weierstrass centre and the R-node centre

One actual common blowup maps canonically to both given actual blowups.
Both squares are proved cartesian from the same exact centre equality and the
ordinary universal flat-base-change family. All maps and triangles are kept.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
open WeierstrassCurve.CriticalNeighborhood
namespace AlgebraicGeometry.Scheme.PowerNode.CommonChartBlowup
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (n : ℕ)
variable (a : M.Carrierˣ)
  (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ n))

/-- Actual ordinary blowup of the original affine residue-point centre. -/
def originalBlowup (hex : NoetherianBlowupExistence.{u}) : BlowupDatum (originalCenterSheaf M) :=
  Classical.choice (hex _ _)

/-- Actual ordinary blowup of the common pulled-back ideal, on the same common chart. -/
def commonBlowup (hex : NoetherianBlowupExistence.{u}) : BlowupDatum (commonCenterSheaf M) :=
  Classical.choice (hex _ _)

/-- An actual ordinary blowup of the original-R node centre. -/
def nodeBlowup (hex : NoetherianBlowupExistence.{u}) :
    BlowupDatum (affineCenter (node π n) (centerIdeal π n)) :=
  Classical.choice (hex _ _)

variable (BW : BlowupDatum (originalCenterSheaf M))
variable (BN : BlowupDatum (affineCenter (node π n) (centerIdeal π n)))
variable (BC : BlowupDatum (commonCenterSheaf M))

/-- Canonical map to the same original affine blowup. -/
def toOriginal : BC.Y ⟶ BW.Y :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.map M.toOriginalScheme rfl BW BC

/-- Canonical map to the actual original-R node blowup. -/
def toNode : BC.Y ⟶ BN.Y :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.map (M.toPowerNodeScheme (π ^ n) a ha)
    (common_node_center_eq M π hπ n a ha) BN BC

@[reassoc] lemma toOriginal_triangle :
    toOriginal M BW BC ≫ BW.map = BC.map ≫ M.toOriginalScheme :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.map_triangle _ _ _ _
@[reassoc] lemma toNode_triangle :
    toNode M π hπ n a ha BN BC ≫ BN.map = BC.map ≫ M.toPowerNodeScheme (π ^ n) a ha :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.map_triangle _ _ _ _

lemma toOriginal_unique (g : BC.Y ⟶ BW.Y)
    (hg : g ≫ BW.map = BC.map ≫ M.toOriginalScheme) : g = toOriginal M BW BC :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.map_unique _ _ _ _ g hg
lemma toNode_unique (g : BC.Y ⟶ BN.Y)
    (hg : g ≫ BN.map = BC.map ≫ M.toPowerNodeScheme (π ^ n) a ha) :
    g = toNode M π hπ n a ha BN BC :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.map_unique _ _ _ _ g hg

lemma original_isPullback (hbc : BlowupFlatBaseChange.{u}) :
    IsPullback (toOriginal M BW BC) BC.map BW.map M.toOriginalScheme :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.isPullback hbc _ inferInstance rfl BW BC
lemma node_isPullback (hbc : BlowupFlatBaseChange.{u}) :
    IsPullback (toNode M π hπ n a ha BN BC) BC.map BN.map (M.toPowerNodeScheme (π ^ n) a ha) :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.isPullback hbc _ inferInstance
    (common_node_center_eq M π hπ n a ha) BN BC

lemma toOriginal_etale (hbc : BlowupFlatBaseChange.{u}) : Etale (toOriginal M BW BC) :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.etale hbc _ inferInstance rfl BW BC
lemma toNode_etale (hbc : BlowupFlatBaseChange.{u}) : Etale (toNode M π hπ n a ha BN BC) :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.etale hbc _ inferInstance
    (common_node_center_eq M π hπ n a ha) BN BC

/-- The actual common blowup comparison, over the same common chart. -/
def pullbackComparison (hbc : BlowupFlatBaseChange.{u}) :
    pullback BW.map M.toOriginalScheme ≅ pullback BN.map (M.toPowerNodeScheme (π ^ n) a ha) :=
  (original_isPullback M BW BC hbc).isoPullback.symm ≪≫
    (node_isPullback M π hπ n a ha BN BC hbc).isoPullback

@[reassoc] lemma pullbackComparison_hom_snd (hbc : BlowupFlatBaseChange.{u}) :
    (pullbackComparison M π hπ n a ha BW BN BC hbc).hom ≫ pullback.snd _ _ =
      pullback.snd BW.map M.toOriginalScheme := by
  simp [pullbackComparison]

@[reassoc] lemma pullbackComparison_inv_snd (hbc : BlowupFlatBaseChange.{u}) :
    (pullbackComparison M π hπ n a ha BW BN BC hbc).inv ≫ pullback.snd _ _ =
      pullback.snd BN.map (M.toPowerNodeScheme (π ^ n) a ha) := by
  simp [pullbackComparison]

/-- The comparison is precisely induced by the two retained canonical maps. -/
@[reassoc] lemma commonComparison_triangle (hbc : BlowupFlatBaseChange.{u}) :
    (original_isPullback M BW BC hbc).isoPullback.hom ≫
      (pullbackComparison M π hπ n a ha BW BN BC hbc).hom =
      (node_isPullback M π hπ n a ha BN BC hbc).isoPullback.hom := by
  simp [pullbackComparison]

lemma common_proper (hbc : BlowupFlatBaseChange.{u}) [IsProper BW.map] : IsProper BC.map :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.proper hbc _ inferInstance rfl BW BC

/-- Concrete application to the same existing one-step blowup used by the
R-node recursion, and the selected ordinary original affine blowup. -/
def firstStepComparison (m : ℕ) (a : M.Carrierˣ)
    (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (m + 2)))
    (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
    (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u}) :
    pullback (originalBlowup M hex).map M.toOriginalScheme ≅
      pullback (OneStepBlowup.ofFamilies π m hex hp hatlas).blowup.map
        (M.toPowerNodeScheme (π ^ (m + 2)) a ha) :=
  pullbackComparison M π hπ (m + 2) a ha (originalBlowup M hex)
    (OneStepBlowup.ofFamilies π m hex hp hatlas).blowup (commonBlowup M hex) hbc

end AlgebraicGeometry.Scheme.PowerNode.CommonChartBlowup

end
end CommonChartBlowupComparison

section ProjectiveBlowupComparison


/-! The same actual common blowup maps to the original projective blowup and
the original R-node blowup. Both comparisons are cartesian, and the projective
comparison factors through the original affine blowup by universal uniqueness. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open WeierstrassCurve.CriticalNeighborhood
open WeierstrassCurve.Projective
namespace AlgebraicGeometry.Scheme.PowerNode.ProjectiveNodeBlowup
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y)
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)

/-- Noetherianity is proved for the original projective scheme over the DVR. -/
lemma projective_isLocallyNoetherian : IsLocallyNoetherian (scheme W) :=
  LocallyOfFiniteType.isLocallyNoetherian (structureMap W)

/-- The ordinary blowup at exactly the original projective residue-point kernel. -/
def projectiveBlowup (hex : NoetherianBlowupExistence.{u}) : BlowupDatum (projectiveCenter he) := by
  letI := projective_isLocallyNoetherian (W := W)
  exact Classical.choice (hex _ _)

variable (BG : BlowupDatum (projectiveCenter he))
  (BW : BlowupDatum (CommonChartBlowup.originalCenterSheaf M))
  (BC : BlowupDatum (CommonChartBlowup.commonCenterSheaf M))

/-- The base-change map from the affine Weierstrass blowup to the projective blowup. -/
def affineToGlobal : BW.Y ⟶ BG.Y :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.map (affineChart W) (affine_center_comap M he) BG BW

/-- The base-change map from the common-chart blowup to the projective blowup. -/
def commonToGlobal : BC.Y ⟶ BG.Y :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.map (commonToProjective M) (common_center_comap M he)
    BG BC

@[reassoc] lemma affineToGlobal_triangle :
    affineToGlobal M he BG BW ≫ BG.map = BW.map ≫ affineChart W :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.map_triangle _ _ _ _

@[reassoc] lemma commonToGlobal_triangle :
    commonToGlobal M he BG BC ≫ BG.map = BC.map ≫ commonToProjective M :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.map_triangle _ _ _ _

lemma affineToGlobal_unique (g : BW.Y ⟶ BG.Y)
    (hg : g ≫ BG.map = BW.map ≫ affineChart W) : g = affineToGlobal M he BG BW :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.map_unique _ _ _ _ g hg

lemma commonToGlobal_unique (g : BC.Y ⟶ BG.Y)
    (hg : g ≫ BG.map = BC.map ≫ commonToProjective M) : g = commonToGlobal M he BG BC :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.map_unique _ _ _ _ g hg

/-- The actual maps commute, using both independently proved centre squares. -/
@[reassoc] lemma commonToGlobal_factor :
    CommonChartBlowup.toOriginal M BW BC ≫ affineToGlobal M he BG BW =
      commonToGlobal M he BG BC :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.map_comp (affineChart W) M.toOriginalScheme
    (affine_center_comap M he) rfl BG BW BC

lemma affine_global_isPullback (hbc : BlowupFlatBaseChange.{u}) :
    IsPullback (affineToGlobal M he BG BW) BW.map BG.map (affineChart W) :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.isPullback hbc _ inferInstance (affine_center_comap M
    he) BG BW

lemma common_global_isPullback (hbc : BlowupFlatBaseChange.{u}) :
    IsPullback (commonToGlobal M he BG BC) BC.map BG.map (commonToProjective M) :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.isPullback hbc _ inferInstance (common_center_comap M
    he) BG BC

lemma affineToGlobal_openImmersion (hbc : BlowupFlatBaseChange.{u}) :
    IsOpenImmersion (affineToGlobal M he BG BW) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (affine_global_isPullback M he BG BW hbc).flip inferInstance

lemma commonToGlobal_etale (hbc : BlowupFlatBaseChange.{u}) : Etale (commonToGlobal M he BG BC) :=
  AlgebraicGeometry.Scheme.Blowup.BaseChange.etale hbc _ inferInstance (common_center_comap M he)
    BG BC

variable (π : R) (hπ : Irreducible π) (n : ℕ) (a : M.Carrierˣ)
  (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ n))
  (BN : BlowupDatum (affineCenter (PowerNode.Rees.node π n) (PowerNode.Rees.centerIdeal π n)))

/-- Actual comparison between the global first blowup and the original R-node
first blowup, obtained from the same retained common blowup BC. -/
def globalNodeComparison (hbc : BlowupFlatBaseChange.{u}) :
    pullback BG.map (commonToProjective M) ≅
      pullback BN.map (M.toPowerNodeScheme (π ^ n) a ha) :=
  (common_global_isPullback M he BG BC hbc).isoPullback.symm ≪≫
    (CommonChartBlowup.node_isPullback M π hπ n a ha BN BC hbc).isoPullback

@[reassoc] lemma globalNodeComparison_hom_snd (hbc : BlowupFlatBaseChange.{u}) :
    (globalNodeComparison M he BG BC π hπ n a ha BN hbc).hom ≫ pullback.snd _ _ =
      pullback.snd BG.map (commonToProjective M) := by
  simp [globalNodeComparison]

@[reassoc] lemma globalNodeComparison_inv_snd (hbc : BlowupFlatBaseChange.{u}) :
    (globalNodeComparison M he BG BC π hπ n a ha BN hbc).inv ≫ pullback.snd _ _ =
      pullback.snd BN.map (M.toPowerNodeScheme (π ^ n) a ha) := by
  simp [globalNodeComparison]

@[reassoc] lemma globalNodeComparison_triangle (hbc : BlowupFlatBaseChange.{u}) :
    (common_global_isPullback M he BG BC hbc).isoPullback.hom ≫
      (globalNodeComparison M he BG BC π hπ n a ha BN hbc).hom =
      (CommonChartBlowup.node_isPullback M π hπ n a ha BN BC hbc).isoPullback.hom := by
  simp [globalNodeComparison]

lemma projectiveBlowup_proper (hex : NoetherianBlowupExistence.{u})
    (hp : NoetherianBlowupProper.{u}) : IsProper (projectiveBlowup he hex).map := by
  let := projective_isLocallyNoetherian (W := W)
  exact hp _ _ _

/-- The actual ordinary global blowup is proper over the original base. -/
lemma projectiveBlowup_structure_proper (hex : NoetherianBlowupExistence.{u})
    (hp : NoetherianBlowupProper.{u}) : IsProper ((projectiveBlowup he hex).map ≫ structureMap W)
      := by
  let := projectiveBlowup_proper he hex hp
  infer_instance

/-- Connection to the actual recursive first step is restricted to exponent
m + 2. The ordinary point blowup at exponent 1 is not its identity base case. -/
def globalFirstStepComparison (m : ℕ) (a : M.Carrierˣ)
    (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (m + 2)))
    (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
    (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u}) :
    pullback (projectiveBlowup he hex).map (commonToProjective M) ≅
      pullback (OneStepBlowup.ofFamilies π m hex hp hatlas).blowup.map
        (M.toPowerNodeScheme (π ^ (m + 2)) a ha) :=
  globalNodeComparison M he (projectiveBlowup he hex) (CommonChartBlowup.commonBlowup M hex)
    π hπ (m + 2) a ha (OneStepBlowup.ofFamilies π m hex hp hatlas).blowup hbc

end AlgebraicGeometry.Scheme.PowerNode.ProjectiveNodeBlowup

end
end ProjectiveBlowupComparison

section OriginalFirstBlowupBridge


/-!
# First actual blowup comparison from the original split residue node

The common chart and the thickness n come from the accepted original
Weierstrass construction. Only ordinary blowup existence and universal flat
base change are added. Both canonical maps and both actual cartesian squares
are retained; no compatibility of later centres is inferred.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
open WeierstrassCurve.CriticalNeighborhood
namespace AlgebraicGeometry.Scheme.PowerNode.CommonChartBlowup

/-- A point on the original affine scheme is an actual closed immersion. -/
lemma originalResidue_isClosedImmersion
    {R : Type u} [CommRing R] [IsLocalRing R]
    {W : WeierstrassCurve R} {x y : ResidueField R}
    (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (WeierstrassCurve.CriticalNeighborhood.originalResidue he).toRingHom)) :=
  IsClosedImmersion.spec_of_surjective _ (originalResidue_surjective he)

/- Source constructor, retained pending the original thickness localization.
The first modification over a genuine original residue node, with actual
ordinary blowups and both cartesian comparison maps on the same common chart. -/
/-- Ordinary properness of the original actual blowup. -/
lemma originalBlowup_proper
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {W : WeierstrassCurve R} {x y : ResidueField R} (M : WeierstrassCurve.CriticalNeighborhood W x
      y)
    (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u}) :
    IsProper (originalBlowup M hex).map := hp _ _ _

/-- Properness of the common blowup follows from the actual original cartesian square. -/
lemma commonBlowup_proper
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {W : WeierstrassCurve R} {x y : ResidueField R} (M : WeierstrassCurve.CriticalNeighborhood W x
      y)
    (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
    (hbc : BlowupFlatBaseChange.{u}) : IsProper (commonBlowup M hex).map := by
  let := originalBlowup_proper M hex hp
  exact common_proper M (originalBlowup M hex) (commonBlowup M hex) hbc

end AlgebraicGeometry.Scheme.PowerNode.CommonChartBlowup

end
end OriginalFirstBlowupBridge

section OriginalProjectiveBlowupBridge


/-! Direct first-step projective adapter from the original Weierstrass residue
node. The original projective scheme, actual residueNodeMap, actual common
chart and actual R-node are retained throughout the two cartesian squares. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open WeierstrassCurve.CriticalNeighborhood
open WeierstrassCurve.Projective
namespace AlgebraicGeometry.Scheme.PowerNode.ProjectiveNodeBlowup

@[reassoc] lemma commonResidue_projective_triangle
    {R : Type u} [CommRing R] [IsLocalRing R]
    {W : WeierstrassCurve R} {x y : ResidueField R} (M : WeierstrassCurve.CriticalNeighborhood W x
      y)
    (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
    (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x :=
      x) (y := y) ρ) :
    M.commonResiduePoint he ρ hρ ≫ commonToProjective M = residueNodeMap W x y he := by
  rw [commonToProjective, ← Category.assoc, M.residue_original_triangle he ρ hρ,
    residueNodeMap_eq_original he]

end AlgebraicGeometry.Scheme.PowerNode.ProjectiveNodeBlowup

end
end OriginalProjectiveBlowupBridge
