/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.CriticalCubic.InfinityCharts
public import Aglib.AlgebraicGeometry.Curves.Nodal.Projective

/-!
# The projective split critical cubic as a pinching

The two explicit affine charts descend to an isomorphism between the
actual critical cubic and the pinched line. The normalization map, branch
sections, infinity section, and original-field structures satisfy exact triangles.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Polynomial
universe u

namespace WeierstrassCurve.CriticalCubic.ProjectivePinching

open WeierstrassCurve.Projective CriticalCubic.AdaptedInfinity
variable (k : Type u) [Field k] (a b r s : k) (hrs : r ≠ s)
    (hr : r ^ 2 + a * r - b = 0) (hs : s ^ 2 + a * s - b = 0)
local notation "W" => CriticalCubic.equation k a b

/-- Descent of the two specified chart maps to the actual original Proj. -/
def pinchedToCritical : Scheme.PinchedLine.pinchedGluing k ⟶ scheme W :=
  pushout.desc (nodeChart k a b r s hrs hr hs) (infinityChart k a b r s hrs hr hs)
    (overlap_compatibility k a b r s hrs hr hs)

@[reassoc, simp] lemma pinchedToCritical_node :
    pushout.inl (Scheme.PinchedLine.gluingToNode k) (Scheme.PinchedLine.gluingToInfinity k) ≫
      pinchedToCritical k a b r s hrs hr hs = nodeChart k a b r s hrs hr hs :=
  pushout.inl_desc _ _ _

@[reassoc, simp] lemma pinchedToCritical_infinity :
    pushout.inr (Scheme.PinchedLine.gluingToNode k) (Scheme.PinchedLine.gluingToInfinity k) ≫
      pinchedToCritical k a b r s hrs hr hs = infinityChart k a b r s hrs hr hs :=
  pushout.inr_desc _ _ _

/-- For the supplied distinct tangent roots, the descended pinched-line comparison is an
isomorphism. -/
instance pinchedToCritical_isIso : IsIso (pinchedToCritical k a b r s hrs hr hs) := by
  apply Scheme.OpenPushoutIso.desc_isIso
    (Scheme.PinchedLine.gluingToNode k) (Scheme.PinchedLine.gluingToInfinity k)
    (nodeChart k a b r s hrs hr hs) (infinityChart k a b r s hrs hr hs)
    (overlap_compatibility k a b r s hrs hr hs)
    (nodeChart_full_overlap k a b r s hrs hr hs)
  intro z
  have hz : z ∈ (nodeChart k a b r s hrs hr hs).opensRange ⊔
      (infinityChart k a b r s hrs hr hs).opensRange := by
    rw [node_infinity_cover]
    trivial
  exact hz

/-- The isomorphism has the proved descent as its actual forward map. -/
def pinchedIsoCritical : Scheme.PinchedLine.pinchedGluing k ≅ scheme W :=
  asIso (pinchedToCritical k a b r s hrs hr hs)

/-- The actual critical cubic, identified with the permanent pinched curve. -/
def criticalIsoPinched : scheme W ≅ Scheme.PinchedLine.pinchedGluing k :=
  (pinchedIsoCritical k a b r s hrs hr hs).symm

@[reassoc] lemma pinchedToCritical_over :
    pinchedToCritical k a b r s hrs hr hs ≫ structureMap W =
      Scheme.PinchedLine.pinchedStructure k := by
  apply pushout.hom_ext
  · rw [← Category.assoc, pinchedToCritical_node, nodeChart_structure,
      Scheme.PinchedLine.pinchedStructure, pushout.inl_desc]
  · rw [← Category.assoc, pinchedToCritical_infinity, infinityChart_structure,
      Scheme.PinchedLine.pinchedStructure, pushout.inr_desc]

/-- The same actual isomorphism, with both original field structures retained. -/
def pinchedIsoCriticalOver :
    Over.mk (Scheme.PinchedLine.pinchedStructure k) ≅ Over.mk (structureMap W) :=
  Over.isoMk (pinchedIsoCritical k a b r s hrs hr hs)
    (pinchedToCritical_over k a b r s hrs hr hs)

/-- Original-field direction from the actual critical cubic to the permanent pinching. -/
def criticalIsoPinchedOver :
    Over.mk (structureMap W) ≅ Over.mk (Scheme.PinchedLine.pinchedStructure k) :=
  (pinchedIsoCriticalOver k a b r s hrs hr hs).symm

/-- Actual affine normalization with the explicit parameter t=r+(s-r)u. -/
def lineAffineToCritical : Scheme.PinchedLine.normalizationScheme k ⟶ scheme W :=
  (CriticalCubic.parameterAffineSchemeIso k r s hrs).hom ≫
    CriticalCubic.affineNormalization k a b ≫ affineChart W

@[reassoc] lemma normalization_nodeChart :
    Scheme.PinchedLine.normalizationMap k ≫ nodeChart k a b r s hrs hr hs =
      lineAffineToCritical k a b r s hrs := by
  rw [nodeChart, ← Category.assoc, CriticalCubic.coordinateNodeSchemeIso_normalization,
    Category.assoc]
  rfl

/-- Compatibility on the actual conductor localization, not a smaller open. -/
lemma lineCharts_compatibility :
    Scheme.PinchedLine.normalizationOverlapInclusion k ≫ lineAffineToCritical k a b r s hrs =
      Scheme.PinchedLine.gluingToInfinity k ≫ infinityChart k a b r s hrs hr hs := by
  rw [← normalization_nodeChart k a b r s hrs hr hs, ← Category.assoc,
    ← Scheme.PinchedLine.conductorOpenIso_over]
  exact overlap_compatibility k a b r s hrs hr hs

/-- The actual map from the permanent normalized line gluing to the critical cubic. -/
def lineToCritical : Scheme.PinchedLine.lineGluing k ⟶ scheme W :=
  pushout.desc (lineAffineToCritical k a b r s hrs)
    (infinityChart k a b r s hrs hr hs) (lineCharts_compatibility k a b r s hrs hr hs)

@[reassoc, simp] lemma lineToCritical_affine :
    pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k) ≫
      lineToCritical k a b r s hrs hr hs = lineAffineToCritical k a b r s hrs :=
  pushout.inl_desc _ _ _

@[reassoc, simp] lemma lineToCritical_infinity :
    pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
      (Scheme.PinchedLine.gluingToInfinity k) ≫
      lineToCritical k a b r s hrs hr hs = infinityChart k a b r s hrs hr hs :=
  pushout.inr_desc _ _ _

/-- Global compatibility with the existing normalization map, proved on both charts. -/
@[reassoc] theorem normalization_triangle :
    Scheme.PinchedLine.gluedNormalizationMap k ≫ pinchedToCritical k a b r s hrs hr hs =
      lineToCritical k a b r s hrs hr hs := by
  apply pushout.hom_ext
  · rw [← Category.assoc, Scheme.PinchedLine.gluedNormalizationMap_affine, Category.assoc,
      pinchedToCritical_node, lineToCritical_affine]
    exact normalization_nodeChart k a b r s hrs hr hs
  · rw [← Category.assoc, Scheme.PinchedLine.gluedNormalizationMap_infinity,
      pinchedToCritical_infinity, lineToCritical_infinity]

@[reassoc] lemma lineToCritical_over :
    lineToCritical k a b r s hrs hr hs ≫ structureMap W = Scheme.PinchedLine.lineStructure k := by
  rw [← normalization_triangle, Category.assoc, pinchedToCritical_over,
    Scheme.PinchedLine.gluedNormalizationMap_over]

/-- The standardized zero branch is the actual original singular origin section. -/
@[reassoc] theorem lineToCritical_branch_zero :
    (Scheme.PinchedLine.branchMap k 0 ≫
      pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
        (Scheme.PinchedLine.gluingToInfinity k)) ≫
        lineToCritical k a b r s hrs hr hs =
      CriticalCubic.originSection k a b ≫ affineChart W := by
  rw [Category.assoc, lineToCritical_affine, ← normalization_nodeChart k a b r s hrs hr hs]
  simpa only [nodeChart, Category.assoc] using
    congrArg (fun f => f ≫ affineChart W)
      (CriticalCubic.coordinateNodeSchemeIso_origin_zero k a b r s hrs hr hs)

/-- The standardized one branch has the same original scheme-valued origin triangle. -/
@[reassoc] theorem lineToCritical_branch_one :
    (Scheme.PinchedLine.branchMap k 1 ≫
      pushout.inl (Scheme.PinchedLine.normalizationOverlapInclusion k)
        (Scheme.PinchedLine.gluingToInfinity k)) ≫
        lineToCritical k a b r s hrs hr hs =
      CriticalCubic.originSection k a b ≫ affineChart W := by
  rw [Category.assoc, lineToCritical_affine, ← normalization_nodeChart k a b r s hrs hr hs]
  simpa only [nodeChart, Category.assoc] using
    congrArg (fun f => f ≫ affineChart W)
      (CriticalCubic.coordinateNodeSchemeIso_origin_one k a b r s hrs hr hs)

/-- The original infinity section is retained as a morphism, not only as a point. -/
@[reassoc] theorem lineToCritical_infinity_section :
    (Spec.map (CommRingCat.ofHom (standardOrigin k)) ≫
      pushout.inr (Scheme.PinchedLine.normalizationOverlapInclusion k)
        (Scheme.PinchedLine.gluingToInfinity k)) ≫
        lineToCritical k a b r s hrs hr hs = infinitySection W := by
  rw [Category.assoc, lineToCritical_infinity, infinityChart_origin]

/-- The same infinity section on the pinched curve. -/
@[reassoc] theorem pinchedToCritical_infinity_section :
    (Spec.map (CommRingCat.ofHom (standardOrigin k)) ≫
      pushout.inr (Scheme.PinchedLine.gluingToNode k) (Scheme.PinchedLine.gluingToInfinity k)) ≫
        pinchedToCritical k a b r s hrs hr hs = infinitySection W := by
  rw [Category.assoc, pinchedToCritical_infinity, infinityChart_origin]

/-- The same actual normalization with source the permanent literal projective line. -/
def projectiveNormalization : Scheme.ProjectiveLine.projectiveP1 k ⟶ scheme W :=
  (Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 k).inv ≫ lineToCritical k a b r s hrs hr hs

@[reassoc] lemma projectiveNormalization_over :
    projectiveNormalization k a b r s hrs hr hs ≫ structureMap W =
      Scheme.ProjectiveLine.structureMap k := by
  rw [projectiveNormalization, Category.assoc, lineToCritical_over,
    ← Scheme.PinchedLine.ProjectiveComparison.lineIsoP1_over, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- The projective-line normalization is exactly the old glued normalization
followed by the newly proved actual cubic isomorphism. -/
@[reassoc] theorem projectiveNormalization_triangle :
    ((Scheme.PinchedLine.ProjectiveComparison.lineIsoP1 k).inv ≫
      Scheme.PinchedLine.gluedNormalizationMap k) ≫
      pinchedToCritical k a b r s hrs hr hs = projectiveNormalization k a b r s hrs hr hs := by
  rw [Category.assoc, normalization_triangle]
  rfl
end WeierstrassCurve.CriticalCubic.ProjectivePinching

/- Migration source: LocalModels/CriticalCubic/ProjectivePinching.lean.
Frozen R5 packet f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 8b9f964301825acd6febbeff1f386c344455da3743b923c31859010883506963.
Pointed-resolution assembly remains outside this module. -/
