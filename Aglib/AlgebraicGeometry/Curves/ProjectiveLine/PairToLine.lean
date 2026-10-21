/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Line.TwoPoints
public import Aglib.AlgebraicGeometry.Curves.Nodal.Polygon.FiniteClosedCover
public import Aglib.AlgebraicGeometry.Curves.Nodal.LineGeometry

/-!
# Ordered points as coordinates on the same glued line

Source: frozen R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
`IntrinsicSplitNode/ResolvedCoordinates.lean`, lines 397–455.
SHA-256: `424932cf8a97432d3030dacda7f9d34b15e99b6b09a00ef681e3d3969bb2681a`.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Polygon Scheme.PinchedLine.ProjectiveComparison
variable (k : Type u) [Field k]

@[reassoc] lemma targetLinePoint_lineIsoP1 (a : k) :
    targetLinePoint k a ≫ (lineIsoP1 k).hom =
      Scheme.PinchedLine.branchMap k a ≫ chart k 0 := by
  change (Scheme.PinchedLine.branchMap k a ≫ selectedLineAffine k) ≫ lineToP1 k = _
  rw [Category.assoc, lineToP1, pushout.inl_desc]

@[reassoc] lemma chartPoint_lineIsoP1_inv (a : k) :
    (Scheme.PinchedLine.branchMap k a ≫ chart k 0) ≫ (lineIsoP1 k).inv =
      targetLinePoint k a := by
  rw [← targetLinePoint_lineIsoP1, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable (s t : Spec (.of k) ⟶ projectiveP1 k)
  (hs : s ≫ structureMap k = 𝟙 _) (ht : t ≫ structureMap k = 𝟙 _) (hne : s ≠ t)

/-- Coordinates followed by the canonical inverse from actual P1 to the
actual target component, both as schemes over the original residue field. -/
def pairToLineOverIso : Over.mk (structureMap k) ≅ Over.mk (Scheme.PinchedLine.lineStructure k) :=
  TwoPoints.normalizePair k s t hs ht hne ≪≫
    (Scheme.PinchedLine.lineIsoP1Over k).symm

/-- The scheme isomorphism from the projective line to the glued line sending the distinct
ordered sections `s` and `t` to the affine points zero and one, respectively. -/
def pairToLineIso : projectiveP1 k ≅ Scheme.PinchedLine.lineGluing k :=
  (Over.forget (Spec (.of k))).mapIso (pairToLineOverIso k s t hs ht hne)

@[reassoc] lemma pairToLineIso_first :
    s ≫ (pairToLineIso k s t hs ht hne).hom = targetLinePoint k 0 := by
  change s ≫ (TwoPoints.normalizePair k s t hs ht hne).hom.left ≫
    (lineIsoP1 k).inv = _
  rw [← Category.assoc, TwoPoints.normalizePair_first]
  exact chartPoint_lineIsoP1_inv k 0

@[reassoc] lemma pairToLineIso_second :
    t ≫ (pairToLineIso k s t hs ht hne).hom = targetLinePoint k 1 := by
  change t ≫ (TwoPoints.normalizePair k s t hs ht hne).hom.left ≫
    (lineIsoP1 k).inv = _
  rw [← Category.assoc, TwoPoints.normalizePair_second]
  exact chartPoint_lineIsoP1_inv k 1

@[reassoc] lemma pairToLineIso_inv_first :
    targetLinePoint k 0 ≫ (pairToLineIso k s t hs ht hne).inv = s := by
  rw [← pairToLineIso_first k s t hs ht hne, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

@[reassoc] lemma pairToLineIso_inv_second :
    targetLinePoint k 1 ≫ (pairToLineIso k s t hs ht hne).inv = t := by
  rw [← pairToLineIso_second k s t hs ht hne, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

@[reassoc] lemma pairToLineIso_over :
    (pairToLineIso k s t hs ht hne).hom ≫ Scheme.PinchedLine.lineStructure k = structureMap k :=
  (pairToLineOverIso k s t hs ht hne).hom.w

@[reassoc] lemma pairToLineIso_inv_over :
    (pairToLineIso k s t hs ht hne).inv ≫ structureMap k = Scheme.PinchedLine.lineStructure k :=
  (pairToLineOverIso k s t hs ht hne).inv.w
end AlgebraicGeometry.Scheme.ProjectiveLine
end
