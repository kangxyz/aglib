/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.StageModelCompatibility

/-!
# StageComparisonIso

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberToFinite)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel.ModelActions

universe u

/-- The canonical isomorphism from base change along `r ≫ v` to successive base changes along
`v` and `r` . -/
def comparisonIso {G R S : Scheme.{u}} (r : G ⟶ R) (v : R ⟶ S) (A : Scheme.FiniteEtale S) :
    (baseChange (r ≫ v)).obj A ≅ (baseChange r).obj ((baseChange v).obj A) :=
  ObjectProperty.isoMk _
    (Over.isoMk (pullbackLeftPullbackSndIso A.obj.hom v r).symm
      (pullbackLeftPullbackSndIso_inv_snd_snd _ _ _))

theorem comparisonIso_hom {G R S : Scheme.{u}} (r : G ⟶ R) (v : R ⟶ S) (A : Scheme.FiniteEtale S) :
    (comparisonIso r v A).hom = baseChangeComparison r v A := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [comparisonIso, baseChangeComparison, _root_.AlgebraicGeometry.Scheme.FiniteEtale.forget,
        Category.assoc]
    · simp [comparisonIso, baseChangeComparison, _root_.AlgebraicGeometry.Scheme.FiniteEtale.forget,
        Category.assoc]
  · simp [comparisonIso, baseChangeComparison, _root_.AlgebraicGeometry.Scheme.FiniteEtale.forget]

variable {K : Type u} [Field K] {G R S : PointedScheme K}

/-- The successive-base-change isomorphism after transport along the supplied equality
`e : f = r ≫ v` . -/
def refinementIso (r : G ⟶ R) (v : R ⟶ S) (f : G ⟶ S) (e : f = r ≫ v)
    (A : Scheme.FiniteEtale S.right) :
    (baseChange f.right).obj A ≅ (baseChange r.right).obj ((baseChange v.right).obj A) :=
  eqToIso (congrArg (fun t : G ⟶ S ↦ (baseChange t.right).obj A) e) ≪≫
    comparisonIso r.right v.right A

@[simp] theorem refinementIso_hom (r : G ⟶ R) (v : R ⟶ S) (f : G ⟶ S)
    (e : f = r ≫ v) (A : Scheme.FiniteEtale S.right) :
    (refinementIso r v f e A).hom = refinement r v f e A := by
  simp only [refinementIso, Iso.trans_hom, eqToIso.hom, comparisonIso_hom, refinement]

@[reassoc] theorem refinement_fst_fst (r : G ⟶ R) (v : R ⟶ S) (f : G ⟶ S)
    (e : f = r ≫ v) (A : Scheme.FiniteEtale S.right) :
    (refinement r v f e A).hom.left ≫
      pullback.fst (pullback.snd A.obj.hom v.right) r.right ≫ pullback.fst A.obj.hom v.right =
        pullback.fst A.obj.hom f.right := by
  subst f
  simp [refinement, baseChangeComparison]

end AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel.ModelActions

namespace AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel.StageModel

universe u
variable {K : Type u} [Field K] {B X : Scheme.{u}}
  (b : Spec (CommRingCat.of K) ⟶ B) (p : X ⟶ B)
  (o : B ⟶ X) (ho : o ≫ p = 𝟙 B)
  (M : StageModel b p) (Z : Scheme.FiniteEtale B) (q : Fiber b Z)
  (f : Z ⟶ M.base) (hf : (fiberToFinite b).map f q = M.point)

/-- The isomorphism from `M.obj` to its refined stage model, using the supplied point
compatibility `hf` . -/
def refinementIso : M.obj b p ≅
    (baseChange (geometricStage b p o ho Z q).right).obj
      ((baseChange (stageComparison b p o ho f q M.point hf).right).obj M.cover) :=
  ModelActions.refinementIso (geometricStage b p o ho Z q)
    (stageComparison b p o ho f q M.point hf) (geometricStage b p o ho M.base M.point)
    (geometricStage_comparison b p o ho f q M.point hf).symm M.cover

@[simp] theorem refinementIso_hom :
    (refinementIso b p o ho M Z q f hf).hom = refinementMap b p o ho M Z q f hf :=
  ModelActions.refinementIso_hom _ _ _ _ _

end AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel.StageModel

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 f8ac5dc3c71c49e37c8a0836e237dbd30b3aaac5c7c49fa6b4ff64797068bb5f.
Definitions, hypotheses and universes are retained modulo native names. -/
