/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.GeometricStageModels

/-!
# StageModelCompatibility

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

namespace AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel

universe u
variable {K : Type u} [Field K] {B X : Scheme.{u}}
  (b : Spec (CommRingCat.of K) ⟶ B) (p : X ⟶ B)
  (o : B ⟶ X) (ho : o ≫ p = 𝟙 B)

namespace ModelActions

theorem action_eqToHom {G S : PointedScheme K} (f f' : G ⟶ S) (h : f = f')
    (a : FiberAutGroup S.hom) (A : Scheme.FiniteEtale S.right)
      (z : Fiber G.hom ((baseChange f.right).obj A)) :
    (fiberToFinite G.hom).map (eqToHom (congrArg (fun q ↦ (baseChange q.right).obj A) h))
        (action f a A z) =
      action f' a A ((fiberToFinite G.hom).map
        (eqToHom (congrArg (fun q ↦ (baseChange q.right).obj A) h)) z) := by
  subst f'
  simp only [eqToHom_refl]
  change action f a A z ≫ 𝟙 _ = action f a A (z ≫ 𝟙 _)
  rw [Category.comp_id, Category.comp_id]

/-- The comparison from pullback along `f` to iterated pullback along `v` and `r`,
transported through the specified equation `e : f = r ≫ v`. -/
def refinement {G R S : PointedScheme K} (r : G ⟶ R) (v : R ⟶ S)
    (f : G ⟶ S) (e : f = r ≫ v) (A : Scheme.FiniteEtale S.right) :
    (baseChange f.right).obj A ⟶ (baseChange r.right).obj ((baseChange v.right).obj A) :=
  eqToHom (congrArg (fun t : G ⟶ S ↦ (baseChange t.right).obj A) e) ≫
    baseChangeComparison r.right v.right A

theorem refinement_injective {G R S : PointedScheme K} (r : G ⟶ R) (v : R ⟶ S)
    (f : G ⟶ S) (e : f = r ≫ v) (A : Scheme.FiniteEtale S.right) :
    Function.Injective ((fiberToFinite G.hom).map (refinement r v f e A)) := by
  subst f
  simp only [refinement, eqToHom_refl, Category.id_comp]
  exact comparison_fiber_injective r v A

theorem refinement_action {G R S : PointedScheme K} (r : G ⟶ R) (v : R ⟶ S)
    (f : G ⟶ S) (e : f = r ≫ v) (aR : FiberAutGroup R.hom) (aS : FiberAutGroup S.hom)
    (ha : pointedMap v aR = aS) (A : Scheme.FiniteEtale S.right)
      (z : Fiber G.hom ((baseChange f.right).obj A)) :
    (fiberToFinite G.hom).map (refinement r v f e A) (action f aS A z) =
      action r aR ((baseChange v.right).obj A)
        ((fiberToFinite G.hom).map (refinement r v f e A) z) := by
  subst f
  subst aS
  simp only [refinement, eqToHom_refl, Category.id_comp]
  exact action_refinement r v aR A z

end ModelActions

namespace StageModel

variable (M : StageModel b p) (Z : Scheme.FiniteEtale B) (q : Fiber b Z)
  (f : Z ⟶ M.base) (hf : (fiberToFinite b).map f q = M.point)

/-- The refinement morphism from `M.obj` to the cover pulled back through the stage
`(Z, q)`, using `f` and its point-preservation equation `hf`. -/
def refinementMap : M.obj b p ⟶
    (baseChange (geometricStage b p o ho Z q).right).obj
      ((baseChange (stageComparison b p o ho f q M.point hf).right).obj M.cover) :=
  ModelActions.refinement (geometricStage b p o ho Z q)
    (stageComparison b p o ho f q M.point hf) (geometricStage b p o ho M.base M.point)
    (geometricStage_comparison b p o ho f q M.point hf).symm M.cover

theorem refinement_fiber_injective :
    Function.Injective ((fiberToFinite (baseChangePoint b p o ho)).map
      (refinementMap b p o ho M Z q f hf)) :=
  ModelActions.refinement_injective (geometricStage b p o ho Z q)
    (stageComparison b p o ho f q M.point hf) (geometricStage b p o ho M.base M.point)
    (geometricStage_comparison b p o ho f q M.point hf).symm M.cover

theorem refinement_action (n : ProjectionKernel b p o ho) (z : Fiber (baseChangePoint b p o ho)
  (M.obj b p)) :
    (fiberToFinite (baseChangePoint b p o ho)).map (refinementMap b p o ho M Z q f hf)
        (ModelActions.action (geometricStage b p o ho M.base M.point)
          (kernelStageAut b p o ho n M.base M.point) M.cover z) =
      ModelActions.action (geometricStage b p o ho Z q) (kernelStageAut b p o ho n Z q)
        ((baseChange (stageComparison b p o ho f q M.point hf).right).obj M.cover)
        ((fiberToFinite (baseChangePoint b p o ho)).map (refinementMap b p o ho M Z q f hf) z) :=
  ModelActions.refinement_action (geometricStage b p o ho Z q)
    (stageComparison b p o ho f q M.point hf) (geometricStage b p o ho M.base M.point)
    (geometricStage_comparison b p o ho f q M.point hf).symm
    (kernelStageAut b p o ho n Z q) (kernelStageAut b p o ho n M.base M.point)
    (kernelStageAut_naturality b p o ho n f q M.point hf) M.cover z

end StageModel

/-- This witness consists entirely of actual finite base covers and actual
arrows, including the displayed geometric pullback equation. -/
structure CommonStageArrow (M N : StageModel b p) (γ : M.obj b p ⟶ N.obj b p) where
  /-- The common finite étale base cover refining both stage models. -/
  base : Scheme.FiniteEtale B
  /-- The selected point of the common base cover over `b`. -/
  point : Fiber b base
  /-- The morphism from the common base cover to `M.base`, preserving the selected point
  by `left_point`. -/
  left : base ⟶ M.base
  left_point : (fiberToFinite b).map left point = M.point
  /-- The morphism from the common base cover to `N.base`, preserving the selected point
  by `right_point`. -/
  right : base ⟶ N.base
  right_point : (fiberToFinite b).map right point = N.point
  /-- The morphism between the two covers pulled back to the common stage, whose further
  geometric pullback agrees with `γ` by `baseChange_arrow`. -/
  arrow :
    (baseChange (stageComparison b p o ho left point M.point left_point).right).obj M.cover ⟶
      (baseChange (stageComparison b p o ho right point N.point right_point).right).obj N.cover
  baseChange_arrow :
    M.refinementMap b p o ho base point left left_point ≫
        (baseChange (geometricStage b p o ho base point).right).map arrow =
      γ ≫ N.refinementMap b p o ho base point right right_point

private theorem commutes_of_refinements {A A' B B' : Type u}
    (i : A → A') (j : B → B') (hj : Function.Injective j) (f : A → B) (g : A' → B')
    (a : A → A) (a' : A' → A') (b : B → B) (b' : B' → B')
    (hsq : ∀ x, j (f x) = g (i x)) (hi : ∀ x, i (a x) = a' (i x))
    (hja : ∀ y, j (b y) = b' (j y)) (hg : ∀ x, g (a' x) = b' (g x)) (x : A) :
    f (a x) = b (f x) := by
  apply hj
  calc
    j (f (a x)) = g (i (a x)) := hsq _
    _ = g (a' (i x)) := congrArg g (hi x)
    _ = b' (g (i x)) := hg _
    _ = b' (j (f x)) := congrArg b' (hsq x).symm
    _ = j (b (f x)) := (hja _).symm

theorem components_compatible_of_commonStage (n : ProjectionKernel b p o ho)
    (M N : StageModel b p) (γ : M.obj b p ⟶ N.obj b p)
    (D : CommonStageArrow b p o ho M N γ) :
    (fiberToFinite (baseChangePoint b p o ho)).map γ ≫ (N.component b p o ho n).hom =
      (M.component b p o ho n).hom ≫ (fiberToFinite (baseChangePoint b p o ho)).map γ := by
  apply FintypeCat.hom_ext
  intro z
  let r := geometricStage b p o ho D.base D.point
  let a := kernelStageAut b p o ho n D.base D.point
  let i := (fiberToFinite (baseChangePoint b p o ho)).map
    (M.refinementMap b p o ho D.base D.point D.left D.left_point)
  let j := (fiberToFinite (baseChangePoint b p o ho)).map
    (N.refinementMap b p o ho D.base D.point D.right D.right_point)
  let g := (fiberToFinite (baseChangePoint b p o ho)).map ((baseChange r.right).map D.arrow)
  have H (x : Fiber (baseChangePoint b p o ho) (M.obj b p)) :
      j ((fiberToFinite (baseChangePoint b p o ho)).map γ x) = g (i x) := by
    have he := congrArg (fiberToFinite (baseChangePoint b p o ho)).map D.baseChange_arrow
    rw [Functor.map_comp, Functor.map_comp] at he
    have hx := ConcreteCategory.congr_hom he x
    exact hx.symm
  change ModelActions.action (geometricStage b p o ho N.base N.point)
      (kernelStageAut b p o ho n N.base N.point) N.cover
      ((fiberToFinite (baseChangePoint b p o ho)).map γ z) =
    (fiberToFinite (baseChangePoint b p o ho)).map γ
      (ModelActions.action (geometricStage b p o ho M.base M.point)
        (kernelStageAut b p o ho n M.base M.point) M.cover z)
  symm
  exact commutes_of_refinements i j
    (N.refinement_fiber_injective b p o ho D.base D.point D.right D.right_point)
    ((fiberToFinite (baseChangePoint b p o ho)).map γ) g
    (ModelActions.action (geometricStage b p o ho M.base M.point)
      (kernelStageAut b p o ho n M.base M.point) M.cover)
    (ModelActions.action r a
      ((baseChange (stageComparison b p o ho D.left D.point M.point D.left_point).right).obj
        M.cover))
    (ModelActions.action (geometricStage b p o ho N.base N.point)
      (kernelStageAut b p o ho n N.base N.point) N.cover)
    (ModelActions.action r a
      ((baseChange (stageComparison b p o ho D.right D.point N.point D.right_point).right).obj
        N.cover))
    H (M.refinement_action b p o ho D.base D.point D.left D.left_point n)
    (N.refinement_action b p o ho D.base D.point D.right D.right_point n)
    (ModelActions.action_naturality r a D.arrow) z

end AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 cd0199b0330512dcbf6119770d53c664e004013f5ae07c80db6bb2405375fb34.
Definitions, hypotheses and universes are retained modulo native names. -/
