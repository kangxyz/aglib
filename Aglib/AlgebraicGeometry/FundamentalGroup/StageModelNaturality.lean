/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.StageFieldNaturality
public import Aglib.CategoryTheory.Functor.NaturalityTransport

/-!
# StageModelNaturality

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberToFinite)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
namespace AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel
universe u
variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
  {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  (p : X ⟶ Spec (CommRingCat.of K)) (o : Spec (CommRingCat.of K) ⟶ X)
  (ho : o ≫ p = 𝟙 _)

/-- Actual common field stages and actual finite-field Hom descent prove
compatibility on every arrow between the geometric models. No choice-independence
or arrow-descent hypothesis is retained. -/
theorem stageModel_components_compatible
    (n : ProjectionKernel (Spec.algebraMap K Ω) p o ho)
    (M N : StageModel (Spec.algebraMap K Ω) p) (γ : M.obj (Spec.algebraMap K Ω) p ⟶ N.obj
      (Spec.algebraMap K Ω) p) :
    (fiberToFinite (baseChangePoint (Spec.algebraMap K Ω) p o ho)).map γ ≫
        (N.component (Spec.algebraMap K Ω) p o ho n).hom =
      (M.component (Spec.algebraMap K Ω) p o ho n).hom ≫
        (fiberToFinite (baseChangePoint (Spec.algebraMap K Ω) p o ho)).map γ := by
  let b := Spec.algebraMap K Ω
  obtain ⟨D⟩ : Nonempty (CommonFiniteSeparableBase K Ω M.base N.base M.point N.point) :=
    ⟨commonFiniteSeparableBase K Ω M.base N.base M.point N.point⟩
  let Z := SeparableStage.finiteSeparableFieldCover K (finiteSepField K Ω D.stage)
  let q := finiteSepPoint K Ω D.stage
  let r := geometricStage b p o ho Z q
  let a := kernelStageAut b p o ho n Z q
  let A := (baseChange (stageComparison b p o ho D.left q M.point D.left_point).right).obj M.cover
  let B := (baseChange (stageComparison b p o ho D.right q N.point D.right_point).right).obj N.cover
  let eM := M.refinementIso b p o ho Z q D.left D.left_point
  let eN := N.refinementIso b p o ho Z q D.right D.right_point
  let γR : (baseChange r.right).obj A ⟶ (baseChange r.right).obj B := eM.inv ≫ γ ≫ eN.hom
  have Hγ : M.refinementMap b p o ho Z q D.left D.left_point ≫ γR =
      γ ≫ N.refinementMap b p o ho Z q D.right D.right_point := by
    rw [← StageModel.refinementIso_hom, ← StageModel.refinementIso_hom]
    exact eM.hom_inv_id_assoc _
  have hnat (z : Fiber (baseChangePoint b p o ho) ((baseChange r.right).obj A)) :
      (fiberToFinite (baseChangePoint b p o ho)).map γR (ModelActions.action r a A z) =
        ModelActions.action r a B ((fiberToFinite (baseChangePoint b p o ho)).map γR z) := by
    let := finiteSepOmegaAlgebra K Ω D.stage
    let := finiteSepOmegaTower K Ω D.stage
    let := finiteSepOmegaIsAlgebraic K Ω D.stage
    have hq : towerPoint K (finiteSepField K Ω D.stage) Ω = q :=
      Over.OverMorphism.ext (finiteSepPoint_left K Ω D.stage).symm
    have H := fieldStage_action_naturality K (finiteSepField K Ω D.stage) Ω p o ho n A B
    rw [hq] at H
    exact H γR z
  let F := fiberToFinite (baseChangePoint b p o ho)
  let i := M.refinementMap b p o ho Z q D.left D.left_point
  let j := N.refinementMap b p o ho Z q D.right D.right_point
  apply FintypeCat.hom_ext
  intro z
  change ModelActions.action (geometricStage b p o ho N.base N.point)
      (kernelStageAut b p o ho n N.base N.point) N.cover (F.map γ z) =
    F.map γ (ModelActions.action (geometricStage b p o ho M.base M.point)
      (kernelStageAut b p o ho n M.base M.point) M.cover z)
  symm
  exact CategoryTheory.Functor.NaturalityTransport.naturality_via_injective (F.map i) (F.map j)
    (N.refinement_fiber_injective b p o ho Z q D.right D.right_point)
    (F.map γ) (F.map γR)
    (ModelActions.action (geometricStage b p o ho M.base M.point)
      (kernelStageAut b p o ho n M.base M.point) M.cover)
    (ModelActions.action r a A)
    (ModelActions.action (geometricStage b p o ho N.base N.point)
      (kernelStageAut b p o ho n N.base N.point) N.cover)
    (ModelActions.action r a B)
    (CategoryTheory.Functor.NaturalityTransport.functor_square_apply F i j γ γR Hγ)
    (M.refinement_action b p o ho Z q D.left D.left_point n)
    (N.refinement_action b p o ho Z q D.right D.right_point n) hnat z

end AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 10fc5fb9c7db7e9e6136345102fab628ba80d722551c2b3d58124d3ffb6d5890.
Definitions, hypotheses and universes are retained modulo native names. -/
