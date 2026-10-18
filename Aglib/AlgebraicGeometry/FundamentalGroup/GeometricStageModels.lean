/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Functor.ModelAutomorphisms
public import Aglib.AlgebraicGeometry.FundamentalGroup.ModelFiberActions
public import Aglib.AlgebraicGeometry.FundamentalGroup.FiniteStageEmbedding

/-!
# GeometricStageModels

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberToFinite mk)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel

universe u
variable {K : Type u} [Field K] {B X : Scheme.{u}}
  (b : Spec (CommRingCat.of K) ⟶ B) (p : X ⟶ B)
  (o : B ⟶ X) (ho : o ≫ p = 𝟙 B)

/-- The morphism from `X ×[B] Spec K` to the stage `Z ×[B] X` with projections
`pullback.snd p b ≫ q.left` and `pullback.fst p b`. -/
def geometricStageRight (Z : Scheme.FiniteEtale B) (q : Fiber b Z) :
    pullback p b ⟶ ((baseChange p).obj Z).obj.left :=
  pullback.lift (f := Z.obj.hom) (g := p) (pullback.snd p b ≫ q.left) (pullback.fst p b) (by
    rw [Category.assoc, Over.w q]
    exact pullback.condition.symm)

@[reassoc] theorem geometricStageRight_fst (Z : Scheme.FiniteEtale B) (q : Fiber b Z) :
    geometricStageRight b p Z q ≫ pullback.fst Z.obj.hom p = pullback.snd p b ≫ q.left :=
  pullback.lift_fst _ _ _

@[reassoc] theorem geometricStageRight_snd (Z : Scheme.FiniteEtale B) (q : Fiber b Z) :
    geometricStageRight b p Z q ≫ pullback.snd Z.obj.hom p = pullback.fst p b :=
  pullback.lift_snd _ _ _

/-- The pointed morphism underlying `geometricStageRight`, with compatibility at the
chosen origin supplied by `o ≫ p = 𝟙 B`. -/
def geometricStage (Z : Scheme.FiniteEtale B) (q : Fiber b Z) :
    Under.mk (baseChangePoint b p o ho) ⟶ Under.mk (stagePoint b p o ho Z q) :=
  Under.homMk (geometricStageRight b p Z q) (by
    change baseChangePoint b p o ho ≫ geometricStageRight b p Z q =
      (pointedFiberEquiv (pointedProjection b p o ho) Z q).left
    rw [pointedFiberEquiv_left]
    apply pullback.hom_ext (f := Z.obj.hom) (g := p)
    · rw [Category.assoc, geometricStageRight_fst, ← Category.assoc,
        baseChangePoint_snd, Category.id_comp]
      exact (pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, geometricStageRight_snd, baseChangePoint_fst]
      exact (pullback.lift_snd _ _ _).symm)

theorem geometricStage_projection (Z : Scheme.FiniteEtale B) (q : Fiber b Z) :
    geometricStage b p o ho Z q ≫ stagePointedProjection b p o ho Z q =
      pointedInclusion b p o ho := by
  apply Under.UnderMorphism.ext
  exact pullback.lift_snd _ _ _

theorem geometricStage_comparison {Z W : Scheme.FiniteEtale B} (g : Z ⟶ W)
    (q : Fiber b Z) (r : Fiber b W) (hr : (fiberToFinite b).map g q = r) :
    geometricStage b p o ho Z q ≫ stageComparison b p o ho g q r hr =
      geometricStage b p o ho W r := by
  apply Under.UnderMorphism.ext
  change geometricStageRight b p Z q ≫ ((baseChange p).map g).hom.left =
    geometricStageRight b p W r
  apply pullback.hom_ext (f := W.obj.hom) (g := p)
  · rw [Category.assoc, PurelyInseparable.Global.baseChangeMap_fst]
    change (geometricStageRight b p Z q) ≫ (pullback.fst Z.obj.hom p ≫ g.hom.left) =
      geometricStageRight b p W r ≫ pullback.fst W.obj.hom p
    simp only [geometricStageRight, pullback.lift_fst, pullback.lift_fst_assoc, Category.assoc]
    exact congrArg (fun z ↦ pullback.snd p b ≫ z.left) hr
  · rw [Category.assoc, PurelyInseparable.Global.baseChangeMap_snd]
    exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm

/-- A model is an actual finite étale base cover with a selected point and an
actual cover of that finite stage. -/
structure StageModel where
  /-- The finite étale base cover of `B` defining this stage. -/
  base : Scheme.FiniteEtale B
  /-- The selected `K`-valued point of the base cover above `b`. -/
  point : Fiber b base
  /-- The finite étale cover of the stage obtained by pulling the base cover back along `p`. -/
  cover : Scheme.FiniteEtale ((baseChange p).obj base).obj.left

namespace StageModel

/-- The cover of `X ×[B] Spec K` obtained by pulling `M.cover` back along
`geometricStageRight b p M.base M.point`. -/
def obj (M : StageModel b p) : Scheme.FiniteEtale (pullback p b) :=
  (baseChange (geometricStageRight b p M.base M.point)).obj M.cover

/-- The automorphism of the geometric fibre of `M.obj` induced by the stage action
of the projection-kernel element `n`. -/
def component (n : ProjectionKernel b p o ho) (M : StageModel b p) :
    Aut ((fiberToFinite (baseChangePoint b p o ho)).obj (M.obj b p)) :=
  FintypeCat.equivEquivIso (ModelActions.permutation
    (geometricStage b p o ho M.base M.point) (kernelStageAut b p o ho n M.base M.point) M.cover)

end StageModel

variable (hmodels : ∀ Y : Scheme.FiniteEtale (pullback p b), ∃ M : StageModel b p, Nonempty
  (M.obj b p ≅ Y))

include hmodels in
/-- Stage models discharge the actual subobject criterion for the existing
kernel map. The finite-stage object producer is still explicit here. -/
theorem kernelHom_injective_of_stageModels : Function.Injective (kernelHom b p o ho) := by
  intro a c hac
  apply PointedInjection.pointedMap_injective_of_subobjects (pointedInclusion b p o ho) ?_
  · exact congrArg Subtype.val hac
  · intro Y
    obtain ⟨M, ⟨e⟩⟩ := hmodels Y
    exact PointedInjection.exists_subobject_of_finite_etale_model
      ((baseChange p).obj M.base).obj.hom (geometricStageRight b p M.base M.point)
      (pullback.fst p b) (pullback.lift_snd _ _ _) Y M.cover e.symm

variable (n : ProjectionKernel b p o ho)
  (hcompat : ∀ (M N : StageModel b p) (g : M.obj b p ⟶ N.obj b p),
    (fiberToFinite (baseChangePoint b p o ho)).map g ≫ (N.component b p o ho n).hom =
      (M.component b p o ho n).hom ≫ (fiberToFinite (baseChangePoint b p o ho)).map g)

/-- The geometric fibre-functor automorphism extending the stage components of `n`,
using the supplied model-existence hypothesis `hmodels` and arrow compatibility `hcompat`. -/
def kernelAutFromStageModels : BaseChangeGroup b p o ho :=
  CategoryTheory.Functor.ModelAutomorphisms.extendAut (fiberToFinite (baseChangePoint b p o ho))
    (StageModel.obj b p) (StageModel.component b p o ho n) hmodels hcompat

theorem pointedMap_kernelAutFromStageModels (Z : Scheme.FiniteEtale B) (q : Fiber b Z) :
    pointedMap (geometricStage b p o ho Z q) (kernelAutFromStageModels b p o ho hmodels n hcompat) =
      kernelStageAut b p o ho n Z q := by
  apply Aut.ext
  apply NatTrans.ext
  funext A
  apply FintypeCat.hom_ext
  intro z
  rw [pointedMap_apply]
  let M : StageModel b p := ⟨Z, q, A⟩
  have h := CategoryTheory.Functor.ModelAutomorphisms.extendAut_on_model (fiberToFinite
    (baseChangePoint b p o ho))
    (StageModel.obj b p) (StageModel.component b p o ho n) hmodels hcompat M
  change (kernelAutFromStageModels b p o ho hmodels n hcompat).hom.app (M.obj b p) =
    (M.component b p o ho n).hom at h
  change (pointedFiberEquiv (geometricStage b p o ho Z q) A).symm
    ((kernelAutFromStageModels b p o ho hmodels n hcompat).hom.app (M.obj b p)
      (pointedFiberEquiv (geometricStage b p o ho Z q) A z)) = _
  rw [h]
  change (pointedFiberEquiv (geometricStage b p o ho Z q) A).symm
      (ModelActions.action (geometricStage b p o ho Z q)
        (kernelStageAut b p o ho n Z q) A
          (pointedFiberEquiv (geometricStage b p o ho Z q) A z)) = _
  simp only [ModelActions.action, Equiv.symm_apply_apply]

/-- With actual object and arrow model coverage, the constructed inverse
maps to n under the SAME original kernel homomorphism. -/
theorem kernelHom_kernelAutFromStageModels :
    kernelHom b p o ho (kernelAutFromStageModels b p o ho hmodels n hcompat) = n := by
  let Z : Scheme.FiniteEtale B := mk (𝟙 B)
  let q : Fiber b Z := Over.homMk b (Category.comp_id _)
  apply Subtype.ext
  change pointedMap (pointedInclusion b p o ho)
    (kernelAutFromStageModels b p o ho hmodels n hcompat) = n.val
  rw [← geometricStage_projection b p o ho Z q, pointedMap_comp, MonoidHom.comp_apply,
    pointedMap_kernelAutFromStageModels, pointedMap_kernelStageAut]

end AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 8203860165bafa9ab96a573a1405983872cc8ac664f31a07bfa4cb95ae1a6836.
Definitions, hypotheses and universes are retained modulo native names. -/
