/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.FiniteEtalePointLift

/-!
# Actual finite-stage lifts of arithmetic kernel automorphisms

An element of the original projection kernel fixes the selected point in
every finite étale base cover. Restricting it to that selected component
constructs the existing fibre automorphism group at the finite stage.
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

/-- The point of the cover pulled back along `p` corresponding to `q` over the section `o`. -/
def stageCoverPoint (Z : Scheme.FiniteEtale B) (q : Fiber b Z) : Fiber (b ≫ o)
    ((baseChange p).obj Z) :=
  pointedFiberEquiv (pointedProjection b p o ho) Z q

/-- The scheme morphism underlying `stageCoverPoint` on the cover pulled back along `p`. -/
def stagePoint (Z : Scheme.FiniteEtale B) (q : Fiber b Z) :
    Spec (CommRingCat.of K) ⟶ ((baseChange p).obj Z).obj.left :=
  (stageCoverPoint b p o ho Z q).left

/-- The pointed structure morphism from the selected finite stage to the point `b ≫ o`. -/
def stagePointedProjection (Z : Scheme.FiniteEtale B) (q : Fiber b Z) :
    Under.mk (stagePoint b p o ho Z q) ⟶ Under.mk (b ≫ o) :=
  Under.homMk ((baseChange p).obj Z).obj.hom (Over.w (stageCoverPoint b p o ho Z q))

/-- The actual projection-kernel equation forces actual component preservation. -/
theorem kernel_fixes_stagePoint (n : ProjectionKernel b p o ho) (Z : Scheme.FiniteEtale B)
    (q : Fiber b Z) :
    (n : FiberAutGroup (b ≫ o)).hom.app ((baseChange p).obj Z)
      (stageCoverPoint b p o ho Z q) = stageCoverPoint b p o ho Z q := by
  have hn := congrArg (fun a : FiberAutGroup b ↦ a.hom.app Z q) n.property
  change (pointedMap (pointedProjection b p o ho) n.val).hom.app Z q = q at hn
  rw [pointedMap_apply] at hn
  apply (pointedFiberEquiv (pointedProjection b p o ho) Z).symm.injective
  exact hn.trans ((pointedFiberEquiv (pointedProjection b p o ho) Z).symm_apply_apply q).symm

/-- The kernel element restricted to the chosen real finite étale base stage. -/
def kernelStageAut (n : ProjectionKernel b p o ho) (Z : Scheme.FiniteEtale B) (q : Fiber b Z) :
    FiberAutGroup (stagePoint b p o ho Z q) :=
  PointLift.pointedLiftAut ((baseChange p).obj Z).obj.hom (stagePoint b p o ho Z q)
    (b ≫ o) (Over.w (stageCoverPoint b p o ho Z q)) n.val
    (kernel_fixes_stagePoint b p o ho n Z q)

-- Keep this original typed fibre/point simp formula before carrier or functor normalization.
@[simp, nolint simpNF] theorem pointedMap_kernelStageAut (n : ProjectionKernel b p o ho)
    (Z : Scheme.FiniteEtale B) (q : Fiber b Z) :
    pointedMap (stagePointedProjection b p o ho Z q) (kernelStageAut b p o ho n Z q) = n.val :=
  PointLift.pointedMap_pointedLiftAut ((baseChange p).obj Z).obj.hom
    (stagePoint b p o ho Z q) (b ≫ o) (Over.w (stageCoverPoint b p o ho Z q)) n.val
    (kernel_fixes_stagePoint b p o ho n Z q)

theorem stagePointedProjection_injective (Z : Scheme.FiniteEtale B) (q : Fiber b Z) :
    Function.Injective (pointedMap (stagePointedProjection b p o ho Z q)) :=
  PointLift.pointedMap_injective ((baseChange p).obj Z).obj.hom
    (stagePoint b p o ho Z q) (b ≫ o) (Over.w (stageCoverPoint b p o ho Z q))

/-- Any actual comparison of pointed finite stages forces compatibility of
the constructed natural automorphisms. -/
theorem kernelStageAut_compatible (n : ProjectionKernel b p o ho)
    (Z W : Scheme.FiniteEtale B) (q : Fiber b Z) (r : Fiber b W)
    (v : Under.mk (stagePoint b p o ho Z q) ⟶ Under.mk (stagePoint b p o ho W r))
    (hv : v ≫ stagePointedProjection b p o ho W r = stagePointedProjection b p o ho Z q) :
    pointedMap v (kernelStageAut b p o ho n Z q) = kernelStageAut b p o ho n W r := by
  apply stagePointedProjection_injective b p o ho W r
  rw [pointedMap_kernelStageAut, ← MonoidHom.comp_apply, ← pointedMap_comp, hv,
    pointedMap_kernelStageAut]

theorem stageCoverPoint_naturality {Z W : Scheme.FiniteEtale B} (g : Z ⟶ W) (q : Fiber b Z) :
    (fiberToFinite (b ≫ o)).map ((baseChange p).map g) (stageCoverPoint b p o ho Z q) =
      stageCoverPoint b p o ho W ((fiberToFinite b).map g q) := by
  have h := ConcreteCategory.congr_hom
    ((pointedFiberIso (pointedProjection b p o ho)).hom.naturality g) q
  exact h.symm

/-- The pointed morphism between pulled-back stages induced by `g`, using the equation sending
`q` to `r`. -/
def stageComparison {Z W : Scheme.FiniteEtale B} (g : Z ⟶ W) (q : Fiber b Z) (r : Fiber b W)
    (hr : (fiberToFinite b).map g q = r) :
    Under.mk (stagePoint b p o ho Z q) ⟶ Under.mk (stagePoint b p o ho W r) :=
  Under.homMk ((baseChange p).map g).hom.left (by
    have he := stageCoverPoint_naturality b p o ho g q
    rw [hr] at he
    exact congrArg (fun z ↦ z.left) he)

theorem stageComparison_fac {Z W : Scheme.FiniteEtale B} (g : Z ⟶ W) (q : Fiber b Z) (r : Fiber b W)
    (hr : (fiberToFinite b).map g q = r) :
    stageComparison b p o ho g q r hr ≫ stagePointedProjection b p o ho W r =
      stagePointedProjection b p o ho Z q :=
  Under.UnderMorphism.ext (Over.w ((baseChange p).map g).hom)

/-- Actual base-cover arrows yield compatible finite-stage actions. -/
theorem kernelStageAut_naturality (n : ProjectionKernel b p o ho)
    {Z W : Scheme.FiniteEtale B} (g : Z ⟶ W) (q : Fiber b Z) (r : Fiber b W)
    (hr : (fiberToFinite b).map g q = r) :
    pointedMap (stageComparison b p o ho g q r hr) (kernelStageAut b p o ho n Z q) =
      kernelStageAut b p o ho n W r :=
  kernelStageAut_compatible b p o ho n Z W q r _ (stageComparison_fac b p o ho g q r hr)

end AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 d93a15caa0970621cf8aeaabd16acb50243c6893391a566e1edceb63e2093ef0.
Definitions, hypotheses and universes are retained modulo native names. -/
