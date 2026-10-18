/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.SeparableFieldHom
public import Aglib.AlgebraicGeometry.FundamentalGroup.RefinedAction

/-!
# PointedFieldAction

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

namespace AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel.PointedField

universe u
variable {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]
  {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of K))
  (x : Spec (CommRingCat.of Ω) ⟶ X) (hx : x ≫ p = Spec.algebraMap K Ω)

/-- The pointed morphism induced by `p` and the compatibility equation `hx`. -/
abbrev projection : Under.mk x ⟶ Under.mk (Spec.algebraMap K Ω) := Under.homMk p hx

/-- The point of the base change determined by `x` and the identity of `Spec Ω`. -/
def geometricPoint : Spec (CommRingCat.of Ω) ⟶ pullback p (Spec.algebraMap K Ω) :=
  pullback.lift x (𝟙 _) (by simpa using hx)

/-- The pointed projection from the geometric base change to `X`. -/
def inclusion : Under.mk (geometricPoint p x hx) ⟶ Under.mk x :=
  Under.homMk (pullback.fst p (Spec.algebraMap K Ω)) (pullback.lift_fst _ _ _)

/-- The point on the base-changed finite stage corresponding to `q` under `pointedFiberEquiv`. -/
def stagePoint (Z : Scheme.FiniteEtale (Spec (CommRingCat.of K)))
    (q : Fiber (Spec.algebraMap K Ω) Z) :=
  (pointedFiberEquiv (projection p x hx) Z q).left

/-- The pointed structure morphism from the base-changed finite stage to `x`. -/
def stageProjection (Z : Scheme.FiniteEtale (Spec (CommRingCat.of K)))
    (q : Fiber (Spec.algebraMap K Ω) Z) :
    Under.mk (stagePoint p x hx Z q) ⟶ Under.mk x :=
  Under.homMk ((baseChange p).obj Z).obj.hom (Over.w (pointedFiberEquiv (projection p x hx) Z q))

/-- The pointed morphism from the geometric base change to the finite stage selected by `q`. -/
def stageInclusion (Z : Scheme.FiniteEtale (Spec (CommRingCat.of K)))
    (q : Fiber (Spec.algebraMap K Ω) Z) :
    Under.mk (geometricPoint p x hx) ⟶ Under.mk (stagePoint p x hx Z q) :=
  Under.homMk (geometricStageRight (Spec.algebraMap K Ω) p Z q) (by
    rw [stagePoint, pointedFiberEquiv_left]
    apply pullback.hom_ext
    · simp [geometricPoint, geometricStageRight, _root_.AlgebraicGeometry.Scheme.FiniteEtale.forget,
        Category.assoc]
    · simp [geometricPoint, geometricStageRight, _root_.AlgebraicGeometry.Scheme.FiniteEtale.forget,
        Category.assoc])

theorem inclusion_factor (Z : Scheme.FiniteEtale (Spec (CommRingCat.of K)))
    (q : Fiber (Spec.algebraMap K Ω) Z) :
    stageInclusion p x hx Z q ≫ stageProjection p x hx Z q = inclusion p x hx :=
  Under.UnderMorphism.ext (pullback.lift_snd _ _ _)

variable (a : FiberAutGroup x) (ha : pointedMap (projection p x hx) a = 1)

include ha in
theorem fixes_stage (Z : Scheme.FiniteEtale (Spec (CommRingCat.of K)))
    (q : Fiber (Spec.algebraMap K Ω) Z) :
    a.hom.app ((baseChange p).obj Z) (pointedFiberEquiv (projection p x hx) Z q) =
      pointedFiberEquiv (projection p x hx) Z q := by
  have hh := congrArg (fun t : FiberAutGroup (Spec.algebraMap K Ω) ↦ t.hom.app Z q) ha
  change (pointedMap (projection p x hx) a).hom.app Z q = q at hh
  rw [pointedMap_apply (projection p x hx) a Z q] at hh
  apply (pointedFiberEquiv (projection p x hx) Z).symm.injective
  exact hh.trans ((pointedFiberEquiv (projection p x hx) Z).symm_apply_apply q).symm

/-- The lift of `a` to the finite-stage fiber automorphism group, using the kernel equation
`ha`. -/
def stageAut (Z : Scheme.FiniteEtale (Spec (CommRingCat.of K)))
    (q : Fiber (Spec.algebraMap K Ω) Z) :
    FiberAutGroup (stagePoint p x hx Z q) :=
  PointLift.pointedLiftAut ((baseChange p).obj Z).obj.hom (stagePoint p x hx Z q) x
    (Over.w (pointedFiberEquiv (projection p x hx) Z q)) a (fixes_stage p x hx a ha Z q)

theorem map_stageAut (Z : Scheme.FiniteEtale (Spec (CommRingCat.of K)))
    (q : Fiber (Spec.algebraMap K Ω) Z) :
    pointedMap (stageProjection p x hx Z q) (stageAut p x hx a ha Z q) = a :=
  PointLift.pointedMap_pointedLiftAut _ _ _ _ _ _

variable [Algebra.IsAlgebraic K Ω]

/-- The canonical two-pullback comparison used by field-Hom descent is the
inverse of the pointed refinement comparison. -/
theorem refinement_separable (s : Finset Ω) (U : Scheme.FiniteEtale X) :
    (ModelActions.refinementIso
      (stageInclusion p x hx (SeparableStage.finiteSeparableFieldCover K (finiteSepField K Ω s))
        (finiteSepPoint K Ω s))
      (stageProjection p x hx (SeparableStage.finiteSeparableFieldCover K (finiteSepField K Ω s))
        (finiteSepPoint K Ω s))
      (inclusion p x hx) (inclusion_factor p x hx _ _).symm U).inv =
      (separableFieldBaseChangeIso K Ω p s U).hom := by
  exact ModelActions.refinement_inv _ _ _ _ _

variable [CompactSpace X] [QuasiSeparatedSpace X]

include ha in
/-- Every actual arrow between geometric pullbacks commutes with the action
of an arithmetic automorphism whose actual field projection is trivial. -/
theorem action_naturality (U V : Scheme.FiniteEtale X)
    (γ : (baseChange (inclusion p x hx).right).obj U ⟶
      (baseChange (inclusion p x hx).right).obj V)
    (z : Fiber (geometricPoint p x hx) ((baseChange (inclusion p x hx).right).obj U)) :
    (fiberToFinite (geometricPoint p x hx)).map γ
        (ModelActions.action (inclusion p x hx) a U z) =
      ModelActions.action (inclusion p x hx) a V
        ((fiberToFinite (geometricPoint p x hx)).map γ z) := by
  obtain ⟨s, g, hg⟩ := exists_separable_field_cover_hom K Ω p U V γ
  let Z := SeparableStage.finiteSeparableFieldCover K (finiteSepField K Ω s)
  let q := finiteSepPoint K Ω s
  let r := stageInclusion p x hx Z q
  let v := stageProjection p x hx Z q
  let f := inclusion p x hx
  have e : f = r ≫ v := (inclusion_factor p x hx Z q).symm
  have hγ : ModelActions.refinement r v f e U ≫ (baseChange r.right).map g =
      γ ≫ ModelActions.refinement r v f e V := by
    rw [← ModelActions.refinementIso_hom, ← ModelActions.refinementIso_hom]
    apply (cancel_mono (ModelActions.refinementIso r v f e V).inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [refinement_separable p x hx]
    have hg' : (baseChange r.right).map g ≫ (separableFieldBaseChangeIso K Ω p s V).hom =
        (separableFieldBaseChangeIso K Ω p s U).hom ≫ γ := hg
    rw [hg']
    rw [← refinement_separable p x hx]
    exact (ModelActions.refinementIso r v f e U).hom_inv_id_assoc γ
  exact ModelActions.naturality_of_refinement r v f e (stageAut p x hx a ha Z q) a
    (map_stageAut p x hx a ha Z q) U V g γ hγ z

end AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel.PointedField

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 c18829aef99c0d4c4081b06f358fec8315a55efbb79323e92f544acc1136bc95.
Definitions, hypotheses and universes are retained modulo native names. -/
