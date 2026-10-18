/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.BaseChange.MarkedKernel
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange.PointedClassification
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Field
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
public import Aglib.AlgebraicGeometry.SchemeOverField
public import Aglib.AlgebraicGeometry.Group.ScalarExtension

/-!
# Actual marked-isogeny monodromy under scalar extension

Source: auxiliary naturality in `K2-018#prop:k2018-arithmetic-characters` and
`K2-018#prop:k2018-integrality-test`, mathematical source
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, `research/exposes/K2/018/expose.tex`,
SHA256 `e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.
Engineering prerequisites: HEAD `7dcde130d429905e2624079dd7a0d18e3ebc94e2`,
Lean 4.34.1/mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, and the reviewed
ScalarExtension source SHA256
`519ab5fad31dcbb3973dcd366e83c0a1166bbf867be647d5d314518df014ff0e`.

The coefficient marking is retained. The underlying local cover is compared
with the actual pullback cover, and fibre monodromy uses the actual induced
pointed fundamental-group map. No monodromy-data package or character square
is assumed. Independently chosen algebraic-closure points and the canonical
Tate coefficient over different fields are separate from this generic slice.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Group.BaseChange
  (groupSchemeBaseChange groupSchemeBaseChange_map_left_fst groupSchemeScalarExtension
    pullbackFiberMulEquiv_apply_left_fst scalarExtensionMap)
open _root_.AlgebraicGeometry.Scheme.OverField (Base FScheme)

noncomputable section
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory
open CategoryTheory
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberToFinite mk)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open AlgebraicGeometry.Scheme.FiniteEtale.GroupBaseChange
namespace AlgebraicGeometry.Scheme.Group.Monodromy
universe u
attribute [local instance] Over.cartesianMonoidalCategory

section KernelFibre
variable {T : Scheme.{u}} {A G H : Grp (Over T)} (p : G ⟶ H)
variable [IsFinite p.hom.hom.left] [Etale p.hom.hom.left]

/-- The actual finite étale cover underlying the group-scheme arrow.
Source: marked-naturality subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
abbrev arrowCover : Scheme.FiniteEtale H.X.left := Scheme.FiniteEtale.mk p.hom.hom.left

variable {L : Type u} [Field L] (t : Spec (.of L) ⟶ T)

/-- The actual origin evaluated at the given field-valued base point.
Source: marked-naturality subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
abbrev originPoint (H : Grp (Over T)) := t ≫ η[H.X].left

/-- The actual arithmetic projection from the origin-pointed fundamental group.
Source: marked-naturality subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
def originProjection (H : Grp (Over T)) : FiberAutGroup (originPoint t H) →* FiberAutGroup t :=
  projectionHom t H.X.hom η[H.X].left (Over.w η[H.X])

/-- The actual origin section on fundamental groups.
Source: marked-naturality subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
def originSection (H : Grp (Over T)) : FiberAutGroup t →* FiberAutGroup (originPoint t H) :=
  originHom t η[H.X].left

/-- A point in the fibre above the origin is an actual source-group point.
Source: marked-naturality subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
def fibrePoint (y : Fiber (originPoint t H) (arrowCover p)) : Over.mk t ⟶ G.X :=
  Over.homMk y.left (by
    have hy : y.left ≫ p.hom.hom.left = t ≫ η[H.X].left := Over.w y
    rw [← Over.w p.hom.hom, ← Category.assoc, hy, Category.assoc,
      Over.w η[H.X], Over.tensorUnit_hom, Category.comp_id]
    rfl)

/-- Such a point belongs to the actual scheme-group kernel.
Source: marked-naturality subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
theorem fibrePoint_kernel (y : Fiber (originPoint t H) (arrowCover p)) :
    fibrePoint p t y ≫ p.hom.hom = 1 := by
  apply Over.OverMorphism.ext
  change y.left ≫ p.hom.hom.left = t ≫ η[H.X].left
  exact Over.w y

/-- The actual cover fibre and the kernel of the point-group map coincide.
Source: marked-naturality subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
def fibreKernelEquiv : Fiber (originPoint t H) (arrowCover p) ≃
    {x : Over.mk t ⟶ G.X // x ≫ p.hom.hom = 1} where
  toFun y := ⟨fibrePoint p t y, fibrePoint_kernel p t y⟩
  invFun x := Over.homMk x.1.left (congrArg Over.Hom.left x.2)
  left_inv y := by apply Over.OverMorphism.ext; rfl
  right_inv x := by apply Subtype.ext; apply Over.OverMorphism.ext; rfl

variable (m : KernelMarking A G H p)

/-- The given universal kernel marking gives a bijection on actual point kernels.
Source: marked-naturality subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
def kernelPointEquiv : (Over.mk t ⟶ A.X) ≃
    {x : Over.mk t ⟶ G.X // x ≫ p.hom.hom = 1} :=
  Equiv.ofBijective (fun a => ⟨a ≫ m.inclusion.hom.hom, by
    rw [Category.assoc, m.over, MonObj.comp_one]⟩) (by
      constructor
      · intro a b hab
        obtain ⟨c, hc, hu⟩ := m.unique_lift (a ≫ m.inclusion.hom.hom)
          (by rw [Category.assoc, m.over, MonObj.comp_one])
        exact (hu a rfl).trans (hu b (congrArg Subtype.val hab).symm).symm
      · intro x
        obtain ⟨a, ha, _⟩ := m.unique_lift x.1 x.2
        exact ⟨a, Subtype.ext ha⟩)

/-- The actual coefficient-point coordinate of the marked origin fibre.
Source: marked-naturality subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
def kernelFibreEquiv : (Over.mk t ⟶ A.X) ≃ Fiber (originPoint t H) (arrowCover p) :=
  (kernelPointEquiv p t m).trans (fibreKernelEquiv p t).symm

@[simp] theorem kernelFibreEquiv_left (a : Over.mk t ⟶ A.X) :
    (kernelFibreEquiv p t m a).left = a.left ≫ m.inclusion.hom.hom.left := rfl

/-- Actual monodromy expressed in the coefficient points fixed by the kernel marking.
Source: marked-naturality subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
def markedMonodromy : FiberAutGroup (originPoint t H) →*
    Equiv.Perm (Over.mk t ⟶ A.X) where
  toFun g := ((kernelFibreEquiv p t m).trans
    (FintypeCat.equivEquivIso.symm (g.app (arrowCover p)))).trans (kernelFibreEquiv p t m).symm
  map_one' := by
    apply Equiv.ext
    intro a
    exact (kernelFibreEquiv p t m).symm_apply_apply a
  map_mul' g h := by
    apply Equiv.ext
    intro a
    change (kernelFibreEquiv p t m).symm
      ((g * h).hom.app (arrowCover p) (kernelFibreEquiv p t m a)) =
      (kernelFibreEquiv p t m).symm (g.hom.app (arrowCover p)
        (kernelFibreEquiv p t m ((kernelFibreEquiv p t m).symm
          (h.hom.app (arrowCover p) (kernelFibreEquiv p t m a)))))
    rw [Equiv.apply_symm_apply]
    rfl

@[simp] theorem markedMonodromy_apply (g : FiberAutGroup (originPoint t H))
    (a : Over.mk t ⟶ A.X) :
    markedMonodromy p t m g a = (kernelFibreEquiv p t m).symm
      (g.hom.app (arrowCover p) (kernelFibreEquiv p t m a)) := rfl
end KernelFibre

section BaseChange
variable {S T : Scheme.{u}} (f : S ⟶ T) {A G H : Grp (Over T)} (p : G ⟶ H)
variable [IsFinite p.hom.hom.left] [Etale p.hom.hom.left]
local instance mappedFinite : IsFinite ((groupSchemeBaseChange f).functor.map p).hom.hom.left :=
  Scheme.Group.BaseChange.map_finite f p inferInstance
local instance mappedEtale : Etale ((groupSchemeBaseChange f).functor.map p).hom.hom.left :=
  Scheme.Group.BaseChange.map_etale f p inferInstance

/-- The scalar-extended arrow is the actual target-cover pullback, by its Cartesian square.
Source: marked-naturality subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
def coverPullbackIso :
    arrowCover ((groupSchemeBaseChange f).functor.map p) ≅
      (baseChange (pullback.fst H.X.hom f)).obj (arrowCover p) :=
  ObjectProperty.isoMk _ (Over.isoMk (Scheme.Group.BaseChange.map_isPullback f p).isoPullback
    (by exact (Scheme.Group.BaseChange.map_isPullback f p).isoPullback_hom_snd))

@[reassoc (attr := simp)] theorem coverPullbackIso_hom_fst :
    (coverPullbackIso f p).hom.hom.left ≫
      pullback.fst p.hom.hom.left (pullback.fst H.X.hom f) = pullback.fst G.X.hom f :=
  (Scheme.Group.BaseChange.map_isPullback f p).isoPullback_hom_fst

variable {L : Type u} [Field L] (s : Spec (.of L) ⟶ S)

/-- Origin compatibility supplies the actual pointed target morphism.
Source: marked-naturality subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
theorem origin_projection :
    originPoint s ((groupSchemeBaseChange f).functor.obj H) ≫ pullback.fst H.X.hom f =
      originPoint (s ≫ f) H := by
  change (s ≫ η[((groupSchemeBaseChange f).functor.obj H).X].left) ≫
    pullback.fst H.X.hom f = (s ≫ f) ≫ η[H.X].left
  rw [Category.assoc, Scheme.Group.BaseChange.origin_fst, Category.assoc]

/-- The actual continuous map of pointed fundamental groups.
Source: marked-naturality subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
def inducedPointedHom :
    FiberAutGroup (originPoint s ((groupSchemeBaseChange f).functor.obj H)) →ₜ*
      FiberAutGroup (originPoint (s ≫ f) H) :=
  inducedGroupHomPointed (pullback.fst H.X.hom f)
    (originPoint s ((groupSchemeBaseChange f).functor.obj H))
    (originPoint (s ≫ f) H) (origin_projection f s)

/-- The induced map commutes with the arithmetic projections because the scheme square does.
Source: marked-naturality subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
theorem inducedPointedHom_projection
    (g : FiberAutGroup (originPoint s ((groupSchemeBaseChange f).functor.obj H))) :
    originProjection (s ≫ f) H (inducedPointedHom f s g) =
      Scheme.FiniteEtale.ClassificationNaturality.inducedGroupHom f s
        (originProjection s ((groupSchemeBaseChange f).functor.obj H) g) := by
  let hf : Under.mk (originPoint s ((groupSchemeBaseChange f).functor.obj H)) ⟶
      Under.mk (originPoint (s ≫ f) H) := Under.homMk (pullback.fst H.X.hom f) (origin_projection
        f s)
  let bf : Under.mk s ⟶ Under.mk (s ≫ f) := Under.homMk f rfl
  let lp := pointedProjection s (((groupSchemeBaseChange f).functor.obj H).X.hom)
    η[((groupSchemeBaseChange f).functor.obj H).X].left (Over.w η[((groupSchemeBaseChange
      f).functor.obj H).X])
  let gp := pointedProjection (s ≫ f) H.X.hom η[H.X].left (Over.w η[H.X])
  have he : hf ≫ gp = lp ≫ bf := by
    apply Under.UnderMorphism.ext
    exact pullback.condition
  have hm := congrArg (fun k => pointedMap k g) he
  change pointedMap gp (pointedMap hf g) = pointedMap bf (pointedMap lp g)
  simpa only [pointedMap_comp, MonoidHom.comp_apply] using hm

/-- The induced map commutes with actual origin sections, using the proved origin square.
Source: marked-naturality subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
theorem inducedPointedHom_section (g : FiberAutGroup s) :
    inducedPointedHom f s (originSection s ((groupSchemeBaseChange f).functor.obj H) g) =
      originSection (s ≫ f) H (Scheme.FiniteEtale.ClassificationNaturality.inducedGroupHom f s g)
        := by
  let hf : Under.mk (originPoint s ((groupSchemeBaseChange f).functor.obj H)) ⟶
      Under.mk (originPoint (s ≫ f) H) := Under.homMk (pullback.fst H.X.hom f) (origin_projection
        f s)
  let bf : Under.mk s ⟶ Under.mk (s ≫ f) := Under.homMk f rfl
  let lo := pointedOrigin s η[((groupSchemeBaseChange f).functor.obj H).X].left
  let go := pointedOrigin (s ≫ f) η[H.X].left
  have he : lo ≫ hf = bf ≫ go := by
    apply Under.UnderMorphism.ext
    exact Scheme.Group.BaseChange.origin_fst f H
  have hm := congrArg (fun k => pointedMap k g) he
  change pointedMap hf (pointedMap lo g) = pointedMap go (pointedMap bf g)
  simpa only [pointedMap_comp, MonoidHom.comp_apply] using hm

/-- The geometric projection kernels map by the actual pointed scheme map.
Kernel membership is proved from the preceding arithmetic-projection square.
Source: marked-naturality subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
def kernelRestriction :
    (originProjection s ((groupSchemeBaseChange f).functor.obj H)).ker →*
      (originProjection (s ≫ f) H).ker where
  toFun g := ⟨inducedPointedHom f s g.1, by
    rw [MonoidHom.mem_ker, inducedPointedHom_projection]
    rw [show originProjection s ((groupSchemeBaseChange f).functor.obj H) g.1 = 1 from g.2,
      map_one]⟩
  map_one' := Subtype.ext (map_one (inducedPointedHom f s))
  map_mul' g h := Subtype.ext (map_mul (inducedPointedHom f s) g.1 h.1)

/-- The actual local origin fibre maps to the global fibre through pullback projection.
Source: marked-naturality subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
def fibreProjectionEquiv :
    Fiber (originPoint s ((groupSchemeBaseChange f).functor.obj H))
      (arrowCover ((groupSchemeBaseChange f).functor.map p)) ≃
      Fiber (originPoint (s ≫ f) H) (arrowCover p) :=
  (FintypeCat.equivEquivIso.symm ((fiberToFinite _).mapIso (coverPullbackIso f p))).trans
    (fiberBaseChangeEquivPointed (pullback.fst H.X.hom f)
      (originPoint s ((groupSchemeBaseChange f).functor.obj H))
      (originPoint (s ≫ f) H) (origin_projection f s) (arrowCover p)).symm

@[simp] theorem fibreProjectionEquiv_left
    (y : Fiber (originPoint s ((groupSchemeBaseChange f).functor.obj H))
      (arrowCover ((groupSchemeBaseChange f).functor.map p))) :
    (fibreProjectionEquiv f p s y).left = y.left ≫ pullback.fst G.X.hom f := by
  change (((pointFiberIso (pullback.fst H.X.hom f)
    (originPoint s ((groupSchemeBaseChange f).functor.obj H)) (originPoint (s ≫ f) H)
    (origin_projection f s)).inv.app (arrowCover p))
      ((fiberToFinite _).map (coverPullbackIso f p).hom y)).left = _
  rw [pointFiberIso_inv_left]
  change (y.left ≫ (coverPullbackIso f p).hom.hom.left) ≫
    pullback.fst p.hom.hom.left (pullback.fst H.X.hom f) = _
  rw [Category.assoc, coverPullbackIso_hom_fst]

/-- The canonical fibre projection intertwines actual monodromy, by naturality of the fibre
automorphism.
Source: marked-naturality subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
theorem fibreProjectionEquiv_equivariant
    (g : FiberAutGroup (originPoint s ((groupSchemeBaseChange f).functor.obj H)))
    (y : Fiber (originPoint s ((groupSchemeBaseChange f).functor.obj H))
      (arrowCover ((groupSchemeBaseChange f).functor.map p))) :
    fibreProjectionEquiv f p s (g.hom.app (arrowCover ((groupSchemeBaseChange f).functor.map p))
      y) =
      (inducedPointedHom f s g).hom.app (arrowCover p) (fibreProjectionEquiv f p s y) := by
  let e := fiberBaseChangeEquivPointed (pullback.fst H.X.hom f)
    (originPoint s ((groupSchemeBaseChange f).functor.obj H))
    (originPoint (s ≫ f) H) (origin_projection f s) (arrowCover p)
  change e.symm ((fiberToFinite _).map (coverPullbackIso f p).hom
      (g.hom.app (arrowCover ((groupSchemeBaseChange f).functor.map p)) y)) =
    e.symm (g.hom.app ((baseChange (pullback.fst H.X.hom f)).obj (arrowCover p))
      (e (e.symm ((fiberToFinite _).map (coverPullbackIso f p).hom y))))
  rw [Equiv.apply_symm_apply, evaluate_naturality]

variable (m : KernelMarking A G H p)

omit [IsFinite p.hom.hom.left] [Etale p.hom.hom.left] in
/-- The kernel-translation action commutes with pullback on every test scheme.
Source: marked-naturality subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
theorem kernelAction_baseChange (U : Over S)
    (a : (Over.map f).obj U ⟶ A.X) (x : (Over.map f).obj U ⟶ G.X) :
    Scheme.Group.BaseChange.sectionsMulEquiv f U G (m.toTorsorAction.act a x) =
      (Scheme.Group.BaseChange.kernelMarking f m).toTorsorAction.act
        (Scheme.Group.BaseChange.sectionsMulEquiv f U A a)
          (Scheme.Group.BaseChange.sectionsMulEquiv f U G x) := by
  change Scheme.Group.BaseChange.sectionsMulEquiv f U G ((a ≫ m.inclusion.hom.hom) * x) =
    (Scheme.Group.BaseChange.sectionsMulEquiv f U A a ≫
      ((groupSchemeBaseChange f).functor.map m.inclusion).hom.hom) *
        Scheme.Group.BaseChange.sectionsMulEquiv f U G x
  rw [map_mul, Scheme.Group.BaseChange.sectionsMulEquiv_naturality]

/-- The actual coefficient marking of the local origin fibre projects to the original marking.
Source: marked-naturality subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
theorem kernelFibreEquiv_projection (a : Over.mk (s ≫ f) ⟶ A.X) :
    fibreProjectionEquiv f p s
      (kernelFibreEquiv ((groupSchemeBaseChange f).functor.map p) s
        (Scheme.Group.BaseChange.kernelMarking f m)
          (_root_.AlgebraicGeometry.Scheme.Group.BaseChange.pullbackFiberMulEquiv f s A a)) =
      kernelFibreEquiv p (s ≫ f) m a := by
  apply Over.OverMorphism.ext
  rw [fibreProjectionEquiv_left, kernelFibreEquiv_left, kernelFibreEquiv_left]
  change ((_root_.AlgebraicGeometry.Scheme.Group.BaseChange.pullbackFiberMulEquiv f s A a).left ≫
    ((groupSchemeBaseChange f).functor.map m.inclusion).hom.hom.left) ≫
      pullback.fst G.X.hom f = a.left ≫ m.inclusion.hom.hom.left
  rw [Category.assoc, groupSchemeBaseChange_map_left_fst, ← Category.assoc,
    pullbackFiberMulEquiv_apply_left_fst]

/-- The inverse marked coordinate is compatible with the actual coefficient-point pullback.
Source: marked-naturality subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
theorem kernelFibreEquiv_symm_projection
    (y : Fiber (originPoint s ((groupSchemeBaseChange f).functor.obj H))
      (arrowCover ((groupSchemeBaseChange f).functor.map p))) :
    (kernelFibreEquiv p (s ≫ f) m).symm (fibreProjectionEquiv f p s y) =
      (_root_.AlgebraicGeometry.Scheme.Group.BaseChange.pullbackFiberMulEquiv f s A).symm
        ((kernelFibreEquiv ((groupSchemeBaseChange f).functor.map p) s
          (Scheme.Group.BaseChange.kernelMarking f m)).symm y) := by
  apply (kernelFibreEquiv p (s ≫ f) m).injective
  rw [Equiv.apply_symm_apply]
  have h := kernelFibreEquiv_projection f p s m
    ((_root_.AlgebraicGeometry.Scheme.Group.BaseChange.pullbackFiberMulEquiv f s A).symm
      ((kernelFibreEquiv ((groupSchemeBaseChange f).functor.map p) s
        (Scheme.Group.BaseChange.kernelMarking f m)).symm y))
  rw [MulEquiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  exact h

/-- Actual marked monodromy after base change is the restriction of global monodromy.
The coefficient-point equivalence, pointed group map and commuting square are constructed.
Source: marked-naturality subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
theorem markedMonodromy_baseChange
    (g : FiberAutGroup (originPoint s ((groupSchemeBaseChange f).functor.obj H)))
    (a : Over.mk (s ≫ f) ⟶ A.X) :
    (_root_.AlgebraicGeometry.Scheme.Group.BaseChange.pullbackFiberMulEquiv f s A).symm
      (markedMonodromy ((groupSchemeBaseChange f).functor.map p) s
        (Scheme.Group.BaseChange.kernelMarking f m) g
          (_root_.AlgebraicGeometry.Scheme.Group.BaseChange.pullbackFiberMulEquiv f s A a)) =
      markedMonodromy p (s ≫ f) m (inducedPointedHom f s g) a := by
  rw [markedMonodromy_apply, ← kernelFibreEquiv_symm_projection,
    fibreProjectionEquiv_equivariant, kernelFibreEquiv_projection, markedMonodromy_apply]

/-- In particular, monodromy displacement of the actual origin has the same restriction formula.
This is a value formula; no untwisted character or H¹ identification is asserted by this
declaration.
Source: marked-naturality subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
theorem originDisplacement_baseChange
    (g : FiberAutGroup (originPoint s ((groupSchemeBaseChange f).functor.obj H))) :
    (_root_.AlgebraicGeometry.Scheme.Group.BaseChange.pullbackFiberMulEquiv f s A).symm
      (markedMonodromy ((groupSchemeBaseChange f).functor.map p) s
        (Scheme.Group.BaseChange.kernelMarking f m) g 1) =
      markedMonodromy p (s ≫ f) m (inducedPointedHom f s g) 1 := by
  simpa only [map_one] using markedMonodromy_baseChange f p s m g 1

end BaseChange
end AlgebraicGeometry.Scheme.Group.Monodromy

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 01bf4f19b06f9657841cb68bb4a9c7f3f0f18aab3a89019f9b987cdcef35d5ab.
Definitions, hypotheses and universes are retained modulo native names. -/
