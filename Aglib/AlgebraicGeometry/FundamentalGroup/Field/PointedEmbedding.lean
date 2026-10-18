/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.Embedding
public import Aglib.AlgebraicGeometry.Group.Monodromy
public import Aglib.AlgebraicGeometry.SchemeOverField
public import Aglib.AlgebraicGeometry.Group.ScalarExtension

/-!
# Actual curve-origin transport for the constructed field restriction

Auxiliary naturality for K2-018 arithmetic characters and integrality test,
mathematical revision e73d98b1b5c1e5abcdebf7d058e436d792b87982, expose SHA256
 e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299.
The actual closure arrow is used on finite covers pulled back to the rational
origin. A natural fibre comparison and continuous pointed restriction are
constructed, rather than supplied. The same global scheme and origin are used.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Group.BaseChange (groupSchemeBaseChange scalarExtensionMap)
open _root_.AlgebraicGeometry.Scheme.OverField (Base FScheme)

noncomputable section
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.PreGaloisCategory CategoryTheory.MonObj
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberBaseChangeEquiv
  fiberBaseChangeEquiv_left fiberBaseChangeEquiv_symm_left fiberToFinite
  fiberToFiniteBaseChangeIso)
open CategoryTheory
open AlgebraicGeometry.Scheme.FiniteEtale.PointedCovers
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open AlgebraicGeometry.Scheme.Group.Monodromy
namespace AlgebraicGeometry.Scheme.FiniteEtale.PointedFieldEmbeddingBaseChange
open FieldEmbeddingBaseChange
universe u
attribute [local instance] Over.cartesianMonoidalCategory
variable {F K : Type u} [Field F] [Field K] (i : F →+* K)
variable {X : Scheme.{u}} (o : Base F ⟶ X)

/-- Fibre comparison at an actual F-rational point, obtained by pulling every
finite cover back to Spec F and using the proved closed-field comparison. -/
def originFiberComparison :
    fiberToFinite (FieldGalois.geometricPoint F ≫ o) ≅
      fiberToFinite (extensionPoint i ≫ o) :=
  fiberToFiniteBaseChangeIso o (FieldGalois.geometricPoint F) ≪≫
    isoWhiskerLeft (baseChange o)
      (GeometricFibres.closedFiberNatIso F (AlgebraicClosure K) (extensionPoint i)) ≪≫
    (fiberToFiniteBaseChangeIso o (extensionPoint i)).symm

/-- This derived fibre comparison is actual precomposition with the closure arrow. -/
theorem originFiberComparison_hom_left (Y : Scheme.FiniteEtale X)
    (q : Fiber (FieldGalois.geometricPoint F ≫ o) Y) :
    ((originFiberComparison i o).hom.app Y q).left = (closurePointArrow i).left ≫ q.left := by
  change ((fiberToFiniteBaseChangeIso o (extensionPoint i)).inv.app Y
    ((GeometricFibres.closedFiberNatIso F (AlgebraicClosure K) (extensionPoint i)).hom.app
      ((baseChange o).obj Y)
      ((fiberToFiniteBaseChangeIso o (FieldGalois.geometricPoint F)).hom.app Y q))).left = _
  rw [finiteBaseChangeIso_inv_apply, finiteBaseChangeIso_hom_apply, fiberBaseChangeEquiv_symm_left]
  change ((closurePointArrow i).left ≫ (fiberBaseChangeEquiv o (FieldGalois.geometricPoint F) Y
    q).left) ≫ _ = _
  rw [Category.assoc, fiberBaseChangeEquiv_left, pullback.lift_fst]

/-- Continuous transport from the actual extended-origin group to the original
chosen global-origin group. -/
def originTransport : FiberAutGroup (extensionPoint i ≫ o) →ₜ*
    FiberAutGroup (FieldGalois.geometricPoint F ≫ o) where
  __ := (Aut.autMulEquivOfIso (originFiberComparison i o).symm).toMonoidHom
  continuous_toFun := by
    rw [Topology.IsInducing.continuous_iff
      (PreGaloisCategory.autEmbedding_isClosedEmbedding
        (fiberToFinite (FieldGalois.geometricPoint F ≫ o))).isInducing, continuous_pi_iff]
    intro Y
    change Continuous (fun a : FiberAutGroup (extensionPoint i ≫ o) =>
      Aut.autMulEquivOfIso ((originFiberComparison i o).app Y).symm
        (PreGaloisCategory.autEmbedding (fiberToFinite (extensionPoint i ≫ o)) a Y))
    exact continuous_of_discreteTopology.comp
      ((continuous_apply Y).comp continuous_induced_dom)

@[simp] theorem originTransport_apply (g : FiberAutGroup (extensionPoint i ≫ o))
    (Y : Scheme.FiniteEtale X) (q : Fiber (FieldGalois.geometricPoint F ≫ o) Y) :
    (originTransport i o g).hom.app Y q =
      (originFiberComparison i o).inv.app Y
        (g.hom.app Y ((originFiberComparison i o).hom.app Y q)) := rfl

theorem originFiberComparison_equivariant (g : FiberAutGroup (extensionPoint i ≫ o))
    (Y : Scheme.FiniteEtale X) (q : Fiber (FieldGalois.geometricPoint F ≫ o) Y) :
    (originFiberComparison i o).hom.app Y ((originTransport i o g).hom.app Y q) =
      g.hom.app Y ((originFiberComparison i o).hom.app Y q) := by
  rw [originTransport_apply]
  exact ConcreteCategory.congr_hom ((originFiberComparison i o).inv_hom_id_app Y) _

/-- Transport on field fibres before the actual field scheme pullback. -/
def fieldTransport : FiberAutGroup (extensionPoint i) →* FieldGalois.FieldFundamentalGroup F :=
  (Aut.autMulEquivOfIso
    (GeometricFibres.closedFiberNatIso F (AlgebraicClosure K) (extensionPoint i)).symm).toMonoidHom

theorem fieldTransport_equivariant (g : FiberAutGroup (extensionPoint i))
    (Y : Scheme.FiniteEtale (Base F)) (q : Fiber (FieldGalois.geometricPoint F) Y) :
    (GeometricFibres.closedFiberNatIso F (AlgebraicClosure K) (extensionPoint i)).hom.app Y
      ((fieldTransport i g).hom.app Y q) =
    g.hom.app Y
      ((GeometricFibres.closedFiberNatIso F (AlgebraicClosure K) (extensionPoint i)).hom.app Y q)
        := by
  change (GeometricFibres.closedFiberNatIso F (AlgebraicClosure K) (extensionPoint i)).hom.app Y
    ((GeometricFibres.closedFiberNatIso F (AlgebraicClosure K) (extensionPoint i)).inv.app Y _) = _
  exact ConcreteCategory.congr_hom
    ((GeometricFibres.closedFiberNatIso F (AlgebraicClosure K) (extensionPoint i)).inv_hom_id_app
      Y) _

theorem fieldRestriction_factor (g : FieldGalois.FieldFundamentalGroup K) :
    fieldTransport i
      (Scheme.FiniteEtale.ClassificationNaturality.inducedGroupHom
        (scalarExtensionMap i) (FieldGalois.geometricPoint K) g) = fieldRestriction i g := by
  apply Aut.ext
  apply NatTrans.ext
  funext Y
  apply FintypeCat.hom_ext
  intro q
  rfl

theorem pointedMap_fiber_equivariant {L : Type u} [Field L]
    {S T : PointedScheme L} (f : S ⟶ T) (g : FiberAutGroup S.hom)
    (Y : Scheme.FiniteEtale T.right) (q : Fiber T.hom Y) :
    (pointedFiberIso f).hom.app Y ((pointedMap f g).hom.app Y q) =
      g.hom.app ((baseChange f.right).obj Y) ((pointedFiberIso f).hom.app Y q) := by
  change pointedFiberEquiv f Y ((pointedMap f g).hom.app Y q) =
    g.hom.app ((baseChange f.right).obj Y) (pointedFiberEquiv f Y q)
  rw [pointedMap_apply, Equiv.apply_symm_apply]

section Projection
variable (p : X ⟶ Base F) (ho : o ≫ p = 𝟙 _)

/-- The derived closure transport commutes with actual fibre pullback under the
scheme projection. -/
theorem projectionFiberComparison (Y : Scheme.FiniteEtale (Base F))
    (q : Fiber (FieldGalois.geometricPoint F) Y) :
    (originFiberComparison i o).hom.app ((baseChange p).obj Y)
      ((pointedFiberIso (pointedProjection (FieldGalois.geometricPoint F) p o ho)).hom.app Y q) =
    (pointedFiberIso (pointedProjection (extensionPoint i) p o ho)).hom.app Y
      ((GeometricFibres.closedFiberNatIso F (AlgebraicClosure K) (extensionPoint i)).hom.app Y q)
        := by
  apply Over.OverMorphism.ext
  rw [originFiberComparison_hom_left]
  change (closurePointArrow i).left ≫
    ((pointFiberIso p (FieldGalois.geometricPoint F ≫ o) (FieldGalois.geometricPoint F)
      (by simp [Category.assoc, ho])).hom.app Y q).left =
    ((pointFiberIso p (extensionPoint i ≫ o) (extensionPoint i)
      (by simp [Category.assoc, ho])).hom.app Y
        ((GeometricFibres.closedFiberNatIso F (AlgebraicClosure K) (extensionPoint i)).hom.app Y
          q)).left
  rw [pointFiberIso_hom_left, pointFiberIso_hom_left]
  change (closurePointArrow i).left ≫ pullback.lift q.left
    (FieldGalois.geometricPoint F ≫ o) _ =
      pullback.lift ((closurePointArrow i).left ≫ q.left) (extensionPoint i ≫ o) _
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc]
    exact congrArg (fun z => z ≫ o) (Over.w (closurePointArrow i))

/-- Arithmetic projection of actual curve-origin transport is exactly the
constructed field-fibre transport. -/
theorem originTransport_projection (g : FiberAutGroup (extensionPoint i ≫ o)) :
    projectionHom (FieldGalois.geometricPoint F) p o ho (originTransport i o g) =
      fieldTransport i (projectionHom (extensionPoint i) p o ho g) := by
  apply Aut.ext
  apply NatTrans.ext
  funext Y
  apply FintypeCat.hom_ext
  intro q
  apply (FintypeCat.equivEquivIso.symm
    ((GeometricFibres.closedFiberNatIso F (AlgebraicClosure K) (extensionPoint i)).app Y)).injective
  apply (FintypeCat.equivEquivIso.symm
    ((pointedFiberIso (pointedProjection (extensionPoint i) p o ho)).app Y)).injective
  change (pointedFiberIso (pointedProjection (extensionPoint i) p o ho)).hom.app Y
    ((GeometricFibres.closedFiberNatIso F (AlgebraicClosure K) (extensionPoint i)).hom.app Y
      ((pointedMap (pointedProjection (FieldGalois.geometricPoint F) p o ho)
        (originTransport i o g)).hom.app Y q)) =
    (pointedFiberIso (pointedProjection (extensionPoint i) p o ho)).hom.app Y
      ((GeometricFibres.closedFiberNatIso F (AlgebraicClosure K) (extensionPoint i)).hom.app Y
        ((fieldTransport i (pointedMap (pointedProjection (extensionPoint i) p o ho) g)).hom.app
          Y q))
  rw [← projectionFiberComparison, pointedMap_fiber_equivariant]
  change (originFiberComparison i o).hom.app ((baseChange p).obj Y)
    ((originTransport i o g).hom.app ((baseChange p).obj Y)
      ((pointedFiberIso (pointedProjection (FieldGalois.geometricPoint F) p o ho)).hom.app Y q)) = _
  rw [originFiberComparison_equivariant, projectionFiberComparison,
    fieldTransport_equivariant]
  exact (pointedMap_fiber_equivariant (pointedProjection (extensionPoint i) p o ho) g Y
    ((GeometricFibres.closedFiberNatIso F (AlgebraicClosure K) (extensionPoint i)).hom.app Y
      q)).symm

end Projection

/-- The fibre comparison commutes with pullback along the actual rational origin. -/
theorem originSectionFiberComparison (Y : Scheme.FiniteEtale X)
    (q : Fiber (FieldGalois.geometricPoint F ≫ o) Y) :
    (fiberToFiniteBaseChangeIso o (extensionPoint i)).hom.app Y
      ((originFiberComparison i o).hom.app Y q) =
    (GeometricFibres.closedFiberNatIso F (AlgebraicClosure K) (extensionPoint i)).hom.app
      ((baseChange o).obj Y)
      ((fiberToFiniteBaseChangeIso o (FieldGalois.geometricPoint F)).hom.app Y q) := by
  change (fiberToFiniteBaseChangeIso o (extensionPoint i)).hom.app Y
    ((fiberToFiniteBaseChangeIso o (extensionPoint i)).inv.app Y _) = _
  exact ConcreteCategory.congr_hom
    ((fiberToFiniteBaseChangeIso o (extensionPoint i)).inv_hom_id_app Y) _

theorem originHom_fiber_equivariant {L : Type u} [Field L]
    (b : Spec (.of L) ⟶ Base F) (g : FiberAutGroup b)
    (Y : Scheme.FiniteEtale X) (q : Fiber (b ≫ o) Y) :
    (fiberToFiniteBaseChangeIso o b).hom.app Y ((originHom b o g).hom.app Y q) =
      g.hom.app ((baseChange o).obj Y) ((fiberToFiniteBaseChangeIso o b).hom.app Y q) :=
  pointedMap_fiber_equivariant (pointedOrigin b o) g Y q

/-- Actual closed-field origin transport preserves the actual arithmetic section. -/
theorem originTransport_section (g : FiberAutGroup (extensionPoint i)) :
    originTransport i o (originHom (extensionPoint i) o g) =
      originHom (FieldGalois.geometricPoint F) o (fieldTransport i g) := by
  apply Aut.ext
  apply NatTrans.ext
  funext Y
  apply FintypeCat.hom_ext
  intro q
  apply (FintypeCat.equivEquivIso.symm ((originFiberComparison i o).app Y)).injective
  apply (FintypeCat.equivEquivIso.symm
    ((fiberToFiniteBaseChangeIso o (extensionPoint i)).app Y)).injective
  change (fiberToFiniteBaseChangeIso o (extensionPoint i)).hom.app Y
    ((originFiberComparison i o).hom.app Y
      ((originTransport i o (originHom (extensionPoint i) o g)).hom.app Y q)) =
    (fiberToFiniteBaseChangeIso o (extensionPoint i)).hom.app Y
      ((originFiberComparison i o).hom.app Y
        ((originHom (FieldGalois.geometricPoint F) o (fieldTransport i g)).hom.app Y q))
  rw [originFiberComparison_equivariant, originHom_fiber_equivariant]
  simp only [originSectionFiberComparison]
  rw [originHom_fiber_equivariant, fieldTransport_equivariant]

variable (H : Grp (FScheme F))

/-- The actual continuous pointed curve restriction, at the original global
algebraic-closure origin and actual local algebraic-closure origin. -/
def pointedRestriction :
    FiberAutGroup (originPoint (FieldGalois.geometricPoint K)
      ((groupSchemeBaseChange (scalarExtensionMap i)).functor.obj H)) →ₜ*
    FiberAutGroup (originPoint (FieldGalois.geometricPoint F) H) :=
  (originTransport i η[H.X].left).comp
    (inducedPointedHom (scalarExtensionMap i) (FieldGalois.geometricPoint K))

/-- The actual pointed restriction commutes with the actual arithmetic field
restriction at the original and local geometric points. -/
theorem pointedRestriction_projection
    (g : FiberAutGroup (originPoint (FieldGalois.geometricPoint K)
      ((groupSchemeBaseChange (scalarExtensionMap i)).functor.obj H))) :
    originProjection (FieldGalois.geometricPoint F) H (pointedRestriction i H g) =
      fieldRestriction i
        (originProjection (FieldGalois.geometricPoint K)
          ((groupSchemeBaseChange (scalarExtensionMap i)).functor.obj H) g) := by
  change projectionHom (FieldGalois.geometricPoint F) H.X.hom η[H.X].left (Over.w η[H.X])
    (originTransport i η[H.X].left
      (inducedPointedHom (scalarExtensionMap i) (FieldGalois.geometricPoint K) g)) = _
  rw [originTransport_projection]
  change fieldTransport i
    (originProjection (extensionPoint i) H
      (inducedPointedHom (scalarExtensionMap i) (FieldGalois.geometricPoint K) g)) = _
  rw [inducedPointedHom_projection, fieldRestriction_factor]

/-- The actual completed origin section maps to the original global origin section. -/
theorem pointedRestriction_section (g : FieldGalois.FieldFundamentalGroup K) :
    pointedRestriction i H
      (originSection (FieldGalois.geometricPoint K)
        ((groupSchemeBaseChange (scalarExtensionMap i)).functor.obj H) g) =
    originSection (FieldGalois.geometricPoint F) H (fieldRestriction i g) := by
  change originTransport i η[H.X].left
    (inducedPointedHom (scalarExtensionMap i) (FieldGalois.geometricPoint K)
      (originSection (FieldGalois.geometricPoint K)
        ((groupSchemeBaseChange (scalarExtensionMap i)).functor.obj H) g)) = _
  rw [inducedPointedHom_section]
  change originTransport i η[H.X].left
    (originHom (extensionPoint i) η[H.X].left
      (Scheme.FiniteEtale.ClassificationNaturality.inducedGroupHom
        (scalarExtensionMap i) (FieldGalois.geometricPoint K) g)) = _
  rw [originTransport_section, fieldRestriction_factor]
  rfl

/-- The geometric kernels therefore restrict through the actual pointed-field map. -/
def geometricRestriction :
    (originProjection (FieldGalois.geometricPoint K)
      ((groupSchemeBaseChange (scalarExtensionMap i)).functor.obj H)).ker →*
    (originProjection (FieldGalois.geometricPoint F) H).ker where
  toFun g := ⟨pointedRestriction i H g.1, by
    rw [MonoidHom.mem_ker, pointedRestriction_projection]
    rw [show originProjection (FieldGalois.geometricPoint K)
      ((groupSchemeBaseChange (scalarExtensionMap i)).functor.obj H) g.1 = 1 from g.2, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ _ _)

section KernelFibre
variable {A G : Grp (FScheme F)} (p : G ⟶ H)
variable [IsFinite p.hom.hom.left] [Etale p.hom.hom.left]
variable [IsFinite A.X.hom]
variable (m : KernelMarking A G H p)

/-- The existing kernel marking commutes with the derived actual closed-field
fibre comparison. -/
theorem kernelFibreComparison
    (a : Over.mk (FieldGalois.geometricPoint F) ⟶ A.X) :
    (originFiberComparison i η[H.X].left).hom.app (arrowCover p)
      (kernelFibreEquiv p (FieldGalois.geometricPoint F) m a) =
    kernelFibreEquiv p (extensionPoint i) m
      (GeometricFibres.closedGroupPointsEquiv F (AlgebraicClosure K) (extensionPoint i) A a) := by
  apply Over.OverMorphism.ext
  rw [originFiberComparison_hom_left, kernelFibreEquiv_left, kernelFibreEquiv_left]
  change (closurePointArrow i).left ≫ (a.left ≫ m.inclusion.hom.hom.left) =
    ((closurePointArrow i).left ≫ a.left) ≫ m.inclusion.hom.hom.left
  exact (Category.assoc _ _ _).symm

/-- Full marked monodromy of the same global arrow commutes with the actual
closed-point transport, before its actual scalar extension. -/
theorem markedMonodromy_originTransport
    (g : FiberAutGroup (originPoint (extensionPoint i) H))
    (a : Over.mk (FieldGalois.geometricPoint F) ⟶ A.X) :
    GeometricFibres.closedGroupPointsEquiv F (AlgebraicClosure K) (extensionPoint i) A
      (markedMonodromy p (FieldGalois.geometricPoint F) m
        (originTransport i η[H.X].left g) a) =
    markedMonodromy p (extensionPoint i) m g
      (GeometricFibres.closedGroupPointsEquiv F (AlgebraicClosure K) (extensionPoint i) A a) := by
  apply (kernelFibreEquiv p (extensionPoint i) m).injective
  rw [← kernelFibreComparison]
  simp only [markedMonodromy_apply, Equiv.apply_symm_apply]
  rw [← kernelFibreComparison]
  exact originFiberComparison_equivariant i η[H.X].left g (arrowCover p)
    (kernelFibreEquiv p (FieldGalois.geometricPoint F) m a)

end KernelFibre

end AlgebraicGeometry.Scheme.FiniteEtale.PointedFieldEmbeddingBaseChange

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 53e207e9204a3a908217b41375e3c8ce8b00e386b0c7b3b1eff4d186114d709f.
Definitions, hypotheses and universes are retained modulo native names. -/
