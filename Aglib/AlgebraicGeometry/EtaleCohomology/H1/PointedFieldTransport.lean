/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.PointedEmbedding
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.Naturality
public import Aglib.AlgebraicGeometry.SchemeOverField

/-!
# Actual closed-field change of geometric origin in small-etale H1

K2-018 arithmetic-character/completion comparison, mathematical revision
 e73d98b1b5c1e5abcdebf7d058e436d792b87982, expose SHA256
 e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299.
The accepted actual rational-origin fibre comparison is used. The change of
base point, induced continuous group map, coefficient point map and positive
scheme-torsor transport are constructions, not an assumed H1 square.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.OverField (Base)

noncomputable section
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.PreGaloisCategory CategoryTheory.MonObj
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber fiberToFinite)
open AlgebraicGeometry.Scheme.FiniteEtale.PointedCovers
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open CategoryTheory
open AlgebraicGeometry.Scheme.FiniteEtale
open AlgebraicGeometry.Scheme.FiniteEtale.FiberTorsorActions
open AlgebraicGeometry.Scheme.FiniteEtale.ClassificationNaturality
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.FundamentalGroupComparison
open GroupCohomology.ContinuousH1
namespace AlgebraicGeometry.Scheme.EtaleCohomology.PointedFieldTransport
open FieldEmbeddingBaseChange PointedFieldEmbeddingBaseChange
universe u v w
attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge
variable {F K : Type u} [Field F] [Field K] (i : F →+* K)
variable {X : Scheme.{u}} (o : Base F ⟶ X)

/-- The actual closure arrow at the rational scheme point. -/
def pointArrow : Over.mk (extensionPoint i ≫ o) ⟶ Over.mk (FieldGalois.geometricPoint F ≫ o) :=
  Over.homMk (closurePointArrow i).left (by
    change (closurePointArrow i).left ≫ (FieldGalois.geometricPoint F ≫ o) = extensionPoint i ≫ o
    exact congrArg (fun z => z ≫ o) (Over.w (closurePointArrow i)))

/-- The equivalence from cover points at the original geometric origin to points at
the extended origin, induced by `originFiberComparison i o`. -/
def pointEquiv (Y : Scheme.FiniteEtale X) : Fiber (FieldGalois.geometricPoint F ≫ o) Y ≃ Fiber
    (extensionPoint i ≫ o) Y :=
  FintypeCat.equivEquivIso.symm ((originFiberComparison i o).app Y)

theorem pointEquiv_apply (Y : Scheme.FiniteEtale X)
    (x : Fiber (FieldGalois.geometricPoint F ≫ o) Y) :
    pointEquiv i o Y x = pointArrow i o ≫ x := by
  apply Over.OverMorphism.ext
  exact originFiberComparison_hom_left i o Y x

variable [GaloisCategory (Scheme.FiniteEtale X)]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (FieldGalois.geometricPoint F ≫ o))]

/-- The ordinary fibre-functor axioms at the extended point are transported
through the actual derived natural fibre isomorphism. -/
instance extendedFiberFunctor : PreGaloisCategory.FiberFunctor (fiberToFinite (extensionPoint i ≫
  o)) where
  preservesTerminalObjects := preservesLimitsOfShape_of_natIso (originFiberComparison i o)
  preservesPullbacks := preservesLimitsOfShape_of_natIso (originFiberComparison i o)
  preservesFiniteCoproducts := ⟨fun _ => preservesColimitsOfShape_of_natIso
    (originFiberComparison i o)⟩
  preservesEpis := Functor.PreservesEpimorphisms.of_iso (originFiberComparison i o)
  preservesQuotientsByFiniteGroups _G := preservesColimitsOfShape_of_natIso
    (originFiberComparison i o)
  reflectsIsos := reflectsIsomorphisms_of_iso (originFiberComparison i o)

variable (A : Grp (Over X)) [IsFinite A.X.hom] [Etale A.X.hom]

/-- The multiplicative equivalence between coefficient points at the original and
extended origins; its underlying map is precomposition with `pointArrow i o`. -/
def coefficientPointEquiv :
    (Over.mk (FieldGalois.geometricPoint F ≫ o) ⟶ A.X) ≃*
    (Over.mk (extensionPoint i ≫ o) ⟶ A.X) :=
  { pointEquiv i o (coefficientCover A) with
    map_mul' a b := by
      change pointEquiv i o (coefficientCover A) (a * b) =
        pointEquiv i o (coefficientCover A) a * pointEquiv i o (coefficientCover A) b
      rw [pointEquiv_apply, pointEquiv_apply, pointEquiv_apply]
      exact MonObj.comp_mul (pointArrow i o) a b }

omit [GaloisCategory (Scheme.FiniteEtale X)]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (FieldGalois.geometricPoint F ≫ o))] in
theorem coefficientPointEquiv_apply (a : Over.mk (FieldGalois.geometricPoint F ≫ o) ⟶ A.X) :
    coefficientPointEquiv i o A a = pointArrow i o ≫ a := by
  change pointEquiv i o (coefficientCover A) a = _
  exact pointEquiv_apply i o (coefficientCover A) a

variable [IsCommMonObj A.X]
variable (M : Type v) [AddCommGroup M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
variable [DistribMulAction (FiberAutGroup (FieldGalois.geometricPoint F ≫ o)) M]
  [ContinuousSMul (FiberAutGroup (FieldGalois.geometricPoint F ≫ o)) M]
variable (mark : (Over.mk (FieldGalois.geometricPoint F ≫ o) ⟶ A.X) ≃* Multiplicative M)
variable (hmark : ∀ (g : FiberAutGroup (FieldGalois.geometricPoint F ≫ o)) a,
  mark (g.hom.app (coefficientCover A) a) = Multiplicative.ofAdd (g • (mark a).toAdd))
/-- The action of the extended-origin fibre automorphism group on `M` obtained by
restricting the original action along `originTransport i o`. -/
local instance extendedAction : DistribMulAction (FiberAutGroup (extensionPoint i ≫ o)) M :=
  restrictedAction M (originTransport i o)
local instance extendedContinuous : ContinuousSMul (FiberAutGroup (extensionPoint i ≫ o)) M :=
  restrictedAction_continuous M (originTransport i o)

/-- The extended-point marking is literal actual coefficient-point transport. -/
def extendedMark : (Over.mk (extensionPoint i ≫ o) ⟶ A.X) ≃* Multiplicative M :=
  (coefficientPointEquiv i o A).symm.trans mark

omit [GaloisCategory (Scheme.FiniteEtale X)]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (FieldGalois.geometricPoint F ≫ o))]
  [IsCommMonObj A.X] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (FiberAutGroup (FieldGalois.geometricPoint F ≫ o)) M] in
include hmark in
theorem extendedMark_equivariant (g : FiberAutGroup (extensionPoint i ≫ o))
    (x : Over.mk (extensionPoint i ≫ o) ⟶ A.X) :
    extendedMark i o A M mark (g.hom.app (coefficientCover A) x) =
      Multiplicative.ofAdd (g • (extendedMark i o A M mark x).toAdd) := by
  let y := (coefficientPointEquiv i o A).symm x
  have h := originFiberComparison_equivariant i o g (coefficientCover A) y
  change coefficientPointEquiv i o A ((originTransport i o g).hom.app (coefficientCover A) y) =
    g.hom.app (coefficientCover A) (coefficientPointEquiv i o A y) at h
  have h' := congrArg (extendedMark i o A M mark) h
  simp only [extendedMark, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h'
  have hm := hmark (originTransport i o g) y
  change mark ((coefficientPointEquiv i o A).symm (g.hom.app (coefficientCover A) x)) =
    Multiplicative.ofAdd ((originTransport i o g) •
      (mark ((coefficientPointEquiv i o A).symm x)).toAdd)
  simpa only [y, MulEquiv.apply_symm_apply] using h'.symm.trans hm

omit [IsCommMonObj A.X] [GaloisCategory (Scheme.FiniteEtale X)]
  [PreGaloisCategory.FiberFunctor (fiberToFinite (FieldGalois.geometricPoint F ≫ o))] in
/-- Positive scheme-torsor transport commutes with the same actual closure arrow. -/
theorem transport_point (Y : Scheme.FiniteEtale X) (τ : TorsorAction A (toUnit Y.obj))
    (t u : Fiber (FieldGalois.geometricPoint F ≫ o) Y) :
    coefficientPointEquiv i o A (transport (FieldGalois.geometricPoint F ≫ o) A Y τ t u) =
    transport (extensionPoint i ≫ o) A Y τ (pointEquiv i o Y t) (pointEquiv i o Y u) := by
  apply transport_unique (extensionPoint i ≫ o) A Y τ
  rw [coefficientPointEquiv_apply, pointEquiv_apply, pointEquiv_apply, ← τ.naturality,
    transport_act]

variable [PreconnectedSpace X] [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Actual positive cocycles agree under the constructed origin-group restriction. -/
theorem markedCocycle_point (Y : Scheme.FiniteEtale X) (τ : TorsorAction A (toUnit Y.obj))
    (t : Fiber (FieldGalois.geometricPoint F ≫ o) Y) :
    markedBasedCocycle (extensionPoint i ≫ o) A M (extendedMark i o A M mark)
      (extendedMark_equivariant i o A M mark hmark) Y τ (pointEquiv i o Y t) =
    restrictionCocycles M (originTransport i o)
      (markedBasedCocycle (FieldGalois.geometricPoint F ≫ o) A M mark hmark Y τ t) := by
  apply Cocycle.ext
  intro g
  rw [markedBasedCocycle_apply, restrictionCocycles_apply, markedBasedCocycle_apply]
  have he := originFiberComparison_equivariant i o g Y t
  change pointEquiv i o Y ((originTransport i o g).hom.app Y t) =
    g.hom.app Y (pointEquiv i o Y t) at he
  rw [← he, ← transport_point]
  change (mark ((coefficientPointEquiv i o A).symm (coefficientPointEquiv i o A _))).toAdd = _
  rw [MulEquiv.symm_apply_apply]

variable (hA : Stacks03AJ.{u, w} X) (hR : Stacks03RV X)
variable (hcoeff : FiniteCoefficient (representedSheaf A))

/-- For every actual small-etale H1 class, changing the actual closed geometric
origin agrees with restriction through the derived actual continuous group map. -/
theorem representedH1_point (a : H1Etale.{u, u + 1, w} X (representedSheaf A)) :
    representedH1AddEquiv (extensionPoint i ≫ o) A hA hR M (extendedMark i o A M mark)
      (extendedMark_equivariant i o A M mark hmark) hcoeff a =
    restriction M (originTransport i o)
      (representedH1AddEquiv (FieldGalois.geometricPoint F ≫ o) A hA hR M mark hmark hcoeff a) := by
  obtain ⟨p, rfl⟩ := (hA.bijective (representedSheaf A)).surjective a
  refine Quotient.inductionOn p ?_
  intro P
  let Y :=
    _root_.AlgebraicGeometry.Scheme.EtaleCohomology.Torsor.finiteEtaleRepresentative
      (P := P) hR hcoeff.locally_constant
  let e :=
    _root_.AlgebraicGeometry.Scheme.EtaleCohomology.Torsor.finiteEtaleRepresentativeIso
      (P := P) hR hcoeff.locally_constant
  let τ :=
    _root_.AlgebraicGeometry.Scheme.EtaleCohomology.Torsor.representedSchemeAction
      (H := A) (P := P) (Y := Y) (e := e)
  let : Surjective Y.obj.hom :=
    _root_.AlgebraicGeometry.Scheme.EtaleCohomology.Torsor.represented_surjective
      (H := A) (P := P) (Y := Y) (e := e)
  have he : torsorExtClass (torsorOfSchemeAction A Y τ) = torsorExtClass P :=
    torsorExtClass_iso
      (_root_.AlgebraicGeometry.Scheme.EtaleCohomology.Torsor.representedSchemeActionIso
        (H := A) (P := P) (Y := Y) (e := e))
  let : Nonempty (Fiber (FieldGalois.geometricPoint F ≫ o) Y) :=
    SchemeTorsorClassification.nonempty_fiber_of_surjective (FieldGalois.geometricPoint F ≫ o) Y
  let t : Fiber (FieldGalois.geometricPoint F ≫ o) Y := Classical.choice inferInstance
  change representedH1AddEquiv (extensionPoint i ≫ o) A hA hR M _ _ hcoeff (torsorExtClass P) =
    restriction M (originTransport i o)
      (representedH1AddEquiv (FieldGalois.geometricPoint F ≫ o) A hA hR M mark hmark hcoeff
        (torsorExtClass P))
  rw [← he,
    MarkedComparisonTransport.representedH1AddEquiv_schemeAction (extensionPoint i ≫ o) A M
      (extendedMark i o A M mark) (extendedMark_equivariant i o A M mark hmark)
      hA hR hcoeff Y τ (pointEquiv i o Y t),
    MarkedComparisonTransport.representedH1AddEquiv_schemeAction (FieldGalois.geometricPoint F ≫
      o) A M
      mark hmark hA hR hcoeff Y τ t,
    restriction_classOf]
  congr 1
  exact markedCocycle_point i o A M mark hmark Y τ t

end AlgebraicGeometry.Scheme.EtaleCohomology.PointedFieldTransport

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 f69b3952b05d8e6f66b1db9791dd016451575a98e96632c103ed87a97d280e48.
Definitions, hypotheses and universes are retained modulo native names. -/
