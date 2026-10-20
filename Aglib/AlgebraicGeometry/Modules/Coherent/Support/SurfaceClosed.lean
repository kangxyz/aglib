/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Dimension.CodimensionTwoClosed
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.ClosedPoints
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.HeightSlice
public import Aglib.AlgebraicGeometry.Dimension.CodimensionTwo
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.ClosedResidue

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Support.SurfaceClosed` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`6175066499df0535bab4e719ff4fc6abf815c8356507d7f086fc9573fb152961`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules (support)
open _root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent (FiniteTypeSheaves
    finiteType_support_isClosed)
open AlgebraicGeometry.Scheme.Modules.Coherent.Support
    AlgebraicGeometry.Scheme.Modules.Coherent.Support
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules.Coherent.Support
open AlgebraicGeometry.Scheme.Modules.Coherent.Support
    AlgebraicGeometry.Scheme.Modules.Coherent.Support
attribute [local instance] Abelian.hasFiniteBiproducts Classical.decEq
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Support
universe u
variable (X : Scheme.{u}) [IsNoetherian X] [IsIntegral X]

/-- The exact codimension-two CLOSED index and actual original residue maps. -/
def surfaceClosedFamily : ClosedFieldFamily X where
  Index := CodimensionTwoClosedPoint X
  field x := X.residueField x.1
  fieldInstance _ := inferInstance
  point := Subtype.val
  point_injective := Subtype.val_injective
  point_closed x := x.2.2
  immersion x := X.fromSpecResidueField x.1
  closedImmersion x := closedResidueMap_isClosedImmersion X x
  immersion_apply x y := X.fromSpecResidueField_apply x.1 y

omit [AlgebraicGeometry.IsNoetherian X] [IsIntegral X] in
@[simp] theorem mem_surfacePointSet (x : X) :
    x ∈ pointSet X (surfaceClosedFamily X) ↔
      ringKrullDim (X.presheaf.stalk x) = 2 ∧ IsClosed ({x} : Set X) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

omit [AlgebraicGeometry.IsNoetherian X] in
theorem generic_not_surfacePointSet :
    genericPoint X ∉ pointSet X (surfaceClosedFamily X) := by
  intro h
  have hd := ((mem_surfacePointSet X _).mp h).1
  have hz : ringKrullDim (X.presheaf.stalk (genericPoint X)) = 0 := by
    change ringKrullDim X.functionField = 0
    simp
  rw [hz] at hd
  norm_num at hd

omit [AlgebraicGeometry.IsNoetherian X] [IsIntegral X] in
theorem heightOne_not_surfacePointSet (x : CodimensionOnePoint X) :
    x.1 ∉ pointSet X (surfaceClosedFamily X) := by
  intro h
  have hd := ((mem_surfacePointSet X _).mp h).1
  rw [x.2] at hd
  norm_num at hd

/-- The forward support dictionary. The dimension bound, and no normality,
is used precisely to exclude all remaining support points. -/
theorem secondSupport_lands_closedSupport (hdim : SurfaceDimensionAtMostTwo X)
    (N : (secondSupport X).FullSubcategory) :
    supportOn X (pointSet X (surfaceClosedFamily X)) N.obj.obj := by
  intro x
  have hx2 : ringKrullDim (X.presheaf.stalk x.1) < 2 := by
    apply lt_of_le_of_ne (hdim x.1)
    intro heq
    exact x.2 ((mem_surfacePointSet X x.1).mpr
      ⟨heq, codimensionTwoPointsClosed_of_dimension X hdim x.1 heq⟩)
  have hx1 : ringKrullDim (X.presheaf.stalk x.1) ≤ 1 :=
    ENat.WithBot.lt_add_one_iff.mp (by norm_num; exact hx2)
  rcases lt_or_eq_of_le hx1 with hlt | heq
  · apply (smallStalk_kernel_iff X N.obj.obj x.1).mpr
    have hz := (smallStalk_kernel_iff X N.obj.obj (genericPoint X)).mp N.obj.property
    simpa only [eq_genericPoint_of_height_lt_one X x.1 hlt] using hz
  · exact N.property ⟨x.1, heq⟩

/-- The converse dictionary retains both actual support-kernel conditions. -/
theorem closedSupport_lands_positive
    (N : CohSupportOn X (pointSet X (surfaceClosedFamily X))) :
    positiveSupport X N.obj :=
  N.property ⟨genericPoint X, generic_not_surfacePointSet X⟩

theorem closedSupport_lands_second
    (N : CohSupportOn X (pointSet X (surfaceClosedFamily X))) :
    secondSupport X ⟨N.obj, closedSupport_lands_positive X N⟩ := by
  intro x
  exact N.property ⟨x.1, heightOne_not_surfacePointSet X x⟩

/-- The represented actual C2 sheaf has finite support in the correct point
index. In particular this does not identify C2 with all closed finite support. -/
theorem secondSupport_finite_closedSupport (hdim : SurfaceDimensionAtMostTwo X)
    (N : (secondSupport X).FullSubcategory) :
    (support ((equivSmallModel.{u + 1} (FiniteTypeSheaves X)).inverse.obj
        N.obj.obj).obj).Finite := by
  let N' := (equivSmallModel.{u + 1} (FiniteTypeSheaves X)).inverse.obj N.obj.obj
  have hs := (supportOn_iff X _ N.obj.obj).mp (secondSupport_lands_closedSupport X hdim N)
  have hf := finite_closed_height_slice X (support N'.obj) (finiteType_support_isClosed N') 2
    (fun x hx => by
      have hd := ((mem_surfacePointSet X x).mp (hs hx)).1
      rw [ringKrullDim_stalk_eq_coheight] at hd
      exact le_of_eq (WithBot.coe_injective hd).symm)
  apply hf.subset
  intro x hx
  refine ⟨hx, ?_⟩
  have hd := ((mem_surfacePointSet X x).mp (hs hx)).1
  rw [ringKrullDim_stalk_eq_coheight] at hd
  exact WithBot.coe_injective hd

/-- Flatten the two actual nested full subcategories, retaining the same
coherent object and morphism. -/
def secondToClosedSupport (hdim : SurfaceDimensionAtMostTwo X) :
    (secondSupport X).FullSubcategory ⥤ CohSupportOn X (pointSet X (surfaceClosedFamily X)) where
  obj N := ⟨N.obj.obj, secondSupport_lands_closedSupport X hdim N⟩
  map f := ObjectProperty.homMk f.hom.hom

instance secondToClosedSupport_full (hdim : SurfaceDimensionAtMostTwo X) :
    (secondToClosedSupport X hdim).Full where
  map_surjective f := ⟨ObjectProperty.homMk (ObjectProperty.homMk f.hom), rfl⟩

instance secondToClosedSupport_faithful (hdim : SurfaceDimensionAtMostTwo X) :
    (secondToClosedSupport X hdim).Faithful where
  map_injective h := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact congrArg (fun f => f.hom) h

instance secondToClosedSupport_essSurj (hdim : SurfaceDimensionAtMostTwo X) :
    (secondToClosedSupport X hdim).EssSurj where
  mem_essImage N :=
    ⟨⟨⟨N.obj, closedSupport_lands_positive X N⟩, closedSupport_lands_second X N⟩,
      ⟨ObjectProperty.isoMk _ (Iso.refl _)⟩⟩

instance secondToClosedSupport_isEquivalence (hdim : SurfaceDimensionAtMostTwo X) :
    (secondToClosedSupport X hdim).IsEquivalence := {}

instance secondToClosedSupport_additive (hdim : SurfaceDimensionAtMostTwo X) :
    (secondToClosedSupport X hdim).Additive where
  map_add := by intros; rfl

def secondToClosedSupportExact (hdim : SurfaceDimensionAtMostTwo X) :
    _root_.CategoryTheory.ExactCategory.ExactFunctor
    (_root_.CategoryTheory.ObjectProperty.subcategoryExactStructure (secondSupport X))
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (CohSupportOn X (pointSet X
        (surfaceClosedFamily X)))) where
  toFunctor := secondToClosedSupport X hdim
  map_conflation _ h := h.map_of_exact _

instance secondToClosedSupportExact_isEquivalence (hdim : SurfaceDimensionAtMostTwo X) :
    (secondToClosedSupportExact X hdim).toFunctor.IsEquivalence :=
  secondToClosedSupport_isEquivalence X hdim

end AlgebraicGeometry.Scheme.Modules.Coherent.Support
