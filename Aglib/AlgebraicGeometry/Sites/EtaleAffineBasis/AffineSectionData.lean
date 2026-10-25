/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.FiniteRepresentativeCover
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.MappedCoverModel
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.RepresentativeEquation
/-! # Actual finite representative data for a section on an affine limit -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleAffineBasis
universe u
open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

/-- Finite stage data, including the actual original section equations. -/
structure AffineSectionData {I : Type u} [Category.{u} I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (i : I) {X : Scheme.{u}} (r : D.obj i ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X)
    (s : (pullbackSectionsFunctor F).obj (op (Over.mk (Y := c.pt) (c.π.app i ≫ r)))) where
  /-- The actual common stage carrying all representatives. -/
  stage : I
  /-- The original transition to the specified stage. -/
  toStage : stage ⟶ i
  /-- The labels of the finite descended covering family. -/
  index : Type u
  finite : Finite index
  /-- The actual descended cover over the common stage. -/
  cover : index → Over (D.obj stage)
  affine : ∀ j, IsAffine (cover j).left
  etale : ∀ j, Etale (cover j).hom
  covers : ∀ x : D.obj stage, ∃ j, ∃ y : (cover j).left, (cover j).hom y = x
  /-- The original etale test objects representing the section. -/
  chart : index → X.Etale
  /-- The actual maps from covering charts to the original test objects. -/
  representative : ∀ j, (cover j).left ⟶ (chart j).left
  /-- The literal original coefficient section on each test object. -/
  value : ∀ j, F.obj.obj (op (chart j))
  triangle : ∀ j, representative j ≫ (chart j).hom =
    (cover j).hom ≫ (D.map toStage ≫ r)
  equation : ∀ j, IsBaseChangeSectionRepresentative (S := c.pt)
    (c.π.app stage) (D.map toStage ≫ r) (c.π.app i ≫ r)
    ((Category.assoc _ _ _).symm.trans (congrArg (fun z ↦ z ≫ r) (c.w toStage)))
    F (cover j) (chart j) (representative j) (triangle j) s (value j)


/-- Construct the finite data from actual local representatives and geometric descent. -/
def affineSectionData {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i)] (i : I) {X : Scheme.{u}} (r : D.obj i ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X)
    (s : (pullbackSectionsFunctor F).obj (op (Over.mk (Y := c.pt) (c.π.app i ≫ r)))) :
    AffineSectionData D c i r F s := Classical.choice (by
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  obtain ⟨J, hJ, Y, hY, heY, hcover, U, a, t, ht⟩ :=
    exists_finite_representative_cover (S := c.pt) (c.π.app i ≫ r) F s
  have : Finite J := hJ
  have (j : J) : IsAffine (Y j).left := hY j
  have (j : J) : Etale (Y j).hom := heY j
  let M := mappedCoverModel D c hc i r Y hcover U
    (fun j ↦ (a j).left) (fun j ↦ Over.w (a j))
  refine ⟨⟨M.stage, M.toStage, J, hJ, M.cover, M.affine, M.etale, M.covers,
    U, M.representative, t, M.representative_w, ?_⟩⟩
  exact mappedCover_section_representatives (S := c.pt) (T := D.obj M.stage)
    (X := X) (c.π.app M.stage) (D.map M.toStage ≫ r) (c.π.app i ≫ r) _
    F Y M.cover U a M.representative M.representative_w M.refinement
    M.refinement_w M.refinement_representative s t ht)
end AlgebraicGeometry.Scheme.EtaleAffineBasis
