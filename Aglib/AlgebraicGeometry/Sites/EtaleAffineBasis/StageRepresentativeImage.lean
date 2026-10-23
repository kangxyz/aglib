/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.StageSectionImageExistence
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.RepresentativeEquation
/-! # Stage sections with their original prescribed limit image -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleAffineBasis
universe u v
open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

/-- Named original representative equations give a stage section with the transported image. -/
theorem exists_stage_section_of_representative_equations
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i)] (i : I) {X : Scheme.{u}} (r : D.obj i ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) {J : Type v} [Finite J]
    (W : J → Over (D.obj i)) [∀ j, IsAffine (W j).left] [∀ j, Etale (W j).hom]
    (hcover : ∀ x : D.obj i, ∃ j, ∃ y : (W j).left, (W j).hom y = x)
    (U : J → X.Etale) (a : ∀ j, (W j).left ⟶ (U j).left)
    (ha : ∀ j, a j ≫ (U j).hom = (W j).hom ≫ r)
    (t : ∀ j, F.obj.obj (op (U j)))
    (f : c.pt ⟶ X) (hf : c.π.app i ≫ r = f)
    (s : (pullbackSectionsFunctor F).obj (op (Over.mk f)))
    (hs : ∀ j, IsBaseChangeSectionRepresentative (c.π.app i) r f hf
      F (W j) (U j) (a j) (ha j) s (t j)) :
    ∃ (k : Over i)
      (v : (pullbackSectionsFunctor F).obj (op (Over.mk (D.map k.hom ≫ r)))),
      (pullbackSectionsFunctor F).map
        (Over.homMk (c.π.app k.left)
          ((Category.assoc _ _ _).symm.trans (congrArg (fun z ↦ z ≫ r) (c.w k.hom)))
          (U := Over.mk (c.π.app i ≫ r)) (V := Over.mk (D.map k.hom ≫ r))).op v =
      (pullbackSectionsFunctor F).map (relativeSourceEquality hf).op s := by
  exact exists_stage_section_with_prescribed_image D c hc i r F W hcover U a ha t
    ((pullbackSectionsFunctor F).map (relativeSourceEquality hf).op s)
    (fun j ↦ (hs j).eq)
end AlgebraicGeometry.Scheme.EtaleAffineBasis
