/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.RepresentativeEquation
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.StageOverlapEquality

/-! # Genuine common-stage matching from original finite representative data

The original named local equations are opened at an independent scheme-cone
boundary, before specializing to a relative scheme diagram. The result is the
actual overlap matching at a genuine later stage, not a continuity premise.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u v

open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

/-- Named original representative equations have matching overlaps at a later
stage. The local data are independent fields, not projections of a dependent
record whose section maps must be normalized during this proof. -/
theorem exists_stage_overlap_matching_of_representative_equations
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, IsAffine (D.obj i)] (i : I) {X : Scheme.{u}} (r : D.obj i ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) {J : Type v} [Finite J]
    (W : J → Over (D.obj i)) [∀ j, IsAffine (W j).left]
    (U : J → X.Etale) (a : ∀ j, (W j).left ⟶ (U j).left)
    (ha : ∀ j, a j ≫ (U j).hom = (W j).hom ≫ r)
    (t : ∀ j, F.obj.obj (op (U j)))
    (f : c.pt ⟶ X) (hf : c.π.app i ≫ r = f)
    (s : (pullbackSectionsFunctor F).obj (op (Over.mk f)))
    (hs : ∀ j, IsBaseChangeSectionRepresentative (c.π.app i) r f hf
      F (W j) (U j) (a j) (ha j) s (t j)) :
    ∃ k : Over i, BaseChangeOverlapMatching (D.map k.hom) r F W U a ha t := by
  exact exists_stage_overlap_matching D c hc i r F W U a ha t
    ((pullbackSectionsFunctor F).map (relativeSourceEquality hf).op s)
    (fun j ↦ (hs j).eq)

end AlgebraicGeometry.Scheme.EtaleAffineBasis
