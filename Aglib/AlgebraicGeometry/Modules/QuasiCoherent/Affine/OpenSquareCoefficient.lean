/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.OpenSquareComposition

/-! # Actual coefficient comparison under an open refinement

This is a cancellation consequence of the existing original open-square
composition law. In particular the refined coefficient is restriction along
the composite ambient chart, not a silently identified iterated restriction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The actual refined coefficient comparison followed by its local correction
is the original coefficient comparison restricted to the smaller chart. -/
@[reassoc]
theorem pullbackOpenSquare_refined_coefficient
    {W X V Y W' V' : Scheme.{u}}
    (p : W ⟶ X) (q : W ⟶ V) (f : X ⟶ Y) (a : V ⟶ Y)
    [IsOpenImmersion p] [IsOpenImmersion a]
    (c : W' ⟶ W) (d : V' ⟶ V) (r : W' ⟶ V')
    [IsOpenImmersion c] [IsOpenImmersion d]
    (wp : p ≫ f = q ≫ a) (wc : c ≫ q = r ≫ d)
    (wt : (c ≫ p) ≫ f = r ≫ (d ≫ a)) (E : Y.Modules) :
    let η := (restrictFunctorComp d a).app E
    let coefficientIso := (pullback r).mapIso η ≪≫
      ((pullbackOpenSquare c r q d wc).app (E.restrict a)).symm
    (pullbackOpenSquare (c ≫ p) r f (d ≫ a) wt).hom.app E ≫ coefficientIso.hom =
      (restrictFunctorComp c p).hom.app ((pullback f).obj E) ≫
        (restrictFunctor c).map ((pullbackOpenSquare p q f a wp).hom.app E) := by
  have hmap :
      (pullback r).map ((restrictFunctorComp d a).inv.app E) ≫
          (pullback r).map ((restrictFunctorComp d a).hom.app E) =
        𝟙 ((pullback r).obj ((restrictFunctor a ⋙ restrictFunctor d).obj E)) :=
    ((pullback r).mapIso ((restrictFunctorComp d a).app E)).inv_hom_id
  have hsquare :
      (pullbackOpenSquare c r q d wc).hom.app (E.restrict a) ≫
          (pullbackOpenSquare c r q d wc).inv.app (E.restrict a) =
        𝟙 ((restrictFunctor c).obj ((pullback q).obj (E.restrict a))) :=
    ((pullbackOpenSquare c r q d wc).app (E.restrict a)).hom_inv_id
  dsimp only
  rw [pullbackOpenSquare_comp_hom_app p q f a c d r wp wc wt E]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
    Iso.app_inv, Category.assoc]
  simp only [reassoc_of% hmap, hsquare]
  have ht : (restrictFunctor c).map ((pullbackOpenSquare p q f a wp).hom.app E) ≫
        𝟙 ((restrictFunctor c).obj ((pullback q).obj (E.restrict a))) =
      (restrictFunctor c).map ((pullbackOpenSquare p q f a wp).hom.app E) :=
    Category.comp_id (obj := W'.Modules)
      ((restrictFunctor c).map ((pullbackOpenSquare p q f a wp).hom.app E))
  exact congrArg
    (fun z : (restrictFunctor c).obj
        ((restrictFunctor p).obj ((pullback f).obj E)) ⟶
          (restrictFunctor c).obj ((pullback q).obj (E.restrict a)) =>
      (restrictFunctorComp c p).hom.app ((pullback f).obj E) ≫ z) ht

end AlgebraicGeometry.Scheme.Modules
