/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.RepresentativeSections
public import Mathlib.CategoryTheory.Sites.Whiskering

/-! # Pairwise compatibility on actual scheme overlaps -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u v

open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

private theorem relativeSections_compatible_for_functor
    {X S : Scheme.{u}} (f : S ⟶ X) (P : (Over X)ᵒᵖ ⥤ Ab.{u + 1})
    {J : Type v} (W : J → S.Etale)
    (z : ∀ j, ((Etale.forget S ⋙ Over.map f).op ⋙ P).obj (op (W j)))
    (h : ∀ j k,
      P.map (Over.homMk (pullback.fst (W j).hom (W k).hom)
        (U := Over.mk (pullback.fst (W j).hom (W k).hom ≫ (W j).hom ≫ f))
        (V := Over.mk ((W j).hom ≫ f))).op (z j) =
      P.map (Over.homMk (pullback.snd (W j).hom (W k).hom)
        (U := Over.mk (pullback.fst (W j).hom (W k).hom ≫ (W j).hom ≫ f))
        (V := Over.mk ((W k).hom ≫ f))
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun a ↦ a ≫ f) pullback.condition.symm).trans
            (Category.assoc _ _ _)))).op (z k)) :
    Presieve.Arrows.Compatible
      (((Etale.forget S ⋙ Over.map f).op ⋙ P) ⋙ CategoryTheory.forget Ab.{u + 1})
      (fun j ↦ (etaleTerminalIsTerminal S).from (W j)) z := by
  intro j k T a b _
  have hab : a.left ≫ (W j).hom = b.left ≫ (W k).hom :=
    (MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm
  let g := pullback.lift a.left b.left hab
  let A : Over.mk (T.hom ≫ f) ⟶
      Over.mk (pullback.fst (W j).hom (W k).hom ≫ (W j).hom ≫ f) :=
    Over.homMk g (by
      change g ≫ ((pullback.fst (W j).hom (W k).hom ≫ (W j).hom) ≫ f) =
        T.hom ≫ f
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun q ↦ q ≫ f)
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun q ↦ q ≫ (W j).hom)
              (pullback.lift_fst a.left b.left hab)).trans
                (MorphismProperty.Over.w a)))))
  let p : Over.mk (pullback.fst (W j).hom (W k).hom ≫ (W j).hom ≫ f) ⟶
      Over.mk ((W j).hom ≫ f) := Over.homMk (pullback.fst (W j).hom (W k).hom)
  let q : Over.mk (pullback.fst (W j).hom (W k).hom ≫ (W j).hom ≫ f) ⟶
      Over.mk ((W k).hom ≫ f) := Over.homMk (pullback.snd (W j).hom (W k).hom)
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun a ↦ a ≫ f) pullback.condition.symm).trans
            (Category.assoc _ _ _)))
  have hA : A ≫ p = (Etale.forget S ⋙ Over.map f).map a := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  have hB : A ≫ q = (Etale.forget S ⋙ Over.map f).map b := by
    apply Over.OverMorphism.ext
    exact pullback.lift_snd _ _ _
  have heq := congrArg (P.map A.op) (h j k)
  have hp := ConcreteCategory.congr_hom (P.map_comp p.op A.op) (z j)
  have hq := ConcreteCategory.congr_hom (P.map_comp q.op A.op) (z k)
  exact (congrArg (fun a ↦ P.map a.op (z j)) hA).symm.trans
    (hp.trans (heq.trans (hq.symm.trans
      (congrArg (fun a ↦ P.map a.op (z k)) hB))))

/-- Relative section data on etale charts is compatible when its restrictions
agree on the actual scheme fiber products. This avoids replacing those fiber
products by a second choice of site pullbacks. -/
theorem relativeSections_compatible_of_scheme_pullbacks
    {X S : Scheme.{u}} (f : S ⟶ X) (F : AbelianSheaf.{u, u + 1} X)
    {J : Type v} (W : J → S.Etale)
    (z : ∀ j, ((Etale.forget S ⋙ Over.map f).op ⋙ pullbackSectionsFunctor F).obj (op (W j)))
    (h : ∀ j k,
      (pullbackSectionsFunctor F).map
        (Over.homMk (pullback.fst (W j).hom (W k).hom)
          (U := Over.mk (pullback.fst (W j).hom (W k).hom ≫ (W j).hom ≫ f))
          (V := Over.mk ((W j).hom ≫ f))).op (z j) =
      (pullbackSectionsFunctor F).map
        (Over.homMk (pullback.snd (W j).hom (W k).hom)
          (U := Over.mk (pullback.fst (W j).hom (W k).hom ≫ (W j).hom ≫ f))
          (V := Over.mk ((W k).hom ≫ f))
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun a ↦ a ≫ f) pullback.condition.symm).trans
              (Category.assoc _ _ _)))).op (z k)) :
    Presieve.Arrows.Compatible
      (((Etale.forget S ⋙ Over.map f).op ⋙ pullbackSectionsFunctor F) ⋙
        CategoryTheory.forget Ab.{u + 1})
      (fun j ↦ (etaleTerminalIsTerminal S).from (W j)) z := by
  exact relativeSections_compatible_for_functor f (pullbackSectionsFunctor F) W z h

end AlgebraicGeometry.Scheme.EtaleAffineBasis
