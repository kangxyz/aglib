/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Opposites

/-! # Sections transported from a selected natural evaluation isomorphism

A representative section is the inverse of the selected evaluation comparison
followed by restriction along the supplied arrow. Restriction, refinement and
equality detected by a family use only functoriality and naturality.
-/

@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

open Opposite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {A : Type u₃} [Category.{v₃} A] {FA : A → A → Type*} {CA : A → Type w}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
  (L : C ⥤ D) (R : Dᵒᵖ ⥤ A) {P : Cᵒᵖ ⥤ A} (e : L.op ⋙ R ≅ P)

/-- Transport a section by the selected evaluation inverse and the given restriction. -/
def representativeSection {Y : D} (U : C) (a : Y ⟶ L.obj U)
    (s : ToType (P.obj (op U))) : ToType (R.obj (op Y)) :=
  R.map a.op ((e.app (op U)).inv s)

/-- Restricting a representative retains the literal composite of its arrows. -/
lemma representativeSection_restrict {Y Z : D} (g : Z ⟶ Y) (U : C)
    (a : Y ⟶ L.obj U) (s : ToType (P.obj (op U))) :
    R.map g.op (representativeSection L R e U a s) =
      representativeSection L R e U (g ≫ a) s := by
  simpa only [representativeSection, op_comp, ConcreteCategory.comp_apply] using
    (ConcreteCategory.congr_hom (R.map_comp a.op g.op) ((e.app (op U)).inv s)).symm

/-- Refining a representative uses the original presheaf restriction. -/
lemma representativeSection_refine {Y : D} {T U : C} (p : T ⟶ U)
    (a : Y ⟶ L.obj T) (s : ToType (P.obj (op U))) :
    representativeSection L R e U (a ≫ L.map p) s =
      representativeSection L R e T a (P.map p.op s) := by
  calc
    representativeSection L R e U (a ≫ L.map p) s =
        R.map a.op (R.map (L.map p).op ((e.app (op U)).inv s)) := by
      simpa only [representativeSection, op_comp, ConcreteCategory.comp_apply] using
        (ConcreteCategory.congr_hom (R.map_comp (L.map p).op a.op)
          ((e.app (op U)).inv s))
    _ = representativeSection L R e T a (P.map p.op s) :=
      congrArg (R.map a.op) (NatTrans.naturality_apply e.inv p.op s).symm

/-- Common coefficient witnesses prove equality when the supplied restrictions detect it. -/
theorem representativeSection_eq_of_witnesses {Y : D} {J : Type*} {W : J → D}
    (g : ∀ j, W j ⟶ Y)
    (hsep : ∀ (x y : ToType (R.obj (op Y))),
      (∀ j, R.map (g j).op x = R.map (g j).op y) → x = y)
    (U V : C) (a : Y ⟶ L.obj U) (b : Y ⟶ L.obj V)
    (s : ToType (P.obj (op U))) (t : ToType (P.obj (op V)))
    (T : J → C) (p : ∀ j, T j ⟶ U) (q : ∀ j, T j ⟶ V)
    (c : ∀ j, W j ⟶ L.obj (T j))
    (hp : ∀ j, c j ≫ L.map (p j) = g j ≫ a)
    (hq : ∀ j, c j ≫ L.map (q j) = g j ≫ b)
    (hst : ∀ j, P.map (p j).op s = P.map (q j).op t) :
    representativeSection L R e U a s = representativeSection L R e V b t := by
  apply hsep
  intro j
  exact (representativeSection_restrict L R e (g j) U a s).trans
    ((congrArg (fun z ↦ representativeSection L R e U z s) (hp j).symm).trans
      ((representativeSection_refine L R e (p j) (c j) s).trans
        ((congrArg (representativeSection L R e (T j) (c j)) (hst j)).trans
          ((representativeSection_refine L R e (q j) (c j) t).symm.trans
            ((congrArg (fun z ↦ representativeSection L R e V z t) (hq j)).trans
              (representativeSection_restrict L R e (g j) V b t).symm)))))

end CategoryTheory.Functor
