/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Grp.Ulift

/-! # Typed additive component transport -/

@[expose] public noncomputable section

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

/-- Lift an actual additive map before specializing its carriers. -/
def liftSectionAddHom {A B : Type u} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) :
    AddCommGrpCat.of (ULift.{v} A) ⟶ AddCommGrpCat.of (ULift.{v} B) :=
  AddCommGrpCat.ofHom {
    toFun s := ⟨f s.down⟩
    map_zero' := ULift.ext _ _ (map_zero f)
    map_add' s t := ULift.ext _ _ (map_add f s.down t.down) }

/-- Lift an actual additive equivalence before specializing its carriers. -/
def liftSectionAddIso {A B : Type u} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) :
    AddCommGrpCat.of (ULift.{v} A) ≅ AddCommGrpCat.of (ULift.{v} B) :=
  AddEquiv.toAddCommGrpIso (AddEquiv.ulift.trans (e.trans AddEquiv.ulift.symm))

/-- Construct additive natural transformations from their literal component equations. -/
def sectionNatTrans {C : Type*} [Category* C] (P Q : C ⥤ AddCommGrpCat.{u})
    (a : ∀ T, P.obj T ⟶ Q.obj T)
    (h : ∀ {T U} (f : T ⟶ U) (s : P.obj T), a U (P.map f s) = Q.map f (a T s)) :
    P ⟶ Q where
  app := a
  naturality {T U} f := by ext s; exact h f s

/-- Construct additive natural isomorphisms from their literal component equations. -/
def sectionNatIso {C : Type*} [Category* C] (P Q : C ⥤ AddCommGrpCat.{u})
    (e : ∀ T, P.obj T ≅ Q.obj T)
    (h : ∀ {T U} (f : T ⟶ U) (s : P.obj T),
      (e U).hom (P.map f s) = Q.map f ((e T).hom s)) : P ≅ Q :=
  NatIso.ofComponents e (by intro T U f; ext s; exact h f s)

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
