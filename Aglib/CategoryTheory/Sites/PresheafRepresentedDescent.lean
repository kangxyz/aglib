/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Yoneda

/-! A represented restriction of a presheaf carries its actual descent action. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Category Opposite

namespace CategoryTheory.PresheafRepresentedDescent

universe w v v' u u'
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
variable (H : Dᵒᵖ ⥤ Type (max w v)) {Y : C}
variable (e : uliftYoneda.{w}.obj Y ≅ L.op ⋙ H)

/-- The supplied represented restriction, as an equivalence on each test object. -/
def sectionEquiv (Z : C) : (Z ⟶ Y) ≃ H.obj (op (L.obj Z)) :=
  Equiv.ulift.symm.trans (e.app (op Z)).toEquiv

lemma sectionEquiv_naturality {Z Z' : C} (f : Z' ⟶ Z) (g : Z ⟶ Y) :
    sectionEquiv H e Z' (f ≫ g) = H.map (L.map f).op (sectionEquiv H e Z g) := by
  exact congrArg (fun k => k (ULift.up g)) (e.hom.naturality f.op)

/-- The section of `H` at `L.obj Y` corresponding to `𝟙 Y` under the supplied
representation isomorphism `e`. -/
def sectionValue : H.obj (op (L.obj Y)) := sectionEquiv H e Y (𝟙 Y)

lemma sectionEquiv_eq {Z : C} (f : Z ⟶ Y) :
    sectionEquiv H e Z f = H.map (L.map f).op (sectionValue (L := L) H e) := by
  simpa [sectionValue] using sectionEquiv_naturality H e f (𝟙 Y)

/-- Pull the identity section along the adjunction counit, then use the local
representing object to obtain the actual descent-action morphism. -/
def action : R.obj (L.obj Y) ⟶ Y :=
  (sectionEquiv H e _).symm (H.map (adj.counit.app (L.obj Y)).op (sectionValue (L := L) H e))

lemma sectionEquiv_action :
    sectionEquiv H e _ (action adj H e) =
      H.map (adj.counit.app (L.obj Y)).op (sectionValue (L := L) H e) :=
  Equiv.apply_symm_apply _ _

lemma action_unit : adj.unit.app Y ≫ action adj H e = 𝟙 Y := by
  apply (sectionEquiv H e Y).injective
  rw [sectionEquiv_naturality]
  simp only [Functor.comp_obj, sectionEquiv_action adj H e]
  change H.map (L.map (adj.unit.app Y)).op
    (H.map (adj.counit.app (L.obj Y)).op (sectionValue (L := L) H e)) = sectionValue (L := L) H e
  rw [← Functor.map_comp_apply, ← op_comp, adj.left_triangle_components Y]
  simp

lemma action_assoc : R.map (adj.counit.app (L.obj Y)) ≫ action adj H e =
    R.map (L.map (action adj H e)) ≫ action adj H e := by
  apply (sectionEquiv H e _).injective
  rw [sectionEquiv_naturality, sectionEquiv_naturality]
  simp only [Functor.comp_obj, Functor.id_obj, sectionEquiv_action adj H e]
  have ha : H.map (L.map (action adj H e)).op (sectionValue (L := L) H e) =
      H.map (adj.counit.app (L.obj Y)).op (sectionValue (L := L) H e) :=
    (sectionEquiv_eq H e _).symm.trans (sectionEquiv_action adj H e)
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
    adj.counit_naturality, adj.counit_naturality]
  simpa only [op_comp, Functor.map_comp, types_comp_apply] using
    congrArg (fun z => H.map (adj.counit.app (L.obj (R.obj (L.obj Y)))).op z) ha.symm

/-- The descent action satisfies the monad laws; no effectiveness or global
representability assertion is assumed. -/
def algebra : adj.toMonad.Algebra where
  A := Y
  a := action adj H e
  unit := action_unit adj H e
  assoc := action_assoc adj H e

end CategoryTheory.PresheafRepresentedDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 b8ed7e1117b921a9fef83e36118cc6e291befae2cec0b4f39b7440f450d211f6.
Definitions, hypotheses and universes are retained modulo native names. -/
