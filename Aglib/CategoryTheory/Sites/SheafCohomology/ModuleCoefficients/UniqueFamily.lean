/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.FamilyProjective
public import Aglib.CategoryTheory.Sites.Hypercohomology.Basic

/-! # A unique-index family is the original representable

The actual family presheaf for a constant family with a unique index is the
original universe-lifted representable. The comparison retains the family map
and therefore identifies single-cover free sources without coproduct Ext
assumptions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Presheaf.Cech

universe c h w

variable {C : Type c} [Category.{h} C] (ι : Type w) [Unique ι] (U : C)

/-- The literal constant unique-index family is the original representable. -/
def uniqueFamilyIso : familyPresheaf (fun _ : ι => U) ≅ uliftYoneda.{w}.obj U :=
  NatIso.ofComponents (fun _ =>
    Equiv.toIso
      { toFun := fun a => ULift.up a.2
        invFun := fun a => ⟨default, a.down⟩
        left_inv := by
          rintro ⟨i, f⟩
          have hi : i = default := Subsingleton.elim _ _
          subst i
          rfl
        right_inv := by rintro ⟨f⟩; rfl })
    (by intro V W f; ext a; rfl)

/-- The unique-family comparison preserves the original map to the represented base. -/
theorem uniqueFamilyIso_hom_comp {W : C} (g : U ⟶ W) :
    (uniqueFamilyIso ι U).hom ≫ uliftYoneda.{w}.map g =
      familyMap (fun _ : ι => Over.mk g) := rfl

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max h w}]

/-- Sheafification and the original free functor preserve the unique-family
source identification. -/
def freeUniqueFamilyIso :
    (presheafToSheaf J AddCommGrpCat.{max h w}).obj
      (familyPresheaf (fun _ : ι => U) ⋙ AddCommGrpCat.free) ≅
        Sheaf.Hypercohomology.freeAbelianSheaf.{w} J U :=
  (presheafToSheaf J AddCommGrpCat).mapIso
    (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).mapIso (uniqueFamilyIso ι U))

/-- Each original free tuple term of a constant unique-index family is the
free sheaf represented by its actual product over the base. -/
def sheafComplexUniqueFamilyIso {W : C} (V : Over W)
    [HasFiniteProducts (Over W)] (n : ℕ) :
    (sheafComplex (familyMap (fun _ : ι => V)) J).X n ≅
      Sheaf.Hypercohomology.freeAbelianSheaf.{w} J
        (∏ᶜ fun _ : Fin (n + 1) => V).left :=
  (presheafToSheaf J AddCommGrpCat.{max h w}).mapIso
    (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).mapIso
      (tupleProductIso (fun _ : ι => V) n)) ≪≫
    freeUniqueFamilyIso (Fin (n + 1) → ι)
      (∏ᶜ fun _ : Fin (n + 1) => V).left J

end CategoryTheory.Presheaf.Cech
