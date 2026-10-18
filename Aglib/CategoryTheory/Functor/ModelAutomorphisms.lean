/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.NatIso

/-!
# Extending compatible actions from actual cover models

This construction needs an actual model for every object and compatibility on
every actual arrow between models. It retains both obligations explicitly;
the finite-stage producers are supplied separately. No group exactness is an
input or a conclusion of this generic component construction.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CategoryTheory.Functor.ModelAutomorphisms

universe u v w
variable {C : Type v} [Category.{u} C] (F : C ⥤ FintypeCat.{u})
  {M : Type w} (obj : M → C) (a : ∀ m, Aut (F.obj (obj m)))
  (hcover : ∀ X : C, ∃ m, Nonempty (obj m ≅ X))

/-- A model index for `X` chosen using the supplied covering hypothesis `hcover`. -/
def chosenModel (X : C) : M := (hcover X).choose

/-- The isomorphism from the chosen model to `X` supplied by `hcover`. -/
def chosenIso (X : C) : obj (chosenModel obj hcover X) ≅ X :=
  (hcover X).choose_spec.some

/-- The automorphism of `F.obj X` obtained by transporting the assigned model automorphism along
the chosen isomorphism. -/
def component (X : C) : Aut (F.obj X) :=
  (F.mapIso (chosenIso obj hcover X)).symm ≪≫
    a (chosenModel obj hcover X) ≪≫ F.mapIso (chosenIso obj hcover X)

variable (hnat : ∀ (m n : M) (g : obj m ⟶ obj n),
  F.map g ≫ (a n).hom = (a m).hom ≫ F.map g)

include hnat in
theorem component_arrow (m : M) (X : C) (g : obj m ⟶ X) :
    F.map g ≫ (component F obj a hcover X).hom = (a m).hom ≫ F.map g := by
  have h := hnat m (chosenModel obj hcover X) (g ≫ (chosenIso obj hcover X).inv)
  rw [F.map_comp] at h
  have h' := congrArg (fun k ↦ k ≫ F.map (chosenIso obj hcover X).hom) h
  simp only [Category.assoc] at h'
  rw [← F.map_comp (chosenIso obj hcover X).inv (chosenIso obj hcover X).hom,
    Iso.inv_hom_id, F.map_id, Category.comp_id] at h'
  exact h'

include hnat in
/-- Any second model has the same transported component, not merely the
particular model selected by choice. -/
theorem component_conjugacy (m : M) (X : C) (e : obj m ≅ X) :
    F.map e.hom ≫ (component F obj a hcover X).hom = (a m).hom ≫ F.map e.hom :=
  component_arrow F obj a hcover hnat m X e.hom

include hnat in
theorem component_naturality {X Y : C} (g : X ⟶ Y) :
    F.map g ≫ (component F obj a hcover Y).hom =
      (component F obj a hcover X).hom ≫ F.map g := by
  apply (cancel_epi (F.map (chosenIso obj hcover X).hom)).mp
  calc
    F.map (chosenIso obj hcover X).hom ≫
        (F.map g ≫ (component F obj a hcover Y).hom) =
      F.map ((chosenIso obj hcover X).hom ≫ g) ≫ (component F obj a hcover Y).hom := by
        rw [F.map_comp, Category.assoc]
    _ = (a (chosenModel obj hcover X)).hom ≫
        F.map ((chosenIso obj hcover X).hom ≫ g) :=
      component_arrow F obj a hcover hnat _ _ _
    _ = (F.map (chosenIso obj hcover X).hom ≫ (component F obj a hcover X).hom) ≫
        F.map g := by
      rw [component_arrow F obj a hcover hnat, F.map_comp, Category.assoc]
    _ = F.map (chosenIso obj hcover X).hom ≫
        ((component F obj a hcover X).hom ≫ F.map g) := Category.assoc _ _ _

/-- An actual natural automorphism of the original finite-valued functor. -/
def extendAut : Aut F :=
  NatIso.ofComponents (component F obj a hcover) (fun g ↦ component_naturality F obj a hcover
    hnat g)

@[simp] theorem extendAut_on_model (m : M) :
    (extendAut F obj a hcover hnat).hom.app (obj m) = (a m).hom := by
  change (component F obj a hcover (obj m)).hom = (a m).hom
  have h := component_conjugacy F obj a hcover hnat m (obj m) (Iso.refl _)
  simpa only [Iso.refl_hom, F.map_id, Category.id_comp, Category.comp_id] using h

/-- The extension is independent of all model choices once compatibility on
actual arrows has been proved. -/
theorem extendAut_unique (b : Aut F) (hb : ∀ m, b.hom.app (obj m) = (a m).hom) :
    extendAut F obj a hcover hnat = b := by
  apply Aut.ext
  apply NatTrans.ext
  funext X
  apply (cancel_epi (F.map (chosenIso obj hcover X).hom)).mp
  have h := b.hom.naturality (chosenIso obj hcover X).hom
  rw [hb] at h
  exact (component_conjugacy F obj a hcover hnat (chosenModel obj hcover X) X
    (chosenIso obj hcover X)).trans h.symm

end CategoryTheory.Functor.ModelAutomorphisms

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 113ad7077addcf3bd4cb90147e6782d58178741a2f1eb35a6c55d94bbcef317c.
Definitions, hypotheses and universes are retained modulo native names. -/
