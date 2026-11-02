/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Opposites

/-!
# Whole identity equations on original comparison maps

The actual functors, isomorphisms and coefficient maps remain arguments of
complete variable-category laws. Native functor, iso and opposite identities
are consumed before specialization to geometric objects.
-/

@[expose] public section

open Opposite

namespace CategoryTheory.Functor

/-- Reflexive original comparisons give the whole coefficient square. -/
theorem originalComparison_refl_square
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (F : C ⥤ D) (G : C' ⥤ D') (H : D' ⥤ D)
    (x : C) (y : C') (c : F.obj x ⟶ H.obj (G.obj y)) :
    F.map (Iso.refl x).hom ≫ c = c ≫ H.map (G.map (Iso.refl y).hom) := by
  simp only [Iso.refl_hom, Functor.map_id, Category.id_comp, Category.comp_id]

/-- A proved composition of original comparisons gives its entire mapped
composition equation, without selecting replacement isomorphisms. -/
theorem originalComparison_trans
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {x y z : C} (e : x ≅ y) (e' : y ≅ z) (e'' : x ≅ z)
    (h : e ≪≫ e' = e'') :
    F.map e.hom ≫ F.map e'.hom = F.map e''.hom := by
  have hF : F.mapIso e ≪≫ F.mapIso e' = F.mapIso e'' :=
    (F.mapIso_trans e e').symm.trans (congrArg F.mapIso h)
  exact congrArg (fun i => i.hom) hF

/-- The complete normalized identity square uses the same coefficient,
comparison and functor identity iso. The premise is its independently proved
unnormalized equation, not the final identity conclusion. -/
theorem originalComparison_identity_normalization
    {C : Type*} [Category* C] (H : C ⥤ C) (e : H ≅ 𝟭 C)
    {M N : C} (c : M ⟶ H.obj N) (j : N ⟶ M)
    (hc : c ≫ H.map j = e.inv.app M) :
    c ≫ H.map j ≫ e.hom.app M = 𝟙 M := by
  rw [← Category.assoc, hc]
  exact e.inv_hom_id_app M

/-- Applying the same contravariant functor twice preserves the literal identity.
No double-dual functor or second implementation is constructed. -/
theorem originalDoubleContravariant_id
    {C : Type*} [Category* C] (D : Cᵒᵖ ⥤ C) (M : C) :
    D.map ((D.map ((𝟙 M).op)).op) = 𝟙 (D.obj (op (D.obj (op M)))) := by
  simp only [op_id, Functor.map_id]

/-- Whole mapped-reflexivity through the original contravariant functor twice.
Both complete functors remain variable until the actual geometric application. -/
theorem originalDoubleContravariant_map_refl
    {C E : Type*} [Category* C] [Category* E]
    (D : Cᵒᵖ ⥤ C) (F : E ⥤ C) (x : E) :
    D.map ((D.map ((F.map (Iso.refl x).hom).op)).op) =
      𝟙 (D.obj (op (D.obj (op (F.obj x))))) := by
  change D.map ((D.map ((F.map (𝟙 x)).op)).op) = _
  rw [F.map_id]
  exact originalDoubleContravariant_id D (F.obj x)

end CategoryTheory.Functor
