/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.RepresentationTheory.Rep.Basic

/-! # Inverse-automorphism restriction on module-valued presheaves

The native automorphism group and native linear representations retain the
literal contravariant restriction map. A supplied actual section isomorphism
transports that same representation and its original natural maps.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v r w g

namespace CategoryTheory.Aut

variable {C : Type u} [Category.{v} C]

/-- Inverse automorphisms give the native group homomorphism to the opposite category. -/
def inverseOpHom (U : C) : Aut U →* Aut (op U) where
  toFun σ := σ.symm.op
  map_one' := rfl
  map_mul' _ _ := rfl

end CategoryTheory.Aut

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] {R : Type r} [CommRing R]
  (P : Cᵒᵖ ⥤ ModuleCat.{w} R) {U : C} {G : Type g} [Group G]
  (action : G →* Aut U)

/-- Contravariant restriction along the inverse of the supplied actual automorphism. -/
def restrictionRepresentation : Representation R G (P.obj (op U)) :=
  (ModuleCat.endRingEquiv _).toMonoidHom.comp
    ((Aut.toEnd _).comp
      ((Functor.mapAut (op U) P).comp ((Aut.inverseOpHom U).comp action)))

@[simp]
theorem restrictionRepresentation_apply (σ : G) (s : P.obj (op U)) :
    restrictionRepresentation P action σ s = P.map (action σ).inv.op s := rfl

/-- The same native representation viewed through the supplied actual section isomorphism. -/
def transportedRestrictionRepresentation {M : ModuleCat.{w} R}
    (sectionIso : M ≅ P.obj (op U)) : Representation R G M :=
  sectionIso.toLinearEquiv.symm.conjRingEquiv.toMonoidHom.comp
    (restrictionRepresentation P action)

/-- The selected section isomorphism intertwines the actual transported restriction. -/
theorem transportedRestrictionRepresentation_restriction {M : ModuleCat.{w} R}
    (sectionIso : M ≅ P.obj (op U)) (σ : G) (m : M) :
    sectionIso.hom (transportedRestrictionRepresentation P action sectionIso σ m) =
      P.map (action σ).inv.op (sectionIso.hom m) := by
  let i := sectionIso.toLinearEquiv
  change i (i.symm (restrictionRepresentation P action σ (i m))) = _
  exact i.apply_symm_apply _

/-- Original natural transformations intertwine the original inverse restrictions. -/
theorem restrictionRepresentation_naturality {Q : Cᵒᵖ ⥤ ModuleCat.{w} R}
    (a : P ⟶ Q) (σ : G) (s : P.obj (op U)) :
    a.app (op U) (restrictionRepresentation P action σ s) =
      restrictionRepresentation Q action σ (a.app (op U) s) :=
  congrArg (fun b => b s) (a.naturality (action σ).inv.op)

/-- An actual square of the selected section maps transports the original naturality law. -/
theorem transportedRestrictionRepresentation_naturality
    {Q : Cᵒᵖ ⥤ ModuleCat.{w} R} (a : P ⟶ Q)
    {M M' : ModuleCat.{w} R} (sectionIso : M ≅ P.obj (op U))
    (sectionIso' : M' ≅ Q.obj (op U)) (j : M ⟶ M')
    (h : j ≫ sectionIso'.hom = sectionIso.hom ≫ a.app (op U))
    (σ : G) (m : M) :
    j (transportedRestrictionRepresentation P action sectionIso σ m) =
      transportedRestrictionRepresentation Q action sectionIso' σ (j m) := by
  have hnat (x : M) : sectionIso'.hom (j x) = a.app (op U) (sectionIso.hom x) :=
    congrArg (fun f => f x) h
  apply sectionIso'.toLinearEquiv.injective
  change sectionIso'.hom (j (transportedRestrictionRepresentation P action sectionIso σ m)) =
    sectionIso'.hom (transportedRestrictionRepresentation Q action sectionIso' σ (j m))
  rw [hnat, transportedRestrictionRepresentation_restriction,
    transportedRestrictionRepresentation_restriction]
  change a.app (op U) (restrictionRepresentation P action σ (sectionIso.hom m)) =
    restrictionRepresentation Q action σ (sectionIso'.hom (j m))
  rw [hnat]
  exact restrictionRepresentation_naturality P action a σ (sectionIso.hom m)

/-- A fixed-image map, through the selected section isomorphism, is fixed under restriction. -/
theorem transportedRestrictionRepresentation_fixed
    {M N : ModuleCat.{w} R} (sectionIso : M ≅ P.obj (op U)) (i : N ⟶ M)
    (hi : ∀ (σ : G) (n : N),
      transportedRestrictionRepresentation P action sectionIso σ (i n) = i n) (σ : G) :
    (i ≫ sectionIso.hom) ≫ P.map (action σ).hom.op = i ≫ sectionIso.hom := by
  ext n
  change P.map (action σ).hom.op (sectionIso.hom (i n)) = sectionIso.hom (i n)
  have h := transportedRestrictionRepresentation_restriction P action sectionIso σ⁻¹ (i n)
  rw [hi, map_inv] at h
  exact h.symm

end CategoryTheory.Presheaf

namespace CategoryTheory.Adjunction

variable {R : Type r} [CommRing R] {D : Type u} [Category.{v} D]
  {C : ModuleCat.{w} R ⥤ D} {S : D ⥤ ModuleCat.{w} R} (adj : C ⊣ S)
  {M M' : ModuleCat.{w} R} {A A' : D} (e : A ≅ C.obj M) (e' : A' ≅ C.obj M')
  (a : A ⟶ A') (j : M ⟶ M')
  (ha : a ≫ e'.hom = e.hom ≫ C.map j)
  {V V' : ModuleCat.{w} R} (b : S.obj A ⟶ V) (b' : S.obj A' ⟶ V') (aV : V ⟶ V')
  (hb : S.map a ≫ b' = b ≫ aV)

include ha hb in
/-- Original unit naturality transports a square of actual trivializations to sections. -/
theorem unit_iso_sections_naturality :
    j ≫ (adj.unit.app M' ≫ S.map e'.inv ≫ b') =
      (adj.unit.app M ≫ S.map e.inv ≫ b) ≫ aV := by
  have he : e.inv ≫ a = C.map j ≫ e'.inv := by
    apply (cancel_mono e'.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [ha, Iso.inv_hom_id_assoc]
  have hu := adj.unit.naturality j
  change j ≫ adj.unit.app M' = adj.unit.app M ≫ S.map (C.map j) at hu
  rw [← Category.assoc j, hu]
  simp only [Category.assoc]
  rw [← S.map_comp_assoc, ← he, S.map_comp]
  simp only [Category.assoc]
  rw [hb]

end CategoryTheory.Adjunction
