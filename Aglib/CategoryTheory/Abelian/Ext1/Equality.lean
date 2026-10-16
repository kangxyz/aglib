/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Abelian.Ext1.Extension

/-!
# Equality of fixed-endpoint extension classes

Equality of the derived degree-one Ext classes gives an isomorphism of the
actual extensions, with identity maps on both fixed endpoints.
-/
@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.DerivedCategory
open _root_.CategoryTheory.Pretriangulated

namespace CategoryTheory.Abelian.Ext1

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X Y : C}

/-- A fixed-endpoint extension isomorphism is an actual short-complex
isomorphism, with identity components at both endpoints. -/
def Extension.Iso.toShortComplexIso {E E' : Extension X Y} (e : Extension.Iso E E') :
    E.toShortComplex ≅ E'.toShortComplex :=
  ShortComplex.isoMk (Iso.refl _) e.middleIso (Iso.refl _)
    (by
      change (𝟙 Y) ≫ E'.i = E.i ≫ e.middleIso.hom
      simpa only [Category.id_comp] using e.comm_i.symm)
    (by
      change e.middleIso.hom ≫ E'.p = E.p ≫ (𝟙 X)
      simpa only [Category.comp_id] using e.comm_p)

/-- Equality of Ext1 classes of actual short exact extensions gives an
extension isomorphism with identity endpoint maps. -/
theorem extClass_eq_iso [HasExt.{w} C] (E E' : Extension X Y)
    (h : E.extClass = E'.extClass) : Nonempty (Extension.Iso E E') := by
  let := HasDerivedCategory.standard C
  let F := singleFunctor C 0
  have hδ : E.shortExact.singleδ = E'.shortExact.singleδ := by
    have hh := congrArg (fun e : Ext.{w} X Y 1 => e.hom) h
    change E.shortExact.extClass.hom = E'.shortExact.extClass.hom at hh
    rw [E.shortExact.extClass_hom, E'.shortExact.extClass_hom] at hh
    exact hh
  obtain ⟨b, hi, hp⟩ := complete_distinguished_triangle_morphism₂
    E.shortExact.singleTriangle E'.shortExact.singleTriangle
    E.shortExact.singleTriangle_distinguished E'.shortExact.singleTriangle_distinguished
    (𝟙 _) (𝟙 _) (by
      change E.shortExact.singleδ ≫ (𝟙 _)⟦(1 : ℤ)⟧' = (𝟙 _) ≫ E'.shortExact.singleδ
      rw [_root_.CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
      exact hδ)
  let f : E.middle ⟶ E'.middle := F.preimage b
  have hf : F.map f = b := F.map_preimage b
  have fi : E.i ≫ f = E'.i := by
    apply F.map_injective
    rw [Functor.map_comp, hf]
    change F.map E.i ≫ b = (𝟙 _) ≫ F.map E'.i at hi
    simpa only [Category.id_comp] using hi
  have fp : f ≫ E'.p = E.p := by
    apply F.map_injective
    rw [Functor.map_comp, hf]
    change F.map E.p ≫ (𝟙 _) = b ≫ F.map E'.p at hp
    simpa only [Category.comp_id] using hp.symm
  let φ : E.toShortComplex ⟶ E'.toShortComplex :=
    { τ₁ := 𝟙 _
      τ₂ := f
      τ₃ := 𝟙 _
      comm₁₂ := by
        change (𝟙 Y) ≫ E'.i = E.i ≫ f
        simpa only [Category.id_comp] using fi.symm
      comm₂₃ := by
        change f ≫ E'.p = E.p ≫ (𝟙 X)
        simpa only [Category.comp_id] using fp }
  have : IsIso f := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃'
    φ E.shortExact E'.shortExact
    (by change IsIso (𝟙 Y); infer_instance)
    (by change IsIso (𝟙 X); infer_instance)
  exact ⟨⟨asIso f, fi, fp⟩⟩

end CategoryTheory.Abelian.Ext1
