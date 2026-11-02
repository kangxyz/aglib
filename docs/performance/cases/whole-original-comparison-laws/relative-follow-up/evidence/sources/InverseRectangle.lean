/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.CoefficientSquares

/-! # Original inverse coefficient rectangle

The actual coherent square comparison first gives its whole vertical pasting
law. Inverting those same comparison isomorphisms and retaining the actual
equality transport gives the inverse coefficient rectangle. No coefficient or
cohomology square is supplied as a premise of the construction.
-/

@[expose] public noncomputable section

namespace CategoryTheory.InjectiveSystem.AdjunctionData

universe uJ vJ uA vA

private theorem five_iso_inverse {C : Type uA} [Category.{vA} C] {A B D E F : C}
    (a : A ≅ B) (b : B ≅ D) (c : D ≅ E) (d : A ≅ F) (e : F ≅ E)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom) :
    b.inv ≫ a.inv = c.hom ≫ e.inv ≫ d.inv := by
  have he : a ≪≫ b ≪≫ c = d ≪≫ e := by
    apply Iso.ext
    simpa only [Iso.trans_hom, Category.assoc] using h
  have hi : c.inv ≫ b.inv ≫ a.inv = e.inv ≫ d.inv := by
    simpa only [Iso.trans_inv, Category.assoc] using congrArg Iso.inv he
  simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using
    congrArg (fun k => c.hom ≫ k) hi

private theorem five_iso_inverse_prefixed {C : Type uA} [Category.{vA} C]
    {A B D E F K L : C}
    (a : A ≅ B) (b : B ≅ D) (c : D ≅ E) (d : A ≅ F) (e : F ≅ E)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom)
    (s : K ⟶ D) (t : K ⟶ L) (j : L ⟶ E) (hs : s ≫ c.hom = t ≫ j) :
    s ≫ b.inv ≫ a.inv = t ≫ j ≫ e.inv ≫ d.inv := by
  rw [five_iso_inverse a b c d e h]
  calc
    _ = (s ≫ c.hom) ≫ e.inv ≫ d.inv := by simp only [Category.assoc]
    _ = (t ≫ j) ≫ e.inv ≫ d.inv := congrArg (fun k => k ≫ e.inv ≫ d.inv) hs
    _ = _ := by simp only [Category.assoc]

variable {J : Type uJ} [Category.{vJ} J]
  {A : J → Type uA} [∀ j, Category.{vA} (A j)]
  (D : InjectiveSystem.AdjunctionData A) (hD : D.Coherent)

include hD in
/-- The inverse whole square rectangle retains the actual intermediate arrow transport. -/
theorem inverse_square_composite_coefficient {S X Y S' X' Y' : J}
    (f : S ⟶ X) (k : X ⟶ Y) (f' : S' ⟶ X') (k' : X' ⟶ Y')
    (g : S ⟶ S') (g' : X ⟶ X') (g'' : Y ⟶ Y')
    (ef : g ≫ f' = f ≫ g') (ek : g' ≫ k' = k ≫ g'')
    (e : g ≫ (f' ≫ k') = (f ≫ k) ≫ g'') (F : A S) :
    (D.leftCompIso g' k').hom.app ((D.left f).obj F) ≫
        (D.left k').map ((D.squareIso f f' g g' ef).inv.app F) ≫
        (D.leftCompIso f' k').inv.app ((D.left g).obj F) =
      eqToHom (congrArg (fun a => (D.left a).obj ((D.left f).obj F)) ek) ≫
        (D.leftCompIso k g'').hom.app ((D.left f).obj F) ≫
        (D.left g'').map ((D.leftCompIso f k).inv.app F) ≫
        (D.squareIso (f ≫ k) (f' ≫ k') g g'' e).inv.app F := by
  apply five_iso_inverse_prefixed
    ((D.leftCompIso f' k').app ((D.left g).obj F))
    ((D.left k').mapIso ((D.squareIso f f' g g' ef).app F))
    ((D.squareIso k k' g' g'' ek).app ((D.left f).obj F))
    ((D.squareIso (f ≫ k) (f' ≫ k') g g'' e).app F)
    ((D.left g'').mapIso ((D.leftCompIso f k).app F))
    (D.squareIso_vComp hD f k f' k' g g' g'' ef ek e F)
    ((D.leftCompIso g' k').hom.app ((D.left f).obj F))
    (eqToHom (congrArg (fun a => (D.left a).obj ((D.left f).obj F)) ek))
    ((D.leftCompIso k g'').hom.app ((D.left f).obj F))
  simp only [squareIso, Iso.app_hom, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app, Iso.hom_inv_id_app_assoc]

include hD in
/-- Actual triangle equalities give the same inverse rectangle before Ext or element evaluation. -/
theorem inverse_square_triangle_coefficient {S X Y S' X' Y' : J}
    (f : S ⟶ X) (k : X ⟶ Y) (f' : S' ⟶ X') (k' : X' ⟶ Y')
    (a : S ⟶ Y) (a' : S' ⟶ Y') (g : S ⟶ S') (g' : X ⟶ X') (g'' : Y ⟶ Y')
    (hv : f ≫ k = a) (hv' : f' ≫ k' = a')
    (ef : g ≫ f' = f ≫ g') (ek : g' ≫ k' = k ≫ g'')
    (e : g ≫ a' = a ≫ g'') (F : A S) :
    (D.leftCompIso g' k').hom.app ((D.left f).obj F) ≫
        (D.left k').map ((D.squareIso f f' g g' ef).inv.app F) ≫
        (D.triangleIso a' f' k' hv').inv.app ((D.left g).obj F) =
      eqToHom (congrArg (fun b => (D.left b).obj ((D.left f).obj F)) ek) ≫
        (D.leftCompIso k g'').hom.app ((D.left f).obj F) ≫
        (D.left g'').map ((D.triangleIso a f k hv).inv.app F) ≫
        (D.squareIso a a' g g'' e).inv.app F := by
  subst a
  subst a'
  simpa only [triangleIso, eqToIso_refl, Iso.refl_trans] using
    D.inverse_square_composite_coefficient hD f k f' k' g g' g'' ef ek e F


universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅ uI

/-- Invert the original whole triangle-square law using its actual square
factorization. The same indexing family gives the literal objectwise transport;
all cancellation and component evaluation precede native specialization. -/
theorem inverse_triangle_coefficient_of_whole
    {C₀ : Type u₀} [Category.{v₀} C₀] {C₁ : Type u₁} [Category.{v₁} C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] {C₃ : Type u₃} [Category.{v₃} C₃]
    {C₄ : Type u₄} [Category.{v₄} C₄] {C₅ : Type u₅} [Category.{v₅} C₅]
    {L_g : C₀ ⥤ C₁} {L_v₀ : C₀ ⥤ C₂} {L_v₁ : C₁ ⥤ C₃} {L_h : C₂ ⥤ C₃}
    {L : C₄ ⥤ C₅} {P₀ : C₀ ⥤ C₄} {P₁ : C₁ ⥤ C₄}
    {Q₀ : C₂ ⥤ C₅} {Q₁ : C₃ ⥤ C₅}
    (t_g : P₀ ≅ L_g ⋙ P₁) (t_h : Q₀ ≅ L_h ⋙ Q₁)
    (s : L_g ⋙ L_v₁ ≅ L_v₀ ⋙ L_h)
    (s₀ : L_v₀ ⋙ Q₀ ≅ P₀ ⋙ L) (s₁ : L_v₁ ⋙ Q₁ ≅ P₁ ⋙ L)
    (h : Adjunction.CoefficientSquares.WholeTriangleSquareEquation t_g t_h s s₀ s₁)
    {I : Type uI} (K : I → C₁ ⥤ C₅) {i j : I} (hij : i = j)
    (θ : K i ≅ L_v₁ ⋙ Q₁) (κ : K j ≅ P₁ ⋙ L)
    (hs₁ : s₁ = θ.symm ≪≫ eqToIso (congrArg K hij) ≪≫ κ) (F : C₀) :
    θ.hom.app (L_g.obj F) ≫ Q₁.map (s.hom.app F) ≫ t_h.inv.app (L_v₀.obj F) =
      eqToHom (congrArg (fun k => (K k).obj (L_g.obj F)) hij) ≫
        κ.hom.app (L_g.obj F) ≫ L.map (t_g.inv.app F) ≫ s₀.inv.app F := by
  have hv : t_h.hom.app (L_v₀.obj F) ≫ Q₁.map (s.inv.app F) ≫
      s₁.hom.app (L_g.obj F) = s₀.hom.app F ≫ L.map (t_g.hom.app F) := by
    have ht := congrArg (fun η => η.app F) h
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Functor.associator_hom_app,
      Category.id_comp, Category.comp_id] using ht
  have hp : θ.hom.app (L_g.obj F) ≫ s₁.hom.app (L_g.obj F) =
      eqToHom (congrArg (fun k => (K k).obj (L_g.obj F)) hij) ≫
        κ.hom.app (L_g.obj F) := by
    rw [hs₁]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso.hom,
      eqToHom_app, Iso.hom_inv_id_app_assoc]
  exact five_iso_inverse_prefixed
    (t_h.app (L_v₀.obj F)) (Q₁.mapIso (s.symm.app F)) (s₁.app (L_g.obj F))
    (s₀.app F) (L.mapIso (t_g.app F)) hv (θ.hom.app (L_g.obj F))
    (eqToHom (congrArg (fun k => (K k).obj (L_g.obj F)) hij))
    (κ.hom.app (L_g.obj F)) hp

end CategoryTheory.InjectiveSystem.AdjunctionData
