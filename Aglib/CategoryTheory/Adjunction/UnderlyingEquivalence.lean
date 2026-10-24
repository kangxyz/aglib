/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Underlying comparisons for an equivalence

These identities retain a specified natural isomorphism and its normalization
by the original equivalence counit. The functors remain arbitrary while the
naturality and triangle calculations are performed.
-/

@[expose] public section

namespace CategoryTheory

variable {C D A : Type*} [Category* C] [Category* D] [Category* A]

/-- Counit normalization determines the underlying original equivalence unit. -/
theorem Equivalence.unit_map_eq_inv (e : C ≌ D) (V : C ⥤ A)
    (c : e.functor ⋙ e.inverse ⋙ V ≅ V)
    (hc : ∀ N, (e.inverse ⋙ V).map (e.counitIso.hom.app N) =
      c.hom.app (e.inverse.obj N)) (M : C) :
    V.map (e.unitIso.hom.app M) = c.inv.app M := by
  have h := congrArg (e.inverse ⋙ V).map (e.functor_unitIso_comp M)
  simp only [Functor.map_comp, Functor.map_id] at h
  rw [hc] at h
  change (e.functor ⋙ e.inverse ⋙ V).map (e.unitIso.hom.app M) ≫
    c.hom.app (e.inverse.obj (e.functor.obj M)) = 𝟙 _ at h
  have h' : c.hom.app M ≫ V.map (e.unitIso.hom.app M) = 𝟙 _ :=
    (c.hom.naturality (e.unitIso.hom.app M)).symm.trans h
  apply (cancel_epi (c.hom.app M)).mp
  exact h'.trans (Iso.hom_inv_id_app c M).symm

/-- Naturality transports an original counit across its specified comparison. -/
theorem Equivalence.map_functor_comp_counit (e : C ≌ D) (V : C ⥤ A)
    (c : e.functor ⋙ e.inverse ⋙ V ≅ V)
    (hc : ∀ N, (e.inverse ⋙ V).map (e.counitIso.hom.app N) =
      c.hom.app (e.inverse.obj N)) {M : C} {N : D} (k : M ⟶ e.inverse.obj N) :
    (e.inverse ⋙ V).map (e.functor.map k ≫ e.counitIso.hom.app N) =
      c.hom.app M ≫ V.map k := by
  rw [Functor.map_comp, hc]
  exact c.hom.naturality k

/-- Two consecutive maps cancel against a specified inverse after natural
transport through a fixed comparison. -/
theorem NatIso.inv_map_map_hom_comp {F G : C ⥤ A} (c : F ≅ G)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (k : G.obj Z ⟶ G.obj Y)
    (hk : G.map g ≫ k = 𝟙 _) :
    c.inv.app X ≫ F.map f ≫ F.map g ≫ c.hom.app Z ≫ k = G.map f := by
  rw [c.hom.naturality_assoc, c.hom.naturality_assoc,
    Iso.inv_hom_id_app_assoc, hk, Category.comp_id]

/-- The original inverse component of equivalence transport along a given
right-functor comparison. -/
theorem Equivalence.transportRightIso_inv_app
    {B E : Type*} [Category* B] [Category* E]
    (e : C ≌ D) (R : B ⥤ D) (I : B ⥤ E) (J : E ⥤ C)
    (q : R ⋙ e.inverse ≅ I ⋙ J) (M : B) :
    ((Functor.rightUnitor R).symm ≪≫
      Functor.isoWhiskerLeft R e.counitIso.symm ≪≫
      (Functor.associator R e.inverse e.functor).symm ≪≫
      Functor.isoWhiskerRight q e.functor ≪≫
      Functor.associator I J e.functor).inv.app M =
        e.functor.map (q.inv.app M) ≫ e.counitIso.hom.app (R.obj M) := by
  simp

/-- Composition and right transport retain the original equivalence and
adjunction unit arrows. -/
theorem Adjunction.equivalence_transport_unit
    {E B : Type*} [Category* E] [Category* B]
    (e : C ≌ D) (s : E ≌ B) {L : C ⥤ E} {R : E ⥤ C}
    (a : L ⊣ R) {T : B ⥤ D} (t : T ≅ s.inverse ⋙ R ⋙ e.functor) (M : D) :
    (((e.symm.toAdjunction.comp a).comp s.toAdjunction).ofNatIsoRight t.symm).unit.app M =
      e.counitIso.inv.app M ≫ e.functor.map (a.unit.app (e.inverse.obj M)) ≫
        e.functor.map (R.map (s.unitIso.hom.app (L.obj (e.inverse.obj M)))) ≫
          t.inv.app _ := by
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Adjunction.comp_unit_app,
    Functor.comp_map, Category.assoc]
  rfl

/-- The component of the fixed composite inverse-image comparison, when the
inverse-equivalence comparison is the identity. -/
theorem Functor.underlyingComparison_hom_app
    {B E Z : Type*} [Category* B] [Category* E] [Category* Z]
    (I : D ⥤ C) (L : C ⥤ B) (F : B ⥤ E) (U : E ⥤ A)
    (V : B ⥤ A) (W : C ⥤ Z) (K : Z ⥤ A) (N : D ⥤ E)
    (t : N ≅ (I ⋙ L) ⋙ F) (c : F ⋙ U ≅ V) (l : L ⋙ V ≅ W ⋙ K) (M : D) :
    (Functor.isoWhiskerRight t U ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (I ⋙ L) c ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft I l ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Iso.refl (I ⋙ W)) K).hom.app M =
        U.map (t.hom.app M) ≫ c.hom.app (L.obj (I.obj M)) ≫
          l.hom.app (I.obj M) := by
  simp

end CategoryTheory
