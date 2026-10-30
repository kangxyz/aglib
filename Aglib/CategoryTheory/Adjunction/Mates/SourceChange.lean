/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.Mates.Whole

/-! # Original source units and their complete exchange pasting

The original identity-side square determines its actual source-unit mate.
Source composition then uses the original vertical pasting, identity comparison
and literal equality transport. Only comparison isomorphisms are cancelled;
the exchange arrows are never assumed invertible.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.SourceChange

/-- The actual source comparison through equality of its original index. -/
def sourceComparison {I : Sort*} {C D : Type*} [Category* C] [Category* D]
    (F : I → C ⥤ D) {i j : I} (h : j = i) {G : C ⥤ D} (a : F j ≅ G) :
    F i ≅ G :=
  eqToIso (congrArg F h.symm) ≪≫ a

/-- Reflexive source transport retains the actual original comparison. -/
@[simp]
theorem sourceComparison_refl {I : Sort*} {C D : Type*} [Category* C] [Category* D]
    (F : I → C ⥤ D) (i : I) {G : C ⥤ D} (a : F i ≅ G) :
    sourceComparison F (i := i) rfl a = a := by
  simp [sourceComparison]

/-- Original identity-side square normalization follows from the original
identity composition comparison and literal source-index equality. -/
theorem identitySource_square {I : Sort*} {C D : Type*} [Category* C] [Category* D]
    (F : I → C ⥤ D) {i j k : I} (h : j = i) (hk : k = i)
    {G : C ⥤ D} {J : C ⥤ C} (a : F j ≅ G) (b : F k ≅ J ⋙ F i)
    (d : J ≅ 𝟭 C) (q : G ≅ J ⋙ F i)
    (hq : q = a.symm ≪≫ eqToIso (congrArg F (h.trans hk.symm)) ≪≫ b)
    (hb : b ≪≫ Functor.isoWhiskerRight d (F i) ≪≫ Functor.leftUnitor (F i) =
      eqToIso (congrArg F hk)) :
    q ≪≫ Functor.isoWhiskerRight d (F i) ≪≫ Functor.leftUnitor (F i) =
      (sourceComparison F h a).symm := by
  apply Iso.ext
  have hh := congrArg Iso.hom hb
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom] at hh
  simp only [hq, sourceComparison, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Category.assoc]
  rw [hh]
  simp only [eqToIso.hom, eqToIso.inv, eqToHom_trans]

/-- The whole original identity normalization retains its component value. -/
theorem normalized_identity_square_app
    {C D : Type*} [Category* C] [Category* D]
    {F H : C ⥤ D} {I : C ⥤ C}
    (a : F ≅ I ⋙ H) (e : I ≅ 𝟭 C) (b : F ≅ H)
    (h : a ≪≫ Functor.isoWhiskerRight e H ≪≫ Functor.leftUnitor H = b) (M : C) :
    a.hom.app M ≫ H.map (e.hom.app M) = b.hom.app M := by
  have hc := congrArg (fun z : F ≅ H => z.hom.app M) h
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hc
  exact (congrArg (fun z => a.hom.app M ≫ z)
    (Category.comp_id (H.map (e.hom.app M)))).symm.trans hc

/-- Mapping the actual normalized identity chain retains the same arrow. -/
theorem mapped_identity_chain {C D E : Type*}
    [Category C] [Category D] [Category E]
    {F H : C ⥤ D} {I : C ⥤ C} (L : D ⥤ E)
    (a : F ≅ I ⋙ H) (b : I ≅ 𝟭 C) (c : F ≅ H)
    (hc : a ≪≫ Functor.isoWhiskerRight b H ≪≫ Functor.leftUnitor H = c) (M : C) :
    L.map (a.hom.app M) ≫ L.map (H.map (b.hom.app M)) = L.map (c.hom.app M) := by
  have ht := congrArg (fun z : F ≅ H => z.hom.app M) hc
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at ht
  have hb := (congrArg (fun z => a.hom.app M ≫ z)
    (Category.comp_id (H.map (b.hom.app M)))).symm.trans ht
  exact (L.map_comp (a.hom.app M) (H.map (b.hom.app M))).symm.trans
    (congrArg L.map hb)

/-- The original arrow pasting survives the given naturality and identity normalization. -/
theorem normalized_arrow_pasting {C : Type*} [Category C]
    {A B D E F G : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ F)
    (x : B ⟶ E) (y : E ⟶ F) (z : F ⟶ G) (t : A ⟶ D) (w : A ⟶ G)
    (hn : b ≫ c = x ≫ y) (hi : a ≫ b = t) (hv : a ≫ x ≫ y ≫ z = w) :
    t ≫ c ≫ z = w := by
  rw [← hi, Category.assoc, ← Category.assoc b, hn, Category.assoc]
  exact hv

/-- Source-index equality transports the original family of maps. -/
theorem indexed_map_transport {I : Type*} {C D E : Type*}
    [Category C] [Category D] [Category E] (F : I → C ⥤ D) (L : D ⥤ E)
    (H : C ⥤ E) (P : I → Prop) (α : ∀ k, P k → (F k ⋙ L ⟶ H))
    {a b : I} (h : a = b) (ha : P a) (hb : P b) (M : C) :
    L.map ((eqToIso (congrArg F h)).hom.app M) ≫ (α b hb).app M =
      (α a ha).app M := by
  subst b
  change L.map (𝟙 _) ≫ _ = _
  rw [L.map_id, Category.id_comp]


/-- The original right-identity adjustment retains its two actual components. -/
theorem adjusted_exchange_app
    {C D : Type*} [Category* C] [Category* D]
    {F L : C ⥤ D} {I : D ⥤ D} (a : F ≅ L ⋙ I) (d : I ≅ 𝟭 D) (M : C) :
    (a ≪≫ Functor.isoWhiskerLeft L d ≪≫ Functor.rightUnitor L).hom.app M =
      a.hom.app M ≫ d.hom.app (L.obj M) := by
  simp

/-- The original left-identity adjustment maps the actual identity comparison. -/
theorem normalized_left_identity_app
    {C D : Type*} [Category* C] [Category* D]
    {I : C ⥤ C} (d : I ≅ 𝟭 C) (L : C ⥤ D) (M : C) :
    (Functor.isoWhiskerRight d L ≪≫ Functor.leftUnitor L).hom.app M =
      L.map (d.hom.app M) := by
  simp

/-- The original adjusted composition retains its three actual components. -/
theorem adjusted_composition_app
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    {K : A ⥤ B} {F : B ⥤ C} {T : A ⥤ C} {L : C ⥤ D}
    {J : B ⥤ D} {I : A ⥤ D} (c : T ≅ K ⋙ F) (a : F ⋙ L ≅ J)
    (b : K ⋙ J ≅ I) (M : A) :
    (Functor.isoWhiskerRight c L ≪≫ Functor.associator K F L ≪≫
      Functor.isoWhiskerLeft K a ≪≫ b).hom.app M =
    L.map (c.hom.app M) ≫ a.hom.app (K.obj M) ≫ b.hom.app M := by
  simp

/-- The original right-identity normalization retains its component. -/
theorem normalized_right_identity_app
    {C D : Type*} [Category* C] [Category* D]
    {F L : C ⥤ D} {I : D ⥤ D} (c : F ≅ L ⋙ I) (d : I ≅ 𝟭 D)
    (t : F ≅ L)
    (h : c ≪≫ Functor.isoWhiskerLeft L d ≪≫ Functor.rightUnitor L = t) (M : C) :
    c.hom.app M ≫ d.hom.app (L.obj M) = t.hom.app M := by
  rw [← adjusted_exchange_app, h]

/-- The normalized original source comparison has the specified inverse component. -/
theorem normalized_source_inverse_app
    {C D : Type*} [Category* C] [Category* D]
    {F L : C ⥤ D} {I : D ⥤ D} (c : F ≅ L ⋙ I) (d : I ≅ 𝟭 D)
    (t : F ≅ L)
    (h : c ≪≫ Functor.isoWhiskerLeft L d ≪≫ Functor.rightUnitor L = t) (M : C) :
    (t.symm ≪≫ c).inv.app M = d.hom.app (L.obj M) := by
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app]
  apply (cancel_epi (c.hom.app M)).1
  rw [Iso.hom_inv_id_app_assoc]
  exact (normalized_right_identity_app c d t h M).symm

/-- Target-index equality transports the original family of maps. -/
theorem indexed_target_transport
    {J C D E : Type*} [Category* C] [Category* D] [Category* E]
    (R : J → D ⥤ E) (F : C ⥤ E) (L : C ⥤ D) (P : J → Prop)
    (α : ∀ j, P j → (F ⟶ L ⋙ R j)) {a b : J} (h : a = b)
    (ha : P a) (hb : P b) (M : C) :
    (α a ha).app M ≫ (eqToIso (congrArg R h)).hom.app (L.obj M) =
      (α b hb).app M := by
  subst b
  simp

/-- Original noninvertible pasting retains the displayed identity adjustments. -/
theorem adjusted_pasting
    {C : Type*} [Category* C] {A B C₁ D E F G H : C}
    (a : A ⟶ B) (b : B ⟶ C₁) (c : C₁ ⟶ D) (d : D ⟶ E) (e : E ⟶ F)
    (r : C₁ ⟶ G) (s : G ⟶ E) (t : A ⟶ H) (u : H ⟶ D)
    (v : H ⟶ E) (w : A ⟶ E)
    (hn : c ≫ d = r ≫ s) (hp : a ≫ b ≫ c = t ≫ u)
    (hd : u ≫ d = v) (ht : t ≫ v = w) :
    w ≫ e = a ≫ b ≫ r ≫ s ≫ e := by
  symm
  rw [← reassoc_of% hn, reassoc_of% hp, reassoc_of% hd, reassoc_of% ht]

/-- The proved original unit tail cancels without inverting the other arrows. -/
theorem remove_unit_tail
    {C : Type*} [Category* C] {A B D E : C}
    (a : A ⟶ B) (u : B ⟶ D) (v : D ⟶ E) (d : E ⟶ B)
    (h : u ≫ v ≫ d = 𝟙 B) : (a ≫ u ≫ v) ≫ d = a := by
  simp only [Category.assoc, h, Category.comp_id]


/-- The original identity-side mate is exactly the original source-adjunction unit formula. -/
theorem mate_source_unit
    {C P V : Type*} [Category* C] [Category* P] [Category* V]
    {LI RI : C ⥤ C} {Le : P ⥤ V} {Re : V ⥤ P}
    (ai : LI ⊣ RI) (ae : Le ⊣ Re) (G : C ⥤ P) (H : C ⥤ V)
    (α : G ⋙ Le ⟶ LI ⋙ H) (dL : LI ≅ 𝟭 C) (dR : RI ≅ 𝟭 C)
    (s : H ≅ G ⋙ Le)
    (hcounit : ∀ M, ai.counit.app M = dL.hom.app (RI.obj M) ≫ dR.hom.app M)
    (hs : ∀ M, α.app M ≫ H.map (dL.hom.app M) = s.inv.app M) (M : C) :
    ((mateEquiv ai ae (TwoSquare.mk G LI Le H α)).natTrans).app M =
      G.map (dR.hom.app M) ≫ ae.unit.app (G.obj M) ≫ Re.map (s.inv.app M) := by
  let t : G.obj (RI.obj M) ⟶ G.obj M := G.map (dR.hom.app M)
  let k := Le.map t ≫ s.inv.app M
  have hb : ((mateEquiv ai ae (TwoSquare.mk G LI Le H α)).natTrans).app M =
      ae.homEquiv _ _ k := by
    apply (ae.homEquiv _ _).symm.injective
    simp only [Functor.comp_obj]
    rw [Equiv.symm_apply_apply]
    change Le.map _ ≫ ae.counit.app _ = k
    rw [mateEquiv_counit ai ae (TwoSquare.mk G LI Le H α) M]
    rw [hcounit M, Functor.map_comp]
    rw [reassoc_of% (hs (RI.obj M))]
    have hn := s.inv.naturality (dR.hom.app M)
    simp only [Functor.comp_map] at hn
    exact hn.symm
  rw [hb]
  change ae.unit.app _ ≫ Re.map k = _
  dsimp only [k]
  rw [Functor.map_comp, ← Category.assoc]
  have hu := ae.unit_naturality t
  exact (congrArg (fun z => z ≫ Re.map (s.inv.app M)) hu).trans (Category.assoc _ _ _)

/-- The original source-unit formula and vertical mate pasting give complete
source composition, retaining the actual source-index comparison. -/
theorem source_pasting
    {C D E F G : Type*} [Category* C] [Category* D] [Category* E]
    [Category* F] [Category* G]
    (R₀ R₁ : C ⥤ D) (I : C ⥤ C) (L : D ⥤ E) (Q : C ⥤ F)
    {Le : F ⥤ G} {Re : G ⥤ F} (a : Le ⊣ Re) (Rp : F ⥤ E)
    (Rpe : G ⥤ E) (Qe : C ⥤ G)
    (df : R₀ ≅ I ⋙ R₁) (di : I ≅ 𝟭 C) (e : R₀ ≅ R₁)
    (dp : Rpe ≅ Re ⋙ Rp) (c : Qe ≅ Q ⋙ Le)
    (β : R₁ ⋙ L ⟶ Q ⋙ Rp) (βs : I ⋙ Q ⟶ Qe ⋙ Re)
    (βt : R₀ ⋙ L ⟶ Qe ⋙ Rpe) (βf : R₁ ⋙ L ⟶ Qe ⋙ Rpe)
    (hid : df ≪≫ Functor.isoWhiskerRight di R₁ ≪≫ Functor.leftUnitor R₁ = e)
    (hs : ∀ M, βs.app M = Q.map (di.hom.app M) ≫
      a.unit.app (Q.obj M) ≫ Re.map (c.inv.app M))
    (hv : ∀ M, L.map (df.hom.app M) ≫ β.app (I.obj M) ≫ Rp.map (βs.app M) =
      βt.app M ≫ dp.hom.app (Qe.obj M))
    (he : ∀ M, L.map (e.hom.app M) ≫ βf.app M = βt.app M) (M : C) :
    βf.app M ≫ dp.hom.app (Qe.obj M) ≫ Rp.map (Re.map (c.hom.app M)) =
      β.app M ≫ Rp.map (a.unit.app (Q.obj M)) := by
  have hexp := congrArg (fun k => k ≫ Rp.map (Re.map (c.hom.app M))) (hv M)
  rw [hs M] at hexp
  simp only [Functor.map_comp, Category.assoc] at hexp
  have hc : Rp.map (Re.map (c.inv.app M)) ≫ Rp.map (Re.map (c.hom.app M)) = 𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app]
    exact (congrArg Rp.map (Re.map_id _)).trans (Rp.map_id _)
  rw [hc] at hexp
  simp only [Functor.comp_obj, Category.comp_id] at hexp
  have hn := normalized_arrow_pasting
    (L.map (df.hom.app M)) (L.map (R₁.map (di.hom.app M))) (β.app M)
    (β.app (I.obj M)) (Rp.map (Q.map (di.hom.app M)))
    (Rp.map (a.unit.app (Q.obj M))) (L.map (e.hom.app M))
    (βt.app M ≫ dp.hom.app (Qe.obj M) ≫ Rp.map (Re.map (c.hom.app M)))
    (β.naturality (di.hom.app M)) (mapped_identity_chain L df di e hid M) hexp
  rw [← he M] at hn
  apply (cancel_epi (L.map (e.hom.app M))).mp
  simpa only [Category.assoc] using hn.symm


/-- The actual exchanged isomorphism with its original right identity removed. -/
def adjustedExchangeIso {C D : Type*} [Category* C] [Category* D]
    {F L : C ⥤ D} {I : D ⥤ D} (a : F ≅ L ⋙ I) (d : I ≅ 𝟭 D) : F ≅ L :=
  a ≪≫ Functor.isoWhiskerLeft L d ≪≫ Functor.rightUnitor L

/-- The constructed adjustment retains the original exchanged component. -/
@[simp]
theorem adjustedExchangeIso_app {C D : Type*} [Category* C] [Category* D]
    {F L : C ⥤ D} {I : D ⥤ D} (a : F ≅ L ⋙ I) (d : I ≅ 𝟭 D) (M : C) :
    (adjustedExchangeIso a d).hom.app M = a.hom.app M ≫ d.hom.app (L.obj M) :=
  adjusted_exchange_app a d M

/-- Original vertical pasting gives composition after both actual right identities
are removed; the exchange arrows themselves need not be invertible. -/
theorem identity_source_pasting
    {C₀ C₁ C₂ E : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* E]
    (R₁ : C₁ ⥤ C₂) (R₂ : C₀ ⥤ C₁) (R₀ : C₀ ⥤ C₂)
    (L₁ : C₂ ⥤ E) (L₂ : C₁ ⥤ E) (L₀ : C₀ ⥤ E) (I J : E ⥤ E)
    (cf : R₀ ≅ R₂ ⋙ R₁) (ci : J ≅ I ⋙ I) (di : I ≅ 𝟭 E) (ei : J ≅ I)
    (β₁ : R₁ ⋙ L₁ ⟶ L₂ ⋙ I) (β₂ : R₂ ⋙ L₂ ⟶ L₀ ⋙ I)
    (βt : R₀ ⋙ L₁ ⟶ L₀ ⋙ I) (βp : R₀ ⋙ L₁ ⟶ L₀ ⋙ J)
    (hi : ci ≪≫ Functor.isoWhiskerLeft I di ≪≫ Functor.rightUnitor I = ei)
    (hp : ∀ M, L₁.map (cf.hom.app M) ≫ β₁.app (R₂.obj M) ≫ I.map (β₂.app M) =
      βp.app M ≫ ci.hom.app (L₀.obj M))
    (ht : ∀ M, βp.app M ≫ ei.hom.app (L₀.obj M) = βt.app M) (M : C₀) :
    βt.app M ≫ di.hom.app (L₀.obj M) =
      L₁.map (cf.hom.app M) ≫ β₁.app (R₂.obj M) ≫
        di.hom.app (L₂.obj (R₂.obj M)) ≫ β₂.app M ≫ di.hom.app (L₀.obj M) := by
  have hn := di.hom.naturality (β₂.app M)
  have hd := normalized_right_identity_app ci di ei hi (L₀.obj M)
  exact adjusted_pasting _ _ _ _ _ _ _ _ _ _ _ hn (hp M) hd (ht M)

/-- The original source-unit formula cancels the actual identity-adjunction tail. -/
theorem identity_source_id
    {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D) (I : C ⥤ C)
    {L R : D ⥤ D} (a : L ⊣ R) (d : I ≅ 𝟭 C) (dL : L ≅ 𝟭 D) (dR : R ≅ 𝟭 D)
    (s : G ≅ G ⋙ L) (β : I ⋙ G ⟶ G ⋙ R)
    (hs : ∀ M, s.inv.app M = dL.hom.app (G.obj M))
    (hb : ∀ M, β.app M = G.map (d.hom.app M) ≫
      a.unit.app (G.obj M) ≫ R.map (s.inv.app M))
    (hu : ∀ X, a.unit.app X ≫ R.map (dL.hom.app X) ≫ dR.hom.app X = 𝟙 X) (M : C) :
    β.app M ≫ dR.hom.app (G.obj M) = G.map (d.hom.app M) := by
  rw [hb M, hs M]
  exact remove_unit_tail _ _ _ _ (hu (G.obj M))

/-- The actual adjusted identity-source isomorphism is the original direct identity,
using the full source-unit construction and original adjunction normalization. -/
theorem adjustedExchangeIso_id
    {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D) (I : C ⥤ C)
    {L R : D ⥤ D} (a : L ⊣ R) (d : I ≅ 𝟭 C) (dL : L ≅ 𝟭 D) (dR : R ≅ 𝟭 D)
    (s : G ≅ G ⋙ L) (β : I ⋙ G ⟶ G ⋙ R) (e : I ⋙ G ≅ G ⋙ R) (he : e.hom = β)
    (hs : ∀ M, s.inv.app M = dL.hom.app (G.obj M))
    (hb : ∀ M, β.app M = G.map (d.hom.app M) ≫
      a.unit.app (G.obj M) ≫ R.map (s.inv.app M))
    (hu : ∀ X, a.unit.app X ≫ R.map (dL.hom.app X) ≫ dR.hom.app X = 𝟙 X) :
    adjustedExchangeIso e dR = Functor.isoWhiskerRight d G ≪≫ Functor.leftUnitor G := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  rw [adjustedExchangeIso_app, normalized_left_identity_app, he]
  exact identity_source_id G I a d dL dR s β hs hb hu M

/-- The complete adjusted exchange composition comes from the original vertical
pasting and identity comparisons, not from an assumed adjusted coherence law. -/
theorem adjustedExchangeIso_comp
    {C₀ C₁ C₂ E : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* E]
    (R₁ : C₁ ⥤ C₂) (R₂ : C₀ ⥤ C₁) (R₀ : C₀ ⥤ C₂)
    (L₁ : C₂ ⥤ E) (L₂ : C₁ ⥤ E) (L₀ : C₀ ⥤ E) (I J : E ⥤ E)
    (cf : R₀ ≅ R₂ ⋙ R₁) (ci : J ≅ I ⋙ I) (di : I ≅ 𝟭 E) (ei : J ≅ I)
    (β₁ : R₁ ⋙ L₁ ⟶ L₂ ⋙ I) (β₂ : R₂ ⋙ L₂ ⟶ L₀ ⋙ I)
    (βt : R₀ ⋙ L₁ ⟶ L₀ ⋙ I) (βp : R₀ ⋙ L₁ ⟶ L₀ ⋙ J)
    (e₁ : R₁ ⋙ L₁ ≅ L₂ ⋙ I) (e₂ : R₂ ⋙ L₂ ≅ L₀ ⋙ I)
    (et : R₀ ⋙ L₁ ≅ L₀ ⋙ I)
    (he₁ : e₁.hom = β₁) (he₂ : e₂.hom = β₂) (het : et.hom = βt)
    (hi : ci ≪≫ Functor.isoWhiskerLeft I di ≪≫ Functor.rightUnitor I = ei)
    (hp : ∀ M, L₁.map (cf.hom.app M) ≫ β₁.app (R₂.obj M) ≫ I.map (β₂.app M) =
      βp.app M ≫ ci.hom.app (L₀.obj M))
    (ht : ∀ M, βp.app M ≫ ei.hom.app (L₀.obj M) = βt.app M) :
    adjustedExchangeIso et di =
      Functor.isoWhiskerRight cf L₁ ≪≫ Functor.associator R₂ R₁ L₁ ≪≫
        Functor.isoWhiskerLeft R₂ (adjustedExchangeIso e₁ di) ≪≫
          adjustedExchangeIso e₂ di := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  rw [adjusted_composition_app]
  simpa only [adjustedExchangeIso_app, he₁, he₂, het, Category.assoc] using
    identity_source_pasting R₁ R₂ R₀ L₁ L₂ L₀ I J cf ci di ei β₁ β₂ βt βp hi hp ht M

end CategoryTheory.SourceChange
