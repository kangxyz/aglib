/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HigherHorizontal
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HigherVertical

/-! # Native comparison factors prove the higher horizontal transport edges

The premises are the already proved homology/single comparison coherence and
original map factorization. No final horizontal transport edge is assumed.
-/

@[expose] public section
namespace CategoryTheory

/-- The inverse of the original target comparison retains its two original factors. -/
theorem mapped_target_inverse
    {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {X Y : C} (σ : X ≅ Y) {Z : D} (e : Z ≅ H.obj Y) (t : H.obj X ≅ Z)
    (ht : t.hom = H.map σ.hom ≫ e.inv) :
    t.inv = e.hom ≫ H.map σ.inv := by
  apply (cancel_epi t.hom).mp
  rw [Iso.hom_inv_id, ht]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← H.map_comp, Iso.hom_inv_id, H.map_id]

section Source
variable {A₀ A₁ A₂ C₀ C₁ C₂ : Type*}
  [Category* A₀] [Category* A₁] [Category* A₂]
  [Category* C₀] [Category* C₁] [Category* C₂]

/-- Native homology composition and naturality give the first horizontal edge. -/
theorem mapped_horizontal_source_edge
    (H₀ : C₀ ⥤ A₀) (H₁ : C₁ ⥤ A₁) (H₂ : C₂ ⥤ A₂)
    (G₁ : A₀ ⥤ A₁) (G₂ : A₁ ⥤ A₂) (G : A₀ ⥤ A₂)
    (D₁ : C₀ ⥤ C₁) (D₂ : C₁ ⥤ C₂) (D : C₀ ⥤ C₂)
    (γ₁ : D₁ ⋙ H₁ ≅ H₀ ⋙ G₁) (γ₂ : D₂ ⋙ H₂ ≅ H₁ ⋙ G₂)
    (γ : D ⋙ H₂ ≅ H₀ ⋙ G) (c : G ≅ G₁ ⋙ G₂) (cD : D ≅ D₁ ⋙ D₂)
    (K : C₀)
    (hγ : H₂.map (cD.hom.app K) ≫ γ₂.hom.app (D₁.obj K) ≫
      G₂.map (γ₁.hom.app K) = γ.hom.app K ≫ c.hom.app (H₀.obj K))
    {Z : A₀} (e : Z ≅ H₀.obj K) :
    c.hom.app Z ≫ G₂.map (G₁.map e.hom ≫ γ₁.inv.app K) ≫
        γ₂.inv.app (D₁.obj K) =
      G.map e.hom ≫ γ.inv.app K ≫ H₂.map (cD.hom.app K) := by
  apply (cancel_mono (γ₂.hom.app (D₁.obj K) ≫ G₂.map (γ₁.hom.app K))).mp
  simp only [Category.assoc]
  rw [hγ, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app_assoc]
  rw [← G₂.map_comp, Category.assoc, Iso.inv_hom_id_app]
  change c.hom.app Z ≫ G₂.map (G₁.map e.hom ≫ 𝟙 (G₁.obj (H₀.obj K))) = _
  rw [Category.comp_id]
  have hn := c.hom.naturality e.hom
  simpa only [Functor.comp_map] using hn.symm

/-- Pulling back a native factorization through the exact homology comparison
proves the first middle edge. -/
theorem mapped_horizontal_pullback_edge
    (H₁ : C₁ ⥤ A₁) (H₂ : C₂ ⥤ A₂) (G₂ : A₁ ⥤ A₂) (D₂ : C₁ ⥤ C₂)
    (γ₂ : D₂ ⋙ H₂ ≅ H₁ ⋙ G₂)
    {U V : C₁} (b : U ⟶ V) {U' V' : A₁}
    (iU : U' ≅ H₁.obj U) (iV : V' ≅ H₁.obj V) (b' : U' ⟶ V')
    (hb : b' ≫ iV.hom = iU.hom ≫ H₁.map b) :
    G₂.map b' ≫ (G₂.map iV.hom ≫ γ₂.inv.app V) =
      (G₂.map iU.hom ≫ γ₂.inv.app U) ≫ H₂.map (D₂.map b) := by
  have hn := γ₂.inv.naturality b
  simp only [Functor.comp_map] at hn
  rw [← Category.assoc, ← G₂.map_comp, hb, G₂.map_comp, Category.assoc, hn,
    ← Category.assoc]

end Source

section Middle
variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

/-- Naturality of the actual derived exchange changes the coefficient single
without choosing another exchange map. -/
theorem mapped_horizontal_single_edge (H : D ⥤ E)
    {P Q : C ⥤ D} (β : P ⟶ Q) {X Y : C} (p : Y ⟶ X)
    {U V : E} (iU : U ≅ H.obj (P.obj Y)) (iV : V ≅ H.obj (Q.obj Y))
    (b : U ⟶ V) (hb : b ≫ iV.hom = iU.hom ≫ H.map (β.app Y)) :
    b ≫ (iV.hom ≫ H.map (Q.map p)) =
      (iU.hom ≫ H.map (P.map p)) ≫ H.map (β.app X) := by
  rw [← Category.assoc, hb, Category.assoc, ← H.map_comp,
    ← β.naturality, H.map_comp, ← Category.assoc]

end Middle

section Target
variable {A₀ A₁ A₂ C₀ C₁ C₂ E B : Type*}
  [Category* A₀] [Category* A₁] [Category* A₂]
  [Category* C₀] [Category* C₁] [Category* C₂] [Category* E] [Category* B]

/-- Native exact-single composition and higher-image naturality give the final
horizontal edge, including the actual composition comparison. -/
theorem mapped_horizontal_target_edge
    (J₀ : A₀ ⥤ C₀) (J₁ : A₁ ⥤ C₁) (J₂ : A₂ ⥤ C₂)
    (L₁ : A₀ ⥤ A₁) (L₂ : A₁ ⥤ A₂) (L : A₀ ⥤ A₂)
    (D₁ : C₀ ⥤ C₁) (D₂ : C₁ ⥤ C₂) (D : C₀ ⥤ C₂)
    (σ₁ : J₀ ⋙ D₁ ≅ L₁ ⋙ J₁) (σ₂ : J₁ ⋙ D₂ ≅ L₂ ⋙ J₂)
    (σ : J₀ ⋙ D ≅ L ⋙ J₂) (c : L ≅ L₁ ⋙ L₂) (cD : D ≅ D₁ ⋙ D₂)
    (M : A₀)
    (hσ : cD.hom.app (J₀.obj M) ≫ D₂.map (σ₁.hom.app M) ≫
      σ₂.hom.app (L₁.obj M) = σ.hom.app M ≫ J₂.map (c.hom.app M))
    (R : C₂ ⥤ E) (H : E ⥤ B) (V : A₂ ⥤ B) (e : V ≅ J₂ ⋙ R ⋙ H) :
    V.map (c.hom.app M) ≫ e.hom.app (L₂.obj (L₁.obj M)) ≫
        H.map (R.map (σ₂.inv.app (L₁.obj M))) ≫
        H.map (R.map (D₂.map (σ₁.inv.app M))) =
      e.hom.app (L.obj M) ≫ H.map (R.map (σ.inv.app M)) ≫
        H.map (R.map (cD.hom.app (J₀.obj M))) := by
  have hs : J₂.map (c.hom.app M) ≫ σ₂.inv.app (L₁.obj M) ≫
      D₂.map (σ₁.inv.app M) = σ.inv.app M ≫ cD.hom.app (J₀.obj M) := by
    apply (cancel_epi (σ.hom.app M)).mp
    simp only [Iso.hom_inv_id_app_assoc]
    rw [← reassoc_of% hσ, Iso.hom_inv_id_app_assoc,
      ← D₂.map_comp, Iso.hom_inv_id_app]
    change cD.hom.app (J₀.obj M) ≫ D₂.map (𝟙 (D₁.obj (J₀.obj M))) = _
    rw [D₂.map_id]
    exact Category.comp_id (cD.hom.app (J₀.obj M))
  have hn := e.hom.naturality (c.hom.app M)
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  rw [reassoc_of% hn]
  simp only [← H.map_comp, ← R.map_comp]
  rw [hs]

end Target
/-- Assemble horizontal transport with the actual comparison arrows opaque.
The middle coefficient change is proved from naturality, not assumed as an edge. -/
theorem mapped_horizontal_pasting_actual
    {C D₁ D₂ A₁ A₂ : Type*}
    [Category* C] [Category* D₁] [Category* D₂] [Category* A₁] [Category* A₂]
    (H₁ : D₁ ⥤ A₁) (H₂ : D₂ ⥤ A₂) (G : A₁ ⥤ A₂) (DG : D₁ ⥤ D₂)
    (γ : DG ⋙ H₂ ≅ H₁ ⋙ G) (R : C ⥤ D₁) (Q : C ⥤ D₂)
    (β₂ : R ⋙ DG ⟶ Q) {X Y : C} (p : Y ≅ X)
    {U : D₁} (β₁ : U ⟶ R.obj X)
    {A T : D₂} (a : A ⟶ DG.obj U) (d : A ⟶ T) (e : T ⟶ Q.obj X)
    (hp : a ≫ DG.map β₁ ≫ β₂.app X = d ≫ e)
    {U' V' : A₁} (iU : U' ≅ H₁.obj U) (iV : V' ≅ H₁.obj (R.obj X))
    (iE : V' ≅ H₁.obj (R.obj Y))
    (iS : G.obj V' ≅ H₂.obj (DG.obj (R.obj Y)))
    (ht : iV.hom = iE.hom ≫ H₁.map (R.map p.hom))
    (hs : iS.hom = G.map iE.hom ≫ γ.inv.app (R.obj Y))
    {W : A₂} (iW : W ≅ H₂.obj (Q.obj Y))
    (b₁ : U' ⟶ V') (b₂ : G.obj V' ⟶ W)
    (hb₁ : b₁ ≫ iV.hom = iU.hom ≫ H₁.map β₁)
    (hb₂ : b₂ ≫ iW.hom = iS.hom ≫ H₂.map (β₂.app Y))
    {A' T' : A₂} (iA : A' ≅ H₂.obj A) (iT : T' ≅ H₂.obj T)
    (a' : A' ⟶ G.obj U') (d' : A' ⟶ T') (e' : T' ⟶ W)
    (ha : a' ≫ G.map iU.hom ≫ γ.inv.app U = iA.hom ≫ H₂.map a)
    (hd : d' ≫ iT.hom = iA.hom ≫ H₂.map d)
    (he : e' ≫ iW.hom ≫ H₂.map (Q.map p.hom) = iT.hom ≫ H₂.map e) :
    a' ≫ G.map b₁ ≫ b₂ = d' ≫ e' := by
  let iB := G.mapIso iU ≪≫ (γ.app U).symm
  let iC := G.mapIso iV ≪≫ (γ.app (R.obj X)).symm
  let iD := iW ≪≫ H₂.mapIso (Q.mapIso p)
  have hc₀ : iC.hom = iS.hom ≫ H₂.map (DG.map (R.map p.hom)) := by
    have hn := γ.inv.naturality (R.map p.hom)
    simp only [Functor.comp_map] at hn
    dsimp only [iC, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv]
    rw [ht, G.map_comp, Category.assoc, hn, hs, Category.assoc]
  have hc := mapped_horizontal_single_edge H₂ β₂ p.hom iS iW b₂ hb₂
  apply mapped_horizontal_transport H₂ a (DG.map β₁) (β₂.app X) d e hp
    iA iB iC iD iT a' (G.map b₁) b₂ d' e'
  · exact ha
  · exact mapped_horizontal_pullback_edge H₁ H₂ G DG γ β₁ iU iV b₁ hb₁
  · change b₂ ≫ (iW.hom ≫ H₂.map (Q.map p.hom)) = iC.hom ≫ H₂.map (β₂.app X)
    rw [hc₀]
    exact hc
  · exact hd
  · exact he

/-- The literal higher horizontal equation with its actual maps left opaque. -/
def MappedHorizontalPastingEquation
    {A B : Type*} [Category* A] [Category* B] (G : A ⥤ B)
    {U V : A} {P Q W : B} (a : P ⟶ G.obj U) (b : U ⟶ V)
    (c : G.obj V ⟶ W) (d : P ⟶ Q) (e : Q ⟶ W) : Prop :=
  a ≫ G.map b ≫ c = d ≫ e

/-- All higher exchange factors and the conclusion use the shared literal interfaces. -/
theorem mapped_horizontal_pasting_actual_equation
    {C D₁ D₂ A₁ A₂ : Type*}
    [Category* C] [Category* D₁] [Category* D₂] [Category* A₁] [Category* A₂]
    (H₁ : D₁ ⥤ A₁) (H₂ : D₂ ⥤ A₂) (G : A₁ ⥤ A₂) (DG : D₁ ⥤ D₂)
    (γ : DG ⋙ H₂ ≅ H₁ ⋙ G) (R : C ⥤ D₁) (Q : C ⥤ D₂)
    (β₂ : R ⋙ DG ⟶ Q) {X Y : C} (p : Y ≅ X)
    {U : D₁} (β₁ : U ⟶ R.obj X)
    {A T : D₂} (a : A ⟶ DG.obj U) (d : A ⟶ T) (e : T ⟶ Q.obj X)
    (hp : a ≫ DG.map β₁ ≫ β₂.app X = d ≫ e)
    {U' V' : A₁} (iU : U' ≅ H₁.obj U) (iV : V' ≅ H₁.obj (R.obj X))
    (iE : V' ≅ H₁.obj (R.obj Y))
    (iS : G.obj V' ≅ H₂.obj (DG.obj (R.obj Y)))
    (ht : iV.hom = iE.hom ≫ H₁.map (R.map p.hom))
    (hs : iS.hom = G.map iE.hom ≫ γ.inv.app (R.obj Y))
    {W : A₂} (iW : W ≅ H₂.obj (Q.obj Y))
    (b₁ : U' ⟶ V') (b₂ : G.obj V' ⟶ W)
    (hb₁ : MappedTargetInverseEquation H₁ β₁ iU iV b₁)
    (hb₂ : MappedTargetInverseEquation H₂ (β₂.app Y) iS iW b₂)
    {A' T' : A₂} (iA : A' ≅ H₂.obj A) (iT : T' ≅ H₂.obj T)
    (a' : A' ⟶ G.obj U') (d' : A' ⟶ T') (e' : T' ⟶ W)
    (ha : a' ≫ G.map iU.hom ≫ γ.inv.app U = iA.hom ≫ H₂.map a)
    (hd : MappedTargetInverseEquation H₂ d iA iT d')
    (he : e' ≫ iW.hom ≫ H₂.map (Q.map p.hom) = iT.hom ≫ H₂.map e) :
    MappedHorizontalPastingEquation G a' b₁ b₂ d' e' :=
  mapped_horizontal_pasting_actual H₁ H₂ G DG γ R Q β₂ p β₁ a d e hp
    iU iV iE iS ht hs iW b₁ b₂ hb₁ hb₂ iA iT a' d' e' ha hd he

/-- Read the literal horizontal equation without unfolding any actual map. -/
theorem mappedHorizontalPastingEquation_eq
    {A B : Type*} [Category* A] [Category* B] (G : A ⥤ B)
    {U V : A} {P Q W : B} (a : P ⟶ G.obj U) (b : U ⟶ V)
    (c : G.obj V ⟶ W) (d : P ⟶ Q) (e : Q ⟶ W)
    (h : MappedHorizontalPastingEquation G a b c d e) :
    a ≫ G.map b ≫ c = d ≫ e := h

end CategoryTheory
