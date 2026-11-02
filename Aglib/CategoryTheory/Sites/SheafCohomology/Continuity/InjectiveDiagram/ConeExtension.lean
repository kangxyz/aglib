/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.Cone
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.CoefficientSquares

/-! # Original coefficient and section diagrams under an apex extension

Whole comparison laws are proved before choosing a coefficient system. The
existing cone data then supplies the complete coefficient extension and its
section comparison through the original supplied composition isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.Adjunction.RightTriangleCalculus

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

variable {C₀ : Type u₀} [Category.{v₀} C₀] {C₁ : Type u₁} [Category.{v₁} C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] {C₃ : Type u₃} [Category.{v₃} C₃]
  {C₄ : Type u₄} [Category.{v₄} C₄]

/-- The whole transport equation at its actual functor and comparison heads. -/
def WholeTransportEquation {R S : C₁ ⥤ C₀} {Q : C₄ ⥤ C₁} {P : C₄ ⥤ C₀}
    (c : R ⟶ S) (a : Q ⋙ R ≅ P) (b : Q ⋙ S ≅ P) : Prop :=
  Functor.whiskerLeft Q c ≫ b.hom = a.hom

/-- Evaluate equality transport while its categories and functors remain variables. -/
theorem transport_app {R S : C₁ ⥤ C₀} {Q : C₄ ⥤ C₁} {P : C₄ ⥤ C₀}
    (e : R = S) (a : Q ⋙ R ≅ P) (b : Q ⋙ S ≅ P)
    (h : WholeTransportEquation (eqToHom e) a b) (K : C₄) :
    eqToHom (Functor.congr_obj e (Q.obj K)) ≫ b.hom.app K = a.hom.app K := by
  change Functor.whiskerLeft Q (eqToHom e) ≫ b.hom = a.hom at h
  have hc := NatTrans.congr_app h K
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app] using hc

/-- The same original square contracts through its supplied original comparison. -/
def WholeContractionEquation {F : C₁ ⥤ C₀} {H : C₃ ⥤ C₂}
    {V₀ : C₂ ⥤ C₀} {V₁ : C₃ ⥤ C₁} {T U : C₃ ⥤ C₀}
    (s : H ⋙ V₀ ≅ V₁ ⋙ F) (c₀ : V₁ ⋙ F ≅ T) (c₁ : H ⋙ V₀ ≅ U)
    (t : U ⟶ T) : Prop := s.hom ≫ c₀.hom = c₁.hom ≫ t

/-- Contract and append the original arrow before specializing the actual object. -/
theorem contraction_app {F : C₁ ⥤ C₀} {H : C₃ ⥤ C₂}
    {V₀ : C₂ ⥤ C₀} {V₁ : C₃ ⥤ C₁} {T U : C₃ ⥤ C₀}
    (s : H ⋙ V₀ ≅ V₁ ⋙ F) (c₀ : V₁ ⋙ F ≅ T) (c₁ : H ⋙ V₀ ≅ U)
    (e : U = T) (h : WholeContractionEquation s c₀ c₁ (eqToHom e))
    (M : C₃) {N : C₀} (r : T.obj M ⟶ N) :
    s.hom.app M ≫ c₀.hom.app M ≫ r =
      c₁.hom.app M ≫ eqToHom (Functor.congr_obj e M) ≫ r := by
  change s.hom ≫ c₀.hom = c₁.hom ≫ eqToHom e at h
  have hc := NatTrans.congr_app h M
  simp only [NatTrans.comp_app, eqToHom_app] at hc
  have hr := congrArg (fun k => k ≫ r) hc
  simpa only [Category.assoc] using hr

/-- Whole square/triangle pasting on the supplied original right comparisons. -/
def WholeSquareTriangleEquation {F : C₁ ⥤ C₀} {H : C₃ ⥤ C₂}
    {V₀ : C₂ ⥤ C₀} {V₁ : C₃ ⥤ C₁}
    {P₀ : C₄ ⥤ C₀} {P₁ : C₄ ⥤ C₁} {Q₀ : C₄ ⥤ C₂} {Q₁ : C₄ ⥤ C₃}
    (t_h : Q₁ ⋙ H ≅ Q₀) (t₀ : Q₀ ⋙ V₀ ≅ P₀)
    (t₁ : Q₁ ⋙ V₁ ≅ P₁) (t_f : P₁ ⋙ F ≅ P₀) (s : H ⋙ V₀ ≅ V₁ ⋙ F) : Prop :=
  Functor.whiskerRight t_h.hom V₀ ≫ t₀.hom =
    (Functor.associator Q₁ H V₀).hom ≫ Functor.whiskerLeft Q₁ s.hom ≫
      (Functor.associator Q₁ V₁ F).inv ≫ Functor.whiskerRight t₁.hom F ≫ t_f.hom

/-- Evaluate the whole law directly at those same comparison heads. -/
theorem square_triangle_app {F : C₁ ⥤ C₀} {H : C₃ ⥤ C₂}
    {V₀ : C₂ ⥤ C₀} {V₁ : C₃ ⥤ C₁}
    {P₀ : C₄ ⥤ C₀} {P₁ : C₄ ⥤ C₁} {Q₀ : C₄ ⥤ C₂} {Q₁ : C₄ ⥤ C₃}
    (t_h : Q₁ ⋙ H ≅ Q₀) (t₀ : Q₀ ⋙ V₀ ≅ P₀)
    (t₁ : Q₁ ⋙ V₁ ≅ P₁) (t_f : P₁ ⋙ F ≅ P₀) (s : H ⋙ V₀ ≅ V₁ ⋙ F)
    (h : WholeSquareTriangleEquation t_h t₀ t₁ t_f s) (K : C₄) :
    V₀.map (t_h.hom.app K) ≫ t₀.hom.app K =
      s.hom.app (Q₁.obj K) ≫ F.map (t₁.hom.app K) ≫ t_f.hom.app K := by
  dsimp only [WholeSquareTriangleEquation] at h
  have hc := NatTrans.congr_app h K
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] using hc

end CategoryTheory.Adjunction.RightTriangleCalculus

namespace CategoryTheory.InjectiveSystem.AdjunctionData

universe uJ vJ uA vA

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃

variable {J : Type uJ} [Category.{vJ} J]
  {A : J → Type uA} [∀ j, Category.{vA} (A j)]
  (D : InjectiveSystem.AdjunctionData A) (hD : D.Coherent)

/-- Contract the original square comparison as a whole transformation. -/
theorem squareRightIso_comp_whole {X₀ X₁ Y₀ Y₁ : J}
    (f : X₀ ⟶ X₁) (h : Y₀ ⟶ Y₁) (v₀ : X₀ ⟶ Y₀) (v₁ : X₁ ⟶ Y₁)
    (he : f ≫ v₁ = v₀ ≫ h) :
    (D.squareRightIso v₀ v₁ f h he).hom ≫ (D.compIso f v₁).inv =
      (D.compIso v₀ h).inv ≫ eqToHom (congrArg D.right he.symm) := by
  simp only [squareRightIso, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- Append the given original arrow to the proved square contraction. -/
theorem squareRightIso_comp_app {X₀ X₁ Y₀ Y₁ : J}
    (f : X₀ ⟶ X₁) (h : Y₀ ⟶ Y₁) (v₀ : X₀ ⟶ Y₀) (v₁ : X₁ ⟶ Y₁)
    (he : f ≫ v₁ = v₀ ≫ h) (M : A Y₁) {N : A X₀}
    (r : (D.right (f ≫ v₁)).obj M ⟶ N) :
    (D.squareRightIso v₀ v₁ f h he).hom.app M ≫
        (D.compIso f v₁).inv.app M ≫ r =
      (D.compIso v₀ h).inv.app M ≫
        eqToHom (congrArg (fun s => (D.right s).obj M) he.symm) ≫ r := by
  have hs := NatTrans.congr_app (D.squareRightIso_comp_whole f h v₀ v₁ he) M
  have hr := congrArg (fun k => k ≫ r) hs
  simpa only [NatTrans.comp_app, eqToHom_app, Category.assoc] using hr

include hD in
/-- The original square and its two paths to an apex agree as whole comparisons. -/
theorem squareRightIso_triangle_whole {X₀ X₁ Y₀ Y₁ T : J}
    (f : X₀ ⟶ X₁) (h : Y₀ ⟶ Y₁) (v₀ : X₀ ⟶ Y₀) (v₁ : X₁ ⟶ Y₁)
    (p₀ : X₀ ⟶ T) (p₁ : X₁ ⟶ T) (q₀ : Y₀ ⟶ T) (q₁ : Y₁ ⟶ T)
    (he : f ≫ v₁ = v₀ ≫ h) (hp : f ≫ p₁ = p₀) (hq : h ≫ q₁ = q₀)
    (hi : v₀ ≫ q₀ = p₀) (hj : v₁ ≫ q₁ = p₁) :
    Functor.whiskerRight (D.triangleRightIso q₀ h q₁ hq).hom (D.right v₀) ≫
        (D.triangleRightIso p₀ v₀ q₀ hi).hom =
      (Functor.associator (D.right q₁) (D.right h) (D.right v₀)).hom ≫
        Functor.whiskerLeft (D.right q₁) (D.squareRightIso v₀ v₁ f h he).hom ≫
          (Functor.associator (D.right q₁) (D.right v₁) (D.right f)).inv ≫
            Functor.whiskerRight (D.triangleRightIso p₁ v₁ q₁ hj).hom (D.right f) ≫
              (D.triangleRightIso p₀ f p₁ hp).hom := by
  apply NatTrans.ext
  funext K
  have hright := D.triangleRightIso_comp_transport_app hD f v₁ (f ≫ v₁)
    p₀ p₁ q₁ rfl hp hj (by rw [Category.assoc, hj, hp]) K
  simp only [eqToHom_refl, Category.id_comp] at hright
  have htransport := D.triangleRightIso_comp_transport_app hD v₀ h (f ≫ v₁)
    p₀ q₀ q₁ he hi hq (by rw [Category.assoc, hj, hp]) K
  have hsquare := D.squareRightIso_comp_app f h v₀ v₁ he ((D.right q₁).obj K)
    ((D.triangleRightIso p₀ (f ≫ v₁) q₁ (by rw [Category.assoc, hj, hp])).hom.app K)
  have hpath := congrArg
    (fun m => (D.squareRightIso v₀ v₁ f h he).hom.app ((D.right q₁).obj K) ≫ m) hright
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
  exact ((hpath.trans hsquare).trans htransport.symm).symm

include hD in
/-- The original left unit cancels the whole identity triangle. -/
theorem triangleIso_identity_whole {i t : J} (f : i ⟶ i) (e : f = 𝟙 i)
    (p : i ⟶ t) :
    (D.triangleIso p f p (by rw [e, Category.id_comp])).hom ≫
        Functor.whiskerRight
          (eqToHom (congrArg D.left e) ≫ (D.leftIdIso i).hom) (D.left p) ≫
          (Functor.leftUnitor (D.left p)).hom = 𝟙 _ := by
  cases e
  have hu := congrArg Iso.hom (D.leftCompIso_id_comp_whole hD p)
  have ht := congrArg
    (fun k => eqToHom (congrArg D.left (Category.id_comp p).symm) ≫ k) hu
  simp only [triangleIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    eqToIso.hom, eqToHom_refl, Category.id_comp, Category.assoc,
    eqToHom_trans] at ht ⊢
  exact ht

include hD in
/-- Evaluate the original whole identity triangle at its actual coefficient. -/
theorem triangleCoefficientMap_identity {i t : J} (f : i ⟶ i) (e : f = 𝟙 i)
    (p : i ⟶ t) (F : A i) :
    D.triangleCoefficientMap f p p (by rw [e, Category.id_comp])
      (eqToHom (congrArg (fun k => (D.left k).obj F) e) ≫
        (D.leftIdIso i).hom.app F) = 𝟙 ((D.left p).obj F) := by
  have h := NatTrans.congr_app (D.triangleIso_identity_whole hD f e p) F
  simp only [triangleCoefficientMap, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, eqToHom_app, NatTrans.id_app] at h ⊢
  exact (Category.comp_id _).symm.trans ((Category.assoc _ _ _).trans h)

include hD in
/-- The original coefficient composition law retains its equality transport. -/
theorem triangleCoefficientMap_comp_transport {x y z t : J}
    (f : x ⟶ y) (g : y ⟶ z) (d : x ⟶ z) (e : d = f ≫ g)
    (p : x ⟶ t) (q : y ⟶ t) (r : z ⟶ t)
    (hp : f ≫ q = p) (hq : g ≫ r = q)
    {F : A x} {G : A y} {H : A z}
    (φ : (D.left f).obj F ⟶ G) (ψ : (D.left g).obj G ⟶ H) :
    D.triangleCoefficientMap f p q hp φ ≫ D.triangleCoefficientMap g q r hq ψ =
      D.triangleCoefficientMap d p r (by rw [e, Category.assoc, hq, hp])
        (eqToHom (congrArg (fun k => (D.left k).obj F) e) ≫
          (D.leftCompIso f g).hom.app F ≫ (D.left g).map φ ≫ ψ) := by
  cases e
  simpa only [eqToHom_refl, Category.id_comp] using
    D.triangleCoefficientMap_comp hD f g p q r hp hq φ ψ

include hD in
/-- Precomposing an original triangle is the whole supplied left associativity law. -/
theorem triangleIso_precompose_whole {i j k t : J}
    (f : i ⟶ j) (b : j ⟶ k) (c : j ⟶ t) (a : k ⟶ t) (e : b ≫ a = c) :
    (D.leftCompIso f c).hom ≫
        Functor.whiskerLeft (D.left f) (D.triangleIso c b a e).hom =
      (D.triangleIso (f ≫ c) (f ≫ b) a
        ((Category.assoc f b a).trans (congrArg (fun k => f ≫ k) e))).hom ≫
        Functor.whiskerRight (D.leftCompIso f b).hom (D.left a) ≫
          (Functor.associator (D.left f) (D.left b) (D.left a)).hom := by
  cases e
  simpa only [triangleIso, Iso.trans_hom, eqToIso.hom, eqToHom_refl,
    Functor.whiskerLeft_comp, Functor.whiskerLeft_id', Category.id_comp, Category.assoc] using
      D.leftCompIso_assoc_whole hD f b a

private theorem inverse_whole_square {C : Type u₀} [Category.{v₀} C]
    {U V W Z : C} (i : U ≅ V) (j : W ≅ Z) (p : U ⟶ W) (q : V ⟶ Z)
    (h : p ≫ j.hom = i.hom ≫ q) : i.inv ≫ p = q ≫ j.inv := by
  apply (cancel_epi i.hom).1
  rw [← Category.assoc, i.hom_inv_id, Category.id_comp, ← Category.assoc,
    ← h, Category.assoc, j.hom_inv_id, Category.comp_id]

include hD in
/-- Inverse form of the same original whole relative triangle square. -/
theorem triangleIso_precompose_inv_whole {i j k t : J}
    (f : i ⟶ j) (b : j ⟶ k) (c : j ⟶ t) (a : k ⟶ t) (e : b ≫ a = c) :
    (D.triangleIso (f ≫ c) (f ≫ b) a
        ((Category.assoc f b a).trans (congrArg (fun k => f ≫ k) e))).inv ≫
      (D.leftCompIso f c).hom =
      (Functor.whiskerRight (D.leftCompIso f b).hom (D.left a) ≫
        (Functor.associator (D.left f) (D.left b) (D.left a)).hom) ≫
          Functor.whiskerLeft (D.left f) (D.triangleIso c b a e).inv :=
  inverse_whole_square _ (Functor.isoWhiskerLeft (D.left f) (D.triangleIso c b a e)) _ _
    (D.triangleIso_precompose_whole hD f b c a e)

private theorem mapped_section_square
    {C : Type u₀} [Category.{v₀} C] {E : Type u₁} [Category.{v₁} E]
    (G : C ⥤ E) {A B K H : C} {Z W : E}
    (q : A ⟶ B) (r : B ⟶ K) (s : A ⟶ H) (t : H ⟶ K)
    (p : Z ⟶ G.obj A) (w : Z ⟶ W) (p' : W ⟶ G.obj H)
    (h : q ≫ r = s ≫ t) (hn : w ≫ p' = p ≫ G.map s) :
    (p ≫ G.map q) ≫ G.map r = w ≫ p' ≫ G.map t := by
  rw [Category.assoc, ← G.map_comp, h, G.map_comp, ← Category.assoc, ← hn,
    Category.assoc]

private theorem section_square_whole
    {C : Type u₀} [Category.{v₀} C] {E : Type u₁} [Category.{v₁} E]
    {H : Type u₂} [Category.{v₂} H] {B : Type u₃} [Category.{v₃} B]
    (R S : C ⥤ E) (T U : C ⥤ H) (L : E ⥤ H)
    (GE : E ⥤ B) (GH : H ⥤ B) (P : GE ⟶ L ⋙ GH)
    (q : R ⋙ L ⟶ T) (r : T ⟶ U) (s : R ⟶ S) (t : S ⋙ L ⟶ U)
    (h : q ≫ r = Functor.whiskerRight s L ≫ t) :
    (Functor.whiskerLeft R P ≫ Functor.whiskerRight q GH) ≫
        Functor.whiskerRight r GH =
      Functor.whiskerRight s GE ≫ Functor.whiskerLeft S P ≫
        Functor.whiskerRight t GH := by
  ext F
  exact mapped_section_square GH _ _ _ _ _ _ _ (NatTrans.congr_app h F)
    (P.naturality (s.app F))

include hD in
/-- The complete original section square follows from the proved relative triangle. -/
theorem triangleIso_precompose_sections_whole {i j k t : J}
    (f : i ⟶ j) (b : j ⟶ k) (c : j ⟶ t) (a : k ⟶ t) (e : b ≫ a = c)
    {B : Type u₃} [Category.{v₃} B] (Γk : A k ⥤ B) (Γt : A t ⥤ B)
    (P : Γk ⟶ D.left a ⋙ Γt) :
    (Functor.whiskerLeft (D.left (f ≫ b)) P ≫
      Functor.whiskerRight (D.triangleIso (f ≫ c) (f ≫ b) a
        ((Category.assoc f b a).trans (congrArg (fun k => f ≫ k) e))).inv Γt) ≫
        Functor.whiskerRight (D.leftCompIso f c).hom Γt =
      Functor.whiskerRight (D.leftCompIso f b).hom Γk ≫
        Functor.whiskerLeft (D.left f ⋙ D.left b) P ≫
          Functor.whiskerRight
            (Functor.whiskerLeft (D.left f) (D.triangleIso c b a e).inv) Γt := by
  have hc := D.triangleIso_precompose_inv_whole hD f b c a e
  have ha : (Functor.associator (D.left f) (D.left b) (D.left a)).hom = 𝟙 _ := rfl
  simp only [ha, Category.comp_id] at hc
  exact section_square_whole (D.left (f ≫ b)) (D.left f ⋙ D.left b)
    (D.left (f ≫ c)) (D.left f ⋙ D.left c) (D.left a) Γk Γt P _ _ _ _ hc

/-- The whole transport law at the original comparisons, with their origins proved. -/
theorem triangleRightIso_transport_whole_of_eq {x y t : J}
    (f g : x ⟶ y) (e : f = g) (p : x ⟶ t) (q : y ⟶ t)
    (hf : f ≫ q = p) (hg : g ≫ q = p)
    (c : D.right f ⟶ D.right g)
    (a : D.right q ⋙ D.right f ≅ D.right p)
    (b : D.right q ⋙ D.right g ≅ D.right p)
    (hc : c = eqToHom (congrArg D.right e))
    (ha : a = D.triangleRightIso p f q hf) (hb : b = D.triangleRightIso p g q hg) :
    Adjunction.RightTriangleCalculus.WholeTransportEquation c a b := by
  cases hc
  cases ha
  cases hb
  exact D.triangleRightIso_transport_whole f g e p q hf hg

/-- Whole contraction uses the actual original square, compositors and transport. -/
theorem squareRightIso_comp_whole_of_eq {X₀ X₁ Y₀ Y₁ : J}
    (f : X₀ ⟶ X₁) (h : Y₀ ⟶ Y₁) (v₀ : X₀ ⟶ Y₀) (v₁ : X₁ ⟶ Y₁)
    (he : f ≫ v₁ = v₀ ≫ h)
    (s : D.right h ⋙ D.right v₀ ≅ D.right v₁ ⋙ D.right f)
    (c₀ : D.right v₁ ⋙ D.right f ≅ D.right (f ≫ v₁))
    (c₁ : D.right h ⋙ D.right v₀ ≅ D.right (v₀ ≫ h))
    (t : D.right (v₀ ≫ h) ⟶ D.right (f ≫ v₁))
    (hs : s = D.squareRightIso v₀ v₁ f h he)
    (hc₀ : c₀ = (D.compIso f v₁).symm) (hc₁ : c₁ = (D.compIso v₀ h).symm)
    (ht : t = eqToHom (congrArg D.right he.symm)) :
    Adjunction.RightTriangleCalculus.WholeContractionEquation s c₀ c₁ t := by
  cases hs
  cases hc₀
  cases hc₁
  cases ht
  exact D.squareRightIso_comp_whole f h v₀ v₁ he

include hD in
/-- Whole pasting retains the five original comparisons before any evaluation. -/
theorem squareRightIso_triangle_whole_of_eq {X₀ X₁ Y₀ Y₁ T : J}
    (f : X₀ ⟶ X₁) (h : Y₀ ⟶ Y₁) (v₀ : X₀ ⟶ Y₀) (v₁ : X₁ ⟶ Y₁)
    (p₀ : X₀ ⟶ T) (p₁ : X₁ ⟶ T) (q₀ : Y₀ ⟶ T) (q₁ : Y₁ ⟶ T)
    (he : f ≫ v₁ = v₀ ≫ h) (hp : f ≫ p₁ = p₀) (hq : h ≫ q₁ = q₀)
    (hi : v₀ ≫ q₀ = p₀) (hj : v₁ ≫ q₁ = p₁)
    (t_h : D.right q₁ ⋙ D.right h ≅ D.right q₀)
    (t₀ : D.right q₀ ⋙ D.right v₀ ≅ D.right p₀)
    (t₁ : D.right q₁ ⋙ D.right v₁ ≅ D.right p₁)
    (t_f : D.right p₁ ⋙ D.right f ≅ D.right p₀)
    (s : D.right h ⋙ D.right v₀ ≅ D.right v₁ ⋙ D.right f)
    (hh : t_h = D.triangleRightIso q₀ h q₁ hq)
    (h₀ : t₀ = D.triangleRightIso p₀ v₀ q₀ hi)
    (h₁ : t₁ = D.triangleRightIso p₁ v₁ q₁ hj)
    (hf : t_f = D.triangleRightIso p₀ f p₁ hp)
    (hs : s = D.squareRightIso v₀ v₁ f h he) :
    Adjunction.RightTriangleCalculus.WholeSquareTriangleEquation t_h t₀ t₁ t_f s := by
  cases hh
  cases h₀
  cases h₁
  cases hf
  cases hs
  exact D.squareRightIso_triangle_whole hD f h v₀ v₁ p₀ p₁ q₀ q₁ he hp hq hi hj

include hD in
/-- Extending an original triangle is the whole original left-composition law. -/
theorem triangleIso_postcompose_whole {i j t v : J}
    (f : i ⟶ j) (p : i ⟶ t) (q : j ⟶ t) (h : f ≫ q = p) (l : t ⟶ v) :
    (D.triangleIso (p ≫ l) f (q ≫ l)
        ((Category.assoc f q l).symm.trans (congrArg (fun k => k ≫ l) h))).hom ≫
        Functor.whiskerLeft (D.left f) (D.leftCompIso q l).hom =
      (D.leftCompIso p l).hom ≫
        Functor.whiskerRight (D.triangleIso p f q h).hom (D.left l) ≫
          (Functor.associator (D.left f) (D.left q) (D.left l)).hom := by
  cases h
  have hc := D.leftCompIso_assoc_whole hD f q l
  have ht := congrArg
    (fun k => eqToHom (congrArg D.left (Category.assoc f q l)) ≫ k) hc
  simpa only [triangleIso, Iso.trans_hom, eqToIso.hom, eqToHom_refl,
    Category.id_comp, Category.assoc, eqToHom_trans_assoc] using ht

include hD in
/-- The whole law at the actual supplied comparisons, identified with the same coherent data. -/
theorem triangleIso_postcompose_whole_of_eq {i j t v : J}
    (f : i ⟶ j) (p : i ⟶ t) (q : j ⟶ t) (h : f ≫ q = p) (l : t ⟶ v)
    (ep : D.left (p ≫ l) ≅ D.left p ⋙ D.left l)
    (eq : D.left (q ≫ l) ≅ D.left q ⋙ D.left l)
    (a : D.left p ≅ D.left f ⋙ D.left q)
    (b : D.left (p ≫ l) ≅ D.left f ⋙ D.left (q ≫ l))
    (hep : ep = D.leftCompIso p l) (heq : eq = D.leftCompIso q l)
    (ha : a = D.triangleIso p f q h)
    (hb : b = D.triangleIso (p ≫ l) f (q ≫ l)
      ((Category.assoc f q l).symm.trans (congrArg (fun k => k ≫ l) h))) :
    b.hom ≫ Functor.whiskerLeft (D.left f) eq.hom =
      ep.hom ≫ Functor.whiskerRight a.hom (D.left l) ≫
        (Functor.associator (D.left f) (D.left q) (D.left l)).hom := by
  cases hep
  cases heq
  cases ha
  cases hb
  exact D.triangleIso_postcompose_whole hD f p q h l

end CategoryTheory.InjectiveSystem.AdjunctionData

namespace CategoryTheory.InjectiveSystem.AdjunctionData.Cone

universe uI vI uA vA uB vB uC vC uT vT

variable {I : Type uI} [Category.{vI} I]
  {A : I → Type uA} [∀ i, Category.{vA} (A i)]
  {D : InjectiveSystem.AdjunctionData A}
  {B : Type uB} [Category.{vB} B] {C : Type uC} [Category.{vC} C]
  (P : D.Cone B) (Q : D.Cone C) (L : B ⥤ C)
  (e : ∀ i, Q.left i ≅ P.left i ⋙ L)
  (h : ∀ {i j : I} (a : i ⟶ j),
    (Q.leftTriangle a).hom ≫ Functor.whiskerLeft (D.left a) (e j).hom =
      (e i).hom ≫ Functor.whiskerRight (P.leftTriangle a).hom L ≫
        (Functor.associator (D.left a) (P.left j) L).hom)
  (F : InjectiveSystem.System D)

include h in
/-- Whole triangle compatibility and actual component naturality give the extension square. -/
theorem coefficientMap_extension_naturality {i j : I} (a : i ⟶ j) :
    Q.coefficientMap F a ≫ (e j).hom.app (F.obj j) =
      (e i).hom.app (F.obj i) ≫ L.map (P.coefficientMap F a) := by
  have ht := NatTrans.congr_app (h a) (F.obj i)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id] at ht
  change ((Q.leftTriangle a).hom.app (F.obj i) ≫
      (Q.left j).map (F.leftMap D a)) ≫ (e j).hom.app (F.obj j) =
    (e i).hom.app (F.obj i) ≫
      L.map ((P.leftTriangle a).hom.app (F.obj i) ≫ (P.left j).map (F.leftMap D a))
  rw [Category.assoc, (e j).hom.naturality (F.leftMap D a), ← Category.assoc, ht,
    L.map_comp, Category.assoc, Functor.comp_map]

/-- Extend the original coefficient functor through its actual supplied stage comparisons. -/
def coefficientExtendIso : Q.coefficientFunctor F ≅ P.coefficientFunctor F ⋙ L :=
  NatIso.ofComponents (fun i => (e i).app (F.obj i))
    (fun {i j} a => coefficientMap_extension_naturality P Q L e h F (i := i) (j := j) a)

/-- Its component is exactly the original supplied left-composition component. -/
theorem coefficientExtendIso_hom_app (i : I) :
    (coefficientExtendIso P Q L e h F).hom.app i = (e i).hom.app (F.obj i) := rfl

variable {T : Type uT} [Category.{vT} T]
  (Γ : C ⥤ T) (E : B ⥤ T) (s : L ⋙ Γ ≅ E)

/-- The complete original section comparison after extending the same coefficient diagram. -/
def coefficientExtendSectionsIso :
    Q.coefficientFunctor F ⋙ Γ ≅ P.coefficientFunctor F ⋙ E :=
  Functor.isoWhiskerRight (coefficientExtendIso P Q L e h F) Γ ≪≫
    Functor.associator (P.coefficientFunctor F) L Γ ≪≫
    Functor.isoWhiskerLeft (P.coefficientFunctor F) s

/-- The original whole section construction at an arbitrary original stage. -/
theorem coefficientExtendSectionsIso_hom_app (i : I) :
    (coefficientExtendSectionsIso P Q L e h F Γ E s).hom.app i =
      Γ.map ((e i).hom.app (F.obj i)) ≫ s.hom.app ((P.left i).obj (F.obj i)) := by
  change Γ.map ((e i).hom.app (F.obj i)) ≫
    (𝟙 _ ≫ s.hom.app ((P.left i).obj (F.obj i))) = _
  rw [Category.id_comp]

/-- Evaluate the whole comparison directly at the supplied original section arrow. -/
theorem coefficientExtendSectionsIso_hom_app_eq (i : I)
    (a : Γ.obj ((Q.left i).obj (F.obj i)) ⟶ E.obj ((P.left i).obj (F.obj i)))
    (ha : Γ.map ((e i).hom.app (F.obj i)) ≫
      s.hom.app ((P.left i).obj (F.obj i)) = a) :
    (coefficientExtendSectionsIso P Q L e h F Γ E s).hom.app i = a :=
  (coefficientExtendSectionsIso_hom_app P Q L e h F Γ E s i).trans ha

end CategoryTheory.InjectiveSystem.AdjunctionData.Cone
