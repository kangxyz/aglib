/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.ConeExtension

/-! # Ordinary pasting through the original inverse triangles

The inverse component of the existing adjunction-data triangle carries the
original equality transport and canonical composition map. Whole triangle,
local coefficient and square routes are assembled here before geometry or
cohomology is specialized. No second action or comparison model is chosen.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle

theorem cancel_right_pair {V : Type*} [Category V] {A B C D E : V}
    (a : A ≅ B) (b : B ⟶ C) (c : D ≅ C) (d : E ≅ D) (e : A ⟶ E)
    (h : a.hom ≫ b = e ≫ d.hom ≫ c.hom) :
    b ≫ c.inv ≫ d.inv = a.inv ≫ e := by
  apply (cancel_epi a.hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
    using congrArg (fun q => q ≫ c.inv ≫ d.inv) h

theorem factor_inverse {V : Type*} [Category V] {X Y Z T : V}
    (a : X ⟶ Y) (b : Y ≅ Z) (c : Z ≅ T) (d : X ≅ T)
    (h : a ≫ b.hom ≫ c.hom = d.hom) :
    c.inv ≫ b.inv = d.inv ≫ a := by
  apply (cancel_epi d.hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
    using (congrArg (fun q => q ≫ c.inv ≫ b.inv) h).symm

universe uJ vJ uA vA

variable {J : Type uJ} [Category.{vJ} J]
  {A : Jᵒᵖ → Type uA} [∀ X, Category.{vA} (A X)]
  (D : InjectiveSystem.AdjunctionData A)

/-- The same selected left functor, viewed in the original pullback direction. -/
abbrev pull {X Y : J} (f : Y ⟶ X) : A (op X) ⥤ A (op Y) := D.left f.op

/-- The original canonical left comparison at the actual two indexing arrows. -/
abbrev composition {X Y Z : J} (f : Y ⟶ X) (g : Z ⟶ Y) :
    pull D (g ≫ f) ≅ pull D f ⋙ pull D g := D.leftCompIso f.op g.op

/-- The inverse component of the existing original whole triangle. -/
def iso {B X Y : J} (p : X ⟶ B) (f : Y ⟶ X) (q : Y ⟶ B)
    (hf : f ≫ p = q) (L : A (op B)) :
    (pull D f).obj ((pull D p).obj L) ≅ (pull D q).obj L :=
  ((D.triangleIso q.op p.op f.op (congrArg Quiver.Hom.op hf)).app L).symm

/-- The original composition inverse followed by the literal equality transport. -/
theorem iso_eq_composition {B X Y : J} (p : X ⟶ B) (f : Y ⟶ X)
    (q : Y ⟶ B) (hf : f ≫ p = q) (L : A (op B)) :
    iso D p f q hf L = ((composition D p f).app L).symm ≪≫
      eqToIso (congrArg (fun k => (pull D k).obj L) hf) := by
  subst q
  simp only [iso, InjectiveSystem.AdjunctionData.triangleIso,
    eqToIso_refl, Iso.refl_trans, composition, Iso.trans_refl]

/-- Native triangle composition, through the same original comparisons. -/
theorem comp (hD : D.Coherent) {B X Y Z : J}
    (p : X ⟶ B) (f : Y ⟶ X) (g : Z ⟶ Y)
    (q : Y ⟶ B) (hf : f ≫ p = q) (r : Z ⟶ B) (hg : g ≫ q = r)
    {L : A (op B)} :
    (composition D f g).hom.app ((pull D p).obj L) ≫
        (pull D g).map (iso D p f q hf L).hom ≫ (iso D q g r hg L).hom =
      (iso D p (g ≫ f) r
        ((Category.assoc g f p).trans ((congrArg (fun k => g ≫ k) hf).trans hg)) L).hom := by
  let h := (Category.assoc g f p).trans ((congrArg (fun k => g ≫ k) hf).trans hg)
  have ht := D.triangleIso_comp hD p.op q.op r.op g.op f.op
    (congrArg Quiver.Hom.op hf) (congrArg Quiver.Hom.op hg) L
  have hc := cancel_right_pair
    ((D.triangleIso r.op p.op (g ≫ f).op (congrArg Quiver.Hom.op h)).app L)
    ((composition D f g).hom.app ((pull D p).obj L))
    ((pull D g).mapIso
      ((D.triangleIso q.op p.op f.op (congrArg Quiver.Hom.op hf)).app L))
    ((D.triangleIso r.op q.op g.op (congrArg Quiver.Hom.op hg)).app L)
    (𝟙 _) (by
      simpa only [Category.id_comp, Functor.mapIso_hom, Iso.app_hom,
        pull, composition, op_comp] using ht)
  simpa only [iso, Iso.symm_hom, Iso.app_inv, Functor.mapIso_inv,
    Category.comp_id] using hc

/-- The same inverse triangle is natural in the actual coefficient arrow. -/
theorem naturality {B X Y : J} (p : X ⟶ B) (f : Y ⟶ X)
    (r : Y ⟶ B) (hf : f ≫ p = r) {L N : A (op B)} (q : L ⟶ N) :
    (pull D f).map ((pull D p).map q) ≫ (iso D p f r hf N).hom =
      (iso D p f r hf L).hom ≫ (pull D r).map q := by
  simpa only [iso, Iso.symm_hom, Iso.app_inv, Functor.comp_map] using
    (D.triangleIso r.op p.op f.op (congrArg Quiver.Hom.op hf)).inv.naturality q

/-- The inverse of the actual original triangle, with its literal factors. -/
theorem inv_formula {B X Y : J} (p : X ⟶ B) (f : Y ⟶ X)
    (q : Y ⟶ B) (hf : f ≫ p = q) (L : A (op B)) :
    (iso D p f q hf L).inv =
      (eqToIso (congrArg (fun k => (pull D k).obj L) hf)).inv ≫
        (composition D p f).hom.app L := by
  rw [iso_eq_composition]
  rfl

/-- Composition with the original inverse triangle gives exactly its equality map. -/
theorem comp_iso_hom {X Y Z : J} (g : Y ⟶ X) (m : Z ⟶ Y) (r : Z ⟶ X)
    (hm : m ≫ g = r) (L : A (op X)) :
    (composition D g m).hom.app L ≫ (iso D g m r hm L).hom =
      (eqToIso (congrArg (fun k => (pull D k).obj L) hm)).hom := by
  rw [iso_eq_composition]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.hom_inv_id_app_assoc]

theorem comp_inv (hD : D.Coherent) {B X Y Z : J}
    (p : X ⟶ B) (f : Y ⟶ X) (g : Z ⟶ Y)
    (q : Y ⟶ B) (hf : f ≫ p = q) (r : Z ⟶ B) (hg : g ≫ q = r)
    {L : A (op B)} :
    (composition D f g).hom.app ((pull D p).obj L) ≫
        (pull D g).map (iso D p f q hf L).hom =
      (iso D p (g ≫ f) r
        ((Category.assoc g f p).trans ((congrArg (fun k => g ≫ k) hf).trans hg)) L).hom ≫
        (iso D q g r hg L).inv := by
  apply (cancel_mono (iso D q g r hg L).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact comp D hD p f g q hf r hg

theorem congr {B X Y : J} (p : X ⟶ B)
    {f g : Y ⟶ X} (e : f = g) (q : Y ⟶ B) (hf : f ≫ p = q) (hg : g ≫ p = q)
    (L : A (op B)) :
    (eqToIso (congrArg (fun k => (pull D k).obj ((pull D p).obj L)) e)).hom ≫
        (iso D p g q hg L).hom = (iso D p f q hf L).hom := by
  subst g
  simp

theorem assoc_inv (hD : D.Coherent) {B X Y Z : J} (b : X ⟶ B) (f : Y ⟶ X) (g : Z ⟶ Y)
    (r : Z ⟶ B) (h : g ≫ (f ≫ b) = r)
    {L : A (op B)} :
    (iso D (f ≫ b) g r h L).inv ≫
      (pull D g).map ((composition D b f).hom.app L) =
    (iso D b (g ≫ f) r ((Category.assoc g f b).trans h) L).inv ≫
      (composition D f g).hom.app ((pull D b).obj L) := by
  have ht := comp D hD b f g (f ≫ b) rfl r h (L := L)
  have hi := factor_inverse
    ((composition D f g).hom.app ((pull D b).obj L))
    ((pull D g).mapIso (iso D b f (f ≫ b) rfl L))
    (iso D (f ≫ b) g r h L)
    (iso D b (g ≫ f) r ((Category.assoc g f b).trans h) L) ht
  simpa only [iso_eq_composition, Iso.trans_inv, Iso.symm_inv, Iso.app_hom, eqToIso_refl,
    Iso.refl_inv, Category.id_comp, Functor.mapIso_inv] using hi

theorem congr_inv {B X Z : J} (p : X ⟶ B) {f g : Z ⟶ X}
    (e : f = g)
    (r : Z ⟶ B) (hf : f ≫ p = r) (hg : g ≫ p = r) (L : A (op B)) :
    (iso D p f r hf L).inv = (iso D p g r hg L).inv ≫
      (eqToIso (congrArg (fun k => (pull D k).obj ((pull D p).obj L)) e)).inv := by
  subst g
  simp

theorem route (hD : D.Coherent) {B X Y Z : J} (p : X ⟶ B) (f : Y ⟶ X) (g : Z ⟶ Y)
    (q : Y ⟶ B) (hf : f ≫ p = q) (r : Z ⟶ B) (hg : g ≫ q = r)
    {L : A (op B)}
    {N : A (op Y)} {Q : A (op Z)}
    (e : (pull D q).obj L ⟶ N) (s : (pull D g).obj N ⟶ Q) :
    (composition D f g).hom.app ((pull D p).obj L) ≫
      (pull D g).map ((iso D p f q hf L).hom ≫ e) ≫ s =
    (iso D p (g ≫ f) r
      ((Category.assoc g f p).trans ((congrArg (fun k => g ≫ k) hf).trans hg)) L).hom ≫
      (iso D q g r hg L).inv ≫ (pull D g).map e ≫ s := by
  have h := comp_inv D hD p f g q hf r hg (L := L)
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun t => t ≫ (pull D g).map e ≫ s) h

theorem route_explicit (hD : D.Coherent) {B X Y Z : J} (p : X ⟶ B) (f : Y ⟶ X) (g : Z ⟶ Y)
    (q : Y ⟶ B) (hf : f ≫ p = q) (r : Z ⟶ B) (hg : g ≫ q = r)
    {L : A (op B)}
    {N : A (op Y)} {Q : A (op Z)}
    (e : (pull D q).obj L ⟶ N) (s : (pull D g).obj N ⟶ Q) :
    (composition D f g).hom.app ((pull D p).obj L) ≫
      (pull D g).map ((iso D p f q hf L).hom ≫ e) ≫ s =
    (iso D p (g ≫ f) r
      ((Category.assoc g f p).trans ((congrArg (fun k => g ≫ k) hf).trans hg)) L).hom ≫
      (eqToIso (congrArg (fun k => (pull D k).obj L) hg)).inv ≫
      (composition D q g).hom.app L ≫ (pull D g).map e ≫ s := by
  simpa only [inv_formula D, Category.assoc] using
    route D hD p f g q hf r hg e s

theorem coefficient_route_naturality {B C X Y : J}
    (p : X ⟶ B) (f : Y ⟶ X) (b : C ⟶ B) (g : Y ⟶ C) (hf : f ≫ p = g ≫ b)
    {L N : A (op B)} {M : A (op C)}
    {Q : A (op Y)} (a : L ⟶ N)
    (e : (pull D b).obj N ⟶ M) (r : (pull D g).obj M ⟶ Q) :
    (pull D f).map ((pull D p).map a) ≫
      (iso D p f (g ≫ b) hf N).hom ≫ (composition D b g).hom.app N ≫
      (pull D g).map e ≫ r =
    (iso D p f (g ≫ b) hf L).hom ≫ (composition D b g).hom.app L ≫
      (pull D g).map ((pull D b).map a ≫ e) ≫ r := by
  rw [reassoc_of% (naturality D p f (g ≫ b) hf a)]
  rw [reassoc_of% ((composition D b g).hom.naturality a)]
  simp only [Functor.map_comp, Category.assoc]

theorem coefficient_route_iso {B C X Y : J}
    (p : X ⟶ B) (f : Y ⟶ X) (b : C ⟶ B) (g : Y ⟶ C) (hf : f ≫ p = g ≫ b)
    {L N : A (op B)} {M : A (op C)}
    {Q : A (op Y)} (a : L ≅ N)
    (e : (pull D b).obj N ≅ M) (r : (pull D g).obj M ≅ Q) :
    ((pull D f).mapIso ((pull D p).mapIso a)).hom ≫
      (iso D p f (g ≫ b) hf N ≪≫ (composition D b g).app N ≪≫
        (pull D g).mapIso e ≪≫ r).hom =
    (((composition D p f).app L).symm ≪≫
      eqToIso (congrArg (fun t => (pull D t).obj L) hf) ≪≫
      (composition D b g).app L ≪≫
      (pull D g).mapIso ((pull D b).mapIso a ≪≫ e) ≪≫ r).hom := by
  simpa only [iso_eq_composition, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Iso.app_hom, Functor.mapIso_hom, Category.assoc] using
    coefficient_route_naturality D p f b g hf a.hom e.hom r.hom

theorem coefficient_transport_eq {B X Y : J}
    (p : X ⟶ B) (k : Y ⟶ X) (q : Y ⟶ B) (hk : k ≫ p = q)
    {L N : A (op B)} {P : A (op X)}
    {Q : A (op Y)} (α : L ⟶ N)
    (c : (pull D p).obj L ⟶ P) (r : (pull D k).obj P ⟶ Q)
    (s : (pull D q).obj N ⟶ Q)
    (he : (composition D p k).hom.app L ≫ (pull D k).map c ≫ r =
      (eqToIso (congrArg (fun f => (pull D f).obj L) hk)).hom ≫
        (pull D q).map α ≫ s) :
    (pull D k).map ((pull D p).map α) ≫
      (iso D p k q hk N).hom ≫ s = (pull D k).map c ≫ r := by
  rw [reassoc_of% (naturality D p k q hk α)]
  apply (cancel_epi ((composition D p k).hom.app L)).mp
  simpa only [iso_eq_composition, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Category.assoc, Iso.hom_inv_id_app_assoc] using he.symm

theorem triangle_pasting (hD : D.Coherent) {B X Y Z : J}
    (p : X ⟶ B) (l : Y ⟶ X) (g : Z ⟶ Y) (k : Z ⟶ X) (hgl : g ≫ l = k)
    (r : Y ⟶ B) (hl : l ≫ p = r) (s : Z ⟶ B) (hg : g ≫ r = s)
    (hk : k ≫ p = s) {T : A (op B)} :
    (pull D g).map (iso D p
      l r
        hl T).hom ≫
      (iso D r g s hg T).hom =
    (iso D l g k hgl ((pull D
        p).obj T)).hom ≫
      (iso D p k s hk T).hom := by
  apply (cancel_epi ((composition D l g).hom.app ((pull D p).obj T))).mp
  rw [comp D hD p l g r hl s hg]
  have ht := congr D p hgl s
    ((Category.assoc g l p).trans ((congrArg (fun a => g ≫ a) hl).trans hg)) hk T
  simpa only [iso_eq_composition, Iso.trans_hom,
      Iso.symm_hom,
    Iso.app_inv, Category.assoc, Iso.hom_inv_id_app_assoc] using ht.symm

/-- Pull a coefficient isomorphism along two legs, then apply the
ordinary triangle comparison. -/
def localIso {B X Y : J} (p : X ⟶ B) (l : Y ⟶ X) (r : Y ⟶ B)
    (hl : l ≫ p = r) {L T : A (op B)} (alpha : L ≅ T) :
    (pull D l).obj ((pull D p).obj L) ≅ (pull D r).obj T :=
  (pull D l).mapIso ((pull D p).mapIso alpha) ≪≫
    iso D p l r hl T

theorem local_pasting (hD : D.Coherent) {B X Y Z : J}
    (p : X ⟶ B) (l : Y ⟶ X) (g : Z ⟶ Y) (k : Z ⟶ X) (hgl : g ≫ l = k)
    (r : Y ⟶ B) (hl : l ≫ p = r) (s : Z ⟶ B) (hg : g ≫ r = s)
    (hk : k ≫ p = s) {L T : A (op B)} (alpha : L ≅ T) :
    (pull D g).map (localIso D p l r hl alpha).hom ≫
      (iso D r g s hg T).hom =
    (iso D l g k hgl ((pull D
        p).obj L)).hom ≫
      (localIso D p k s hk alpha).hom := by
  simp only [localIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [triangle_pasting D hD p l g k hgl r hl s hg hk]
  rw [reassoc_of%
    (naturality D l
      g k hgl
    ((pull D p).map alpha.hom))]

theorem local_inv_pasting (hD : D.Coherent) {B X Y Z : J}
    (p : X ⟶ B) (l : Y ⟶ X) (g : Z ⟶ Y) (k : Z ⟶ X) (hgl : g ≫ l = k)
    (r : Y ⟶ B) (hl : l ≫ p = r) (s : Z ⟶ B) (hg : g ≫ r = s)
    (hk : k ≫ p = s) {L T : A (op B)} (alpha : L ≅ T) :
    (pull D g).map (localIso D p l r hl alpha).inv ≫
      (iso D l g k hgl
        ((pull D
          p).obj L)).hom ≫
      (localIso D p k s hk alpha).hom =
        (iso D r g s hg T).hom :=
          by
  rw [← local_pasting D hD p l g k hgl r hl s hg hk alpha]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

theorem coefficient_route_inner (hD : D.Coherent) {B X Y Z : J} (b : X ⟶ B) (g : Y ⟶ X) (m : Z ⟶ Y)
    (r : Z ⟶ X) (hm : m ≫ g = r) (q : Z ⟶ B) (hq : r ≫ b = q)
    {L : A (op B)}
    {N : A (op X)} {Q : A (op Z)}
    (e : (pull D b).obj L ⟶ N) (d : (pull D r).obj N ⟶ Q) :
    (iso D (g ≫ b) m q
      ((Category.assoc m g b).symm.trans ((congrArg (fun t => t ≫ b) hm).trans hq)) L).inv ≫
      (pull D m).map ((composition D b g).hom.app L ≫ (pull D g).map e) ≫
      (iso D g m r hm N).hom ≫ d =
    (iso D b r q hq L).inv ≫ (pull D r).map e ≫ d := by
  let hb : m ≫ (g ≫ b) = q := (Category.assoc m g b).symm.trans
    ((congrArg (fun t => t ≫ b) hm).trans hq)
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% (naturality D g m r hm e)]
  rw [reassoc_of% (assoc_inv D hD b g m q hb (L := L))]
  rw [congr_inv D b hm q _ hq L]
  simp only [Category.assoc]
  rw [reassoc_of% (comp_iso_hom D g m r hm ((pull D b).obj L))]
  simp only [Iso.inv_hom_id_assoc]

theorem coefficient_square_route (hD : D.Coherent) {B X Y Z U : J} (p : U ⟶ B) (f : Y ⟶ U)
    (b : X ⟶ B) (g : Y ⟶ X) (hf : f ≫ p = g ≫ b) (m : Z ⟶ Y)
    (r : Z ⟶ X) (hm : m ≫ g = r) (q : Z ⟶ B) (hq : r ≫ b = q)
    {L : A (op B)}
    {N : A (op X)} {Q : A (op Z)}
    (e : (pull D b).obj L ⟶ N) (d : (pull D r).obj N ⟶ Q) :
    (composition D f m).hom.app ((pull D p).obj L) ≫
      (pull D m).map ((iso D p f (g ≫ b) hf L).hom ≫
        (composition D b g).hom.app L ≫ (pull D g).map e) ≫
      (iso D g m r hm N).hom ≫ d =
    (iso D p (m ≫ f) q
      ((Category.assoc m f p).trans ((congrArg (fun t => m ≫ t) hf).trans
        ((Category.assoc m g b).symm.trans ((congrArg (fun t => t ≫ b) hm).trans hq)))) L).hom ≫
      (iso D b r q hq L).inv ≫ (pull D r).map e ≫ d := by
  let hb : m ≫ (g ≫ b) = q := (Category.assoc m g b).symm.trans
    ((congrArg (fun t => t ≫ b) hm).trans hq)
  have ho := route D hD p f m (g ≫ b) hf q hb (L := L)
    ((composition D b g).hom.app L ≫ (pull D g).map e)
    ((iso D g m r hm N).hom ≫ d)
  have hi := coefficient_route_inner D hD b g m r hm q hq e d
  have ht := congrArg (fun t =>
    (iso D p (m ≫ f) q
      ((Category.assoc m f p).trans ((congrArg (fun t => m ≫ t) hf).trans hb)) L).hom ≫ t) hi
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using ho.trans ht

end CategoryTheory.InjectiveSystem.AdjunctionData.OrdinaryTriangle
