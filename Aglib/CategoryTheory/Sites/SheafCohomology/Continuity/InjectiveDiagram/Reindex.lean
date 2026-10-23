/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.SystemCoherence

/-! # Reindexing the actual adjunction data of coefficient systems

Restriction along an indexing functor preserves the original identity and
composition comparisons, with explicit transport by the functor laws. This
allows the injective-system producer to apply to an arbitrary specified diagram,
without extending a coefficient system to all objects of a larger category.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.InjectiveSystem

universe vI vJ vA uI uJ uA

variable {I : Type uI} [Category.{vI} I]
  {J : Type uJ} [Category.{vJ} J]
  {A : I → Type uA} [∀ i, Category.{vA} (A i)]
  (D : AdjunctionData A) (K : J ⥤ I)

/-- Reindex actual adjunctions, retaining functor-law equality transports in
the original identity and composition comparisons. -/
def AdjunctionData.reindex : AdjunctionData (fun j => A (K.obj j)) where
  left a := D.left (K.map a)
  right a := D.right (K.map a)
  adj a := D.adj (K.map a)
  left_preservesMonomorphisms _ := inferInstance
  idIso j := eqToIso (congrArg (fun a => D.right a) (K.map_id j)) ≪≫ D.idIso (K.obj j)
  compIso a b := eqToIso (congrArg (fun c => D.right c) (K.map_comp a b)) ≪≫
    D.compIso (K.map a) (K.map b)

private theorem transport_id_comp (hD : D.Coherent) {i j : I}
    (e : i ⟶ i) (a d : i ⟶ j) (he : e = 𝟙 i) (hd : d = e ≫ a)
    (ha : d = a) (X : A j) :
    eqToHom (congrArg (fun f => (D.right f).obj X) hd) ≫
      (D.compIso e a).hom.app X ≫
        eqToHom (congrArg (fun f => (D.right f).obj ((D.right a).obj X)) he) ≫
          (D.idIso i).hom.app ((D.right a).obj X) =
      eqToHom (congrArg (fun f => (D.right f).obj X) ha) := by
  cases he
  cases hd
  simpa using hD.id_comp a X

private theorem transport_comp_id (hD : D.Coherent) {i j : I}
    (e : j ⟶ j) (a d : i ⟶ j) (he : e = 𝟙 j) (hd : d = a ≫ e)
    (ha : d = a) (X : A j) :
    eqToHom (congrArg (fun f => (D.right f).obj X) hd) ≫
      (D.compIso a e).hom.app X ≫
        (D.right a).map (eqToHom (congrArg (fun f => (D.right f).obj X) he)) ≫
          (D.right a).map ((D.idIso j).hom.app X) =
      eqToHom (congrArg (fun f => (D.right f).obj X) ha) := by
  cases he
  cases hd
  simpa using hD.comp_id a X

private theorem transport_assoc (hD : D.Coherent) {i j k l : I}
    (a : i ⟶ j) (b : j ⟶ k) (c : k ⟶ l)
    (p : i ⟶ k) (q : j ⟶ l) (r s : i ⟶ l)
    (hp : p = a ≫ b) (hq : q = b ≫ c) (hr : r = p ≫ c) (hs : s = a ≫ q)
    (hrs : r = s) (X : A l) :
    eqToHom (congrArg (fun f => (D.right f).obj X) hr) ≫
      (D.compIso p c).hom.app X ≫
        eqToHom (congrArg (fun f => (D.right f).obj ((D.right c).obj X)) hp) ≫
          (D.compIso a b).hom.app ((D.right c).obj X) =
    eqToHom (congrArg (fun f => (D.right f).obj X) hrs) ≫
      eqToHom (congrArg (fun f => (D.right f).obj X) hs) ≫
        (D.compIso a q).hom.app X ≫
          (D.right a).map (eqToHom (congrArg (fun f => (D.right f).obj X) hq)) ≫
            (D.right a).map ((D.compIso b c).hom.app X) := by
  cases hp
  cases hq
  cases hr
  cases hs
  simpa using hD.assoc a b c X

/-- Reindexing preserves the original comparison coherence. The replacement's
coherence is subsequently supplied by the already proved generic producer. -/
theorem AdjunctionData.Coherent.reindex (hD : D.Coherent) : (D.reindex K).Coherent where
  id_comp := by
    intro i j a X
    simpa only [AdjunctionData.reindex, Iso.trans_hom, NatTrans.comp_app,
      eqToIso.hom, eqToHom_app, Category.assoc] using
      transport_id_comp D hD (K.map (𝟙 i)) (K.map a) (K.map (𝟙 i ≫ a))
        (K.map_id i) (K.map_comp (𝟙 i) a) (congrArg K.map (Category.id_comp a)) X
  comp_id := by
    intro i j a X
    simpa only [AdjunctionData.reindex, Iso.trans_hom, NatTrans.comp_app,
      eqToIso.hom, eqToHom_app, Functor.map_comp, Category.assoc] using
      transport_comp_id D hD (K.map (𝟙 j)) (K.map a) (K.map (a ≫ 𝟙 j))
        (K.map_id j) (K.map_comp a (𝟙 j)) (congrArg K.map (Category.comp_id a)) X
  assoc := by
    intro i j k l a b c X
    simpa only [AdjunctionData.reindex, Iso.trans_hom, NatTrans.comp_app,
      eqToIso.hom, eqToHom_app, Functor.map_comp, Category.assoc] using
      transport_assoc D hD (K.map a) (K.map b) (K.map c)
        (K.map (a ≫ b)) (K.map (b ≫ c)) (K.map ((a ≫ b) ≫ c)) (K.map (a ≫ (b ≫ c)))
        (K.map_comp a b) (K.map_comp b c) (K.map_comp (a ≫ b) c)
        (K.map_comp a (b ≫ c)) (congrArg K.map (Category.assoc a b c)) X

end CategoryTheory.InjectiveSystem
