/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Group.Equiv.ComparisonComposite
public import Mathlib.Algebra.Category.Grp.Basic

/-! # Natural isomorphisms from complete original component comparisons

The intermediate groups and maps are supplied families, not new diagram models.
The complete component square and categorical evaluation are assembled here.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

universe v u r b c d

variable {I : Type u} [Category.{v} I]
  (P Q : I ⥤ AddCommGrpCat.{r})
  {B : I → Type b} {C : I → Type c} {D : I → Type d}
  [∀ i, AddCommGroup (B i)] [∀ i, AddCommGroup (C i)] [∀ i, AddCommGroup (D i)]
  (l : ∀ i, P.obj i ≃+ B i) (e : ∀ i, B i ≃+ C i)
  (t : ∀ i, D i ≃+ C i) (s : ∀ i, D i ≃+ Q.obj i)
  (bmap : ∀ {i j}, (i ⟶ j) → (B i →+ B j))
  (cmap : ∀ {i j}, (i ⟶ j) → (C i →+ C j))
  (dmap : ∀ {i j}, (i ⟶ j) → (D i →+ D j))
  (hl : ∀ {i j} (a : i ⟶ j) x, l j (P.map a x) = bmap a (l i x))
  (he : ∀ {i j} (a : i ⟶ j) x, e j (bmap a x) = cmap a (e i x))
  (ht : ∀ {i j} (a : i ⟶ j) x, t j (dmap a x) = cmap a (t i x))
  (hs : ∀ {i j} (a : i ⟶ j) x, s j (dmap a x) = Q.map a (s i x))

/-- Assemble the supplied original component construction and its four map laws. -/
def comparisonCompositeNatIso : P ≅ Q :=
  NatIso.ofComponents
    (fun i => (AddEquiv.comparisonComposite (l i) (e i) (t i) (s i)).toAddCommGrpIso)
    (by
      intro i j a
      apply ConcreteCategory.hom_ext
      intro x
      exact AddEquiv.comparisonComposite_map
        (l i) (e i) (t i) (s i) (l j) (e j) (t j) (s j)
        (P.map a).hom (bmap a) (cmap a) (dmap a) (Q.map a).hom
        (hl a) (he a) (ht a) (hs a) x)

/-- The forward component is exactly the original supplied composite. -/
theorem comparisonCompositeNatIso_hom_app (i : I) :
    (comparisonCompositeNatIso P Q l e t s bmap cmap dmap hl he ht hs).hom.app i =
      AddCommGrpCat.ofHom
        (AddEquiv.comparisonComposite (l i) (e i) (t i) (s i)).toAddMonoidHom := rfl

end CategoryTheory
