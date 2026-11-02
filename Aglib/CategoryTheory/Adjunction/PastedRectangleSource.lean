/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.PastedRectangleNormalization
public import Aglib.CategoryTheory.Adjunction.IdentitySourceMate

/-! # Contracting the original identity-source side of a pasted rectangle -/

@[expose] public section

namespace CategoryTheory

/-- Contract a proved original source factorization without expanding the
remaining normalized rectangle. -/
theorem pastedRectangle_contract_source {C : Type*} [Category C]
    {S A B D T T' : C} (u : S ⟶ A) (v : S ⟶ B) (a : A ⟶ T)
    (t : B ⟶ D) (r : D ⟶ T') (c : T' ⟶ T) (δ : S ⟶ D)
    (h : PastedRectangleEquation u v a (t ≫ r) c) (hδ : v ≫ t = δ) :
    PastedRectangleEquation u δ a r c := by
  unfold PastedRectangleEquation at h ⊢
  rw [← hδ]
  simpa only [Category.assoc] using h

/-- Use the whole actual identity-source mate equation to replace only the
normalized source segment by its original unit comparison. -/
theorem pastedRectangle_contract_identitySource
    {A B C : Type*} [Category A] [Category B] [Category C]
    {I R : A ⥤ A} {P : B ⥤ C} {Q : C ⥤ B} {G : A ⥤ B} {H : A ⥤ C}
    (aI : I ⊣ R) (aP : P ⊣ Q) (β : TwoSquare G I P H)
    (d : R ≅ 𝟭 A) (δ : G ⟶ H ⋙ Q)
    (hδ : IdentitySourceMateEquation aI aP β d δ) (K : A)
    {Z T T' : B} (u : G.obj K ⟶ Z) (a : Z ⟶ T)
    (r : Q.obj (H.obj K) ⟶ T') (c : T' ⟶ T)
    (h : PastedRectangleEquation u (G.map (d.inv.app K)) a
      ((mateEquiv aI aP β).app K ≫ r) c) :
    PastedRectangleEquation u (δ.app K) a r c :=
  pastedRectangle_contract_source u (G.map (d.inv.app K)) a
    ((mateEquiv aI aP β).app K) r c (δ.app K) h (hδ K)

end CategoryTheory
