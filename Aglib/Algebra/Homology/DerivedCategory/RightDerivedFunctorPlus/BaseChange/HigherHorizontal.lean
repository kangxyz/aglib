/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HigherVertical

/-! # Transport of explicit horizontal and identity equations

These category-level lemmas transport supplied literal equations through a
functor and specified endpoint isomorphisms. Their edge compatibility premises
must be discharged by the original comparison maps in each application.
-/

@[expose] public section
open CategoryTheory
namespace CategoryTheory

variable {D E : Type*} [Category* D] [Category* E]

/-- A literal three-edge versus two-edge derived pasting equation transports
through homology once each edge uses its specified native endpoint comparison. -/
theorem mapped_horizontal_transport (H : D ⥤ E)
    {A B C D₀ T : D} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D₀)
    (d : A ⟶ T) (e : T ⟶ D₀) (h : a ≫ b ≫ c = d ≫ e)
    {A' B' C' D' T' : E}
    (iA : A' ≅ H.obj A) (iB : B' ≅ H.obj B) (iC : C' ≅ H.obj C)
    (iD : D' ≅ H.obj D₀) (iT : T' ≅ H.obj T)
    (a' : A' ⟶ B') (b' : B' ⟶ C') (c' : C' ⟶ D')
    (d' : A' ⟶ T') (e' : T' ⟶ D')
    (ha : a' ≫ iB.hom = iA.hom ≫ H.map a)
    (hb : b' ≫ iC.hom = iB.hom ≫ H.map b)
    (hc : c' ≫ iD.hom = iC.hom ≫ H.map c)
    (hd : d' ≫ iT.hom = iA.hom ≫ H.map d)
    (he : e' ≫ iD.hom = iT.hom ≫ H.map e) :
    a' ≫ b' ≫ c' = d' ≫ e' := by
  apply (cancel_mono iD.hom).mp
  simp only [Category.assoc]
  rw [hc, ← Category.assoc b', hb, Category.assoc,
    ← Category.assoc a', ha, Category.assoc,
    he, ← Category.assoc d', hd, Category.assoc]
  rw [← H.map_comp, ← H.map_comp, h, H.map_comp]

/-- Identity normalization transports without asserting that any nonexact
right-derived unit is invertible. -/
theorem mapped_identity_transport (H : D ⥤ E)
    {A B C : D} (b : A ⟶ B) (u : A ⟶ C) (v : B ⟶ C)
    (h : u = b ≫ v) {A' B' C' : E}
    (iA : A' ≅ H.obj A) (iB : B' ≅ H.obj B) (iC : C' ≅ H.obj C)
    (b' : A' ⟶ B') (u' : A' ⟶ C') (v' : B' ⟶ C')
    (hb : b' ≫ iB.hom = iA.hom ≫ H.map b)
    (hu : u' ≫ iC.hom = iA.hom ≫ H.map u)
    (hv : v' ≫ iC.hom = iB.hom ≫ H.map v) :
    u' = b' ≫ v' := by
  apply (cancel_mono iC.hom).mp
  rw [hu, Category.assoc, hv, ← Category.assoc, hb, Category.assoc,
    ← H.map_comp, ← h]

end CategoryTheory
