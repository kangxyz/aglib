/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.UnderlyingMate

/-!
# Original adjunct values through an actual underlying mate

The actual mate determines the underlying hom-equivalence value through its unit
and naturality. Full faithful underlying comparison then gives the same original
preimage value. All four categories and their Hom worlds remain independent.
-/

@[expose] public section

namespace CategoryTheory

universe uA vA uB vB uC vC uD vD

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {U : A ⥤ C} {V : B ⥤ D}

/-- The actual mate/unit and original naturality give the whole underlying adjunct value. -/
theorem underlying_homEquiv_of_mate (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (s : TwoSquare U L₁ L₂ V) (d : R₁ ⋙ U ⟶ V ⋙ R₂)
    (hmate : (mateEquiv adj₁ adj₂ s).natTrans = d)
    (M : A) (N : B) (j : L₁.obj M ⟶ N) :
    U.map (adj₁.homEquiv M N j) ≫ d.app N =
      adj₂.homEquiv (U.obj M) (V.obj N) (s.app M ≫ V.map j) := by
  have hm : (mateEquiv adj₁ adj₂ s).app (L₁.obj M) = d.app (L₁.obj M) :=
    NatTrans.congr_app hmate (L₁.obj M)
  have hu : U.map (adj₁.unit.app M) ≫ d.app (L₁.obj M) =
      adj₂.unit.app (U.obj M) ≫ R₂.map (s.app M) :=
    (congrArg (fun t => U.map (adj₁.unit.app M) ≫ t) hm).symm.trans
      (unit_mateEquiv adj₁ adj₂ s M)
  have hn : U.map (R₁.map j) ≫ d.app N =
      d.app (L₁.obj M) ≫ R₂.map (V.map j) := d.naturality j
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    Functor.map_comp, Category.assoc, hn, ← Category.assoc, hu, Category.assoc]

/-- Full faithful U recovers the SAME adjunct through the original actual comparison preimage.
No fullness of another scalar functor or forgotten-injective assertion is used. -/
theorem homEquiv_eq_preimage_of_underlying_mate
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (s : TwoSquare U L₁ L₂ V)
    (d : R₁ ⋙ U ≅ V ⋙ R₂) (hmate : (mateEquiv adj₁ adj₂ s).natTrans = d.hom)
    [U.Full] [U.Faithful] (M : A) (N : B) (j : L₁.obj M ⟶ N) :
    adj₁.homEquiv M N j = U.preimage
      (adj₂.homEquiv (U.obj M) (V.obj N) (s.app M ≫ V.map j) ≫ d.inv.app N) := by
  apply U.map_injective
  rw [Functor.map_preimage]
  exact (d.app N).eq_comp_inv.mpr (underlying_homEquiv_of_mate adj₁ adj₂ s d.hom hmate M N j)

end CategoryTheory
