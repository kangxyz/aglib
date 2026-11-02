/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.CategoryTheory.Whiskering
public import Aglib.CategoryTheory.NatTrans.TargetComparisonEquation

/-! # Preserve the original canonical map through specified normalization isomorphisms -/
@[expose] public noncomputable section
namespace CategoryTheory
variable {C : Type*} [Category* C] {X Y Z : C}

/-- The specified normalization isomorphism has the original canonical map as its hom. -/
def CanonicalMapNormalizationEquation (b : X ⟶ Y) (e : X ≅ Y) : Prop := b = e.hom

/-- A proved chosen comparison transfers the normalization of the same canonical map. -/
theorem canonicalMapNormalization_comparison (b : X ⟶ Z) (c : Y ⟶ Z)
    (a : X ≅ Y) (e : Y ≅ Z)
    (h : TargetComparisonEquation a.hom c b)
    (hc : CanonicalMapNormalizationEquation c e) :
    CanonicalMapNormalizationEquation b (a ≪≫ e) := by
  change b = a.hom ≫ e.hom
  exact h.symm.trans (congrArg (fun z => a.hom ≫ z) hc)

variable {V U A B : Type*} [Category* V] [Category* U] [Category* A] [Category* B]
  {F F' : U ⥤ A} {G : A ⥤ B} {H : U ⥤ B}

/-- Compare whole original maps before restricting the input functor. -/
theorem canonicalMapNormalization_whisker (i : V ⥤ U)
    (b : F ⟶ F') (e : F ≅ F') (d : F' ⋙ G ≅ H) (n : F ⋙ G ≅ H)
    (hb : b = e.hom) (hn : Functor.isoWhiskerRight e G ≪≫ d = n) :
    CanonicalMapNormalizationEquation
      (Functor.whiskerLeft i (Functor.whiskerRight b G ≫ d.hom))
      (Functor.isoWhiskerLeft i n) := by
  subst b
  subst n
  rfl

/-- Substitute the proved original structural-iso equation before concrete specialization. -/
theorem canonicalMapNormalization_whisker_of_iso_eq (i : V ⥤ U)
    (b : F ⟶ F') (e : F ≅ F') (d₀ d₁ : F' ⋙ G ≅ H) (n : F ⋙ G ≅ H)
    (hb : b = e.hom) (hd : d₀ = d₁)
    (hn : Functor.isoWhiskerRight e G ≪≫ d₀ = n) :
    CanonicalMapNormalizationEquation
      (Functor.whiskerLeft i (Functor.whiskerRight b G ≫ d₁.hom))
      (Functor.isoWhiskerLeft i n) := by
  subst d₁
  exact canonicalMapNormalization_whisker i b e d₀ n hb hn
end CategoryTheory
