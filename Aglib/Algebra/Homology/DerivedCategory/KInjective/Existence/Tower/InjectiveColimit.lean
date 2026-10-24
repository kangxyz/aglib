/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Actual injective colimits from successor injective factorizations

Maps from subobjects of a separator factor through a stage by the native
regular-cardinal factorization theorem. The stage's specified injective
factorization then gives an extension. The native generator criterion proves
injectivity; no exactness of arbitrary limits or replacement axiom is used.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {G : C} (hG : IsSeparator G)
  {J : Type w} [SmallCategory J]
  (F : J ⥤ C) [∀ (i j : J) (f : i ⟶ j), Mono (F.map f)]
  {c : Cocone F} (hc : IsColimit c)
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [IsCardinalFiltered J κ]

include hG hc in
/-- A genuine regular filtered colimit is injective when each original cocone
leg factors through an actual injective object. -/
lemma injective_of_colimit_injective_factors
    (hsize : HasCardinalLT (Subobject G) κ)
    (hfactor : ∀ j, ∃ (E : C) (_ : Injective E) (a : F.obj j ⟶ E)
      (b : E ⟶ c.pt), c.ι.app j = a ≫ b) : Injective c.pt := by
  rw [injective_iff_rlp_monomorphisms_zero, ← generatingMonomorphisms_rlp hG]
  intro X Y f hf
  obtain ⟨S⟩ := hf
  refine { sq_hasLift := ?_ }
  intro z q sq
  obtain ⟨j, y, hy⟩ := IsPresentable.surjectivity hc
    (Subobject.hasCardinalLT_of_mono hsize S.arrow) z
  obtain ⟨E, hE, a, b, hab⟩ := hfactor j
  have : Injective E := hE
  refine ⟨⟨{ l := Injective.factorThru (y ≫ a) S.arrow ≫ b
             fac_left := ?_
             fac_right := ?_ }⟩⟩
  · rw [← Category.assoc, Injective.comp_factorThru, Category.assoc, ← hab, ← hy]
  · exact (isZero_zero C).eq_of_tgt _ _

end CategoryTheory.IsGrothendieckAbelian
