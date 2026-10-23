/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Basic
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.Opposite

/-! # Exactness of original Hom cochains of a termwise projective chain complex -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] (K : ChainComplex C ℕ)

/-- Functoriality in coefficients of the original additive Hom cochain complex. -/
def additiveHomFunctor : C ⥤ CochainComplex AddCommGrpCat.{v} ℕ where
  obj F := ((preadditiveYoneda.obj F).mapHomologicalComplex (.up ℕ)).obj K.op
  map g := ((preadditiveYoneda.map g).mapHomologicalComplex (.up ℕ)).app K.op
  map_id F := by ext n x; simp
  map_comp f g := by ext n x; simp

instance additiveHomFunctor_additive : (additiveHomFunctor K).Additive where
  map_add := by
    intro X Y f g
    ext n x
    change K.X n ⟶ X at x
    change x ≫ (f + g) = x ≫ f + x ≫ g
    simp only [Preadditive.comp_add]

/-- Termwise projectivity gives an actual short exact sequence of native Hom
cochain complexes for every short exact sequence of coefficients. -/
theorem additiveHomFunctor_shortExact [∀ n, Projective (K.X n)]
    (S : ShortComplex C) (hS : S.ShortExact) :
    (S.map (additiveHomFunctor K)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact (hS.map_of_exact (preadditiveCoyonedaObj (K.X n))).map_of_exact
    (forget₂ (ModuleCat (End (K.X n))ᵐᵒᵖ) AddCommGrpCat)

/-- Positive Hom-cochain acyclicity passes to the quotient of a short exact
sequence when the kernel and middle term are acyclic. -/
theorem additiveHomFunctor_quotient_exactAt [∀ n, Projective (K.X n)]
    (S : ShortComplex C) (hS : S.ShortExact) (n : ℕ)
    (h₁ : ((additiveHomFunctor K).obj S.X₁).ExactAt (n + 2))
    (h₂ : ((additiveHomFunctor K).obj S.X₂).ExactAt (n + 1)) :
    ((additiveHomFunctor K).obj S.X₃).ExactAt (n + 1) := by
  have hT := additiveHomFunctor_shortExact K S hS
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hT.homology_exact₃ (n + 1) (n + 2) rfl).isZero_X₂
    (h₂.isZero_homology.eq_of_src _ _) (h₁.isZero_homology.eq_of_tgt _ _)

end CategoryTheory.Sheaf.ModuleCoefficients
