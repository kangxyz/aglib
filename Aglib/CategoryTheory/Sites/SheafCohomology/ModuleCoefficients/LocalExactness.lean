/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.LiftCorrection
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.CechExactProducts
public import Mathlib.CategoryTheory.Sites.Over

/-!
# All-slice Čech acyclicity and exact quotients

The predicate uses the native Čech complex in every slice category. In
particular its finite products are fiber products over the chosen base object.
Exactness on the presheaf category is sectionwise exactness, not merely sheaf
exactness. The local lifting argument is what must supply that distinction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

universe w v u v' u'

variable {C : Type u} [Category.{v} C]
  [∀ W : C, HasFiniteProducts (Over W)]
  {A : Type u'} [Category.{v'} A] [Abelian A] [HasProducts.{w} A]

/-- Positive exactness of native Čech cochains for every family over every
object, evaluated on the original presheaf restricted to that slice. -/
def CechAcyclic (F : Cᵒᵖ ⥤ A) : Prop :=
  ∀ (W : C) (ι : Type w) (U : ι → Over W) (n : ℕ),
    ((cechComplexFunctor U).obj ((Over.forget W).op ⋙ F)).ExactAt (n + 1)

/-- The sheaf predicate retains the native presheaf and native slice restriction. -/
abbrev SheafCechAcyclic {J : GrothendieckTopology C} (F : Sheaf J A) : Prop :=
  CechAcyclic.{w} F.obj

/-- In a sectionwise short exact sequence, positive Čech acyclicity passes to
the quotient when both the kernel and middle term are Čech-acyclic. -/
theorem CechAcyclic.quotient
    [∀ (ι : Type w), HasExactLimitsOfShape (Discrete ι) A]
    (S : ShortComplex (Cᵒᵖ ⥤ A)) (hS : S.ShortExact)
    (h₁ : CechAcyclic.{w} S.X₁) (h₂ : CechAcyclic.{w} S.X₂) :
    CechAcyclic.{w} S.X₃ := by
  intro W ι U n
  let R := (Functor.whiskeringLeft _ _ A).obj (Over.forget W).op
  let T := (S.map R).map (cechComplexFunctor U)
  have hT : T.ShortExact :=
    cech_shortExact_of_exact_products U (S.map R) (hS.map_of_exact R)
  have hleft : IsZero (T.X₂.homology (n + 1)) := (h₂ W ι U n).isZero_homology
  have hright : IsZero (T.X₁.homology ((n + 1) + 1)) :=
    (h₁ W ι U (n + 1)).isZero_homology
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hT.homology_exact₃ (n + 1) ((n + 1) + 1) rfl).isZero_X₂
    (hleft.eq_of_src _ _) (hright.eq_of_tgt _ _)

end CategoryTheory.Sheaf.ModuleCoefficients
