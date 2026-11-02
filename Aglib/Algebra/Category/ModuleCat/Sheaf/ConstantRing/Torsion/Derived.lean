/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Torsion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Plus

/-! # The original internal-torsion homology range

The full and bounded-below ranges use the supplied derived realization and
its actual homology. No common annihilator is part of the range predicate.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ModuleCat.Sheaf.ConstantRing

universe u v r w d

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type r) [Ring Λ] [HasWeakSheafify J RingCat.{r}]
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (ModuleSheaf.{u, v, r, w} J Λ)]

/-- Internal torsion of the actual homology module sheaves. -/
def moduleTorsionCohomology : ObjectProperty (DerivedCategory (ModuleSheaf.{u, v, r, w} J Λ)) :=
  fun K => ∀ n : ℤ, moduleIsTorsion J Λ
    ((DerivedCategory.homologyFunctor (ModuleSheaf.{u, v, r, w} J Λ) n).obj K)

/-- The original Plus subcategory uses these same homology objects. -/
def moduleTorsionCohomologyPlus :
    ObjectProperty (DerivedCategory.Plus (ModuleSheaf.{u, v, r, w} J Λ)) :=
  fun K => moduleTorsionCohomology J Λ K.obj

/-- Actual derived isomorphisms retain the same internal-torsion range. -/
theorem moduleTorsionCohomology_of_iso
    {K L : DerivedCategory (ModuleSheaf.{u, v, r, w} J Λ)} (e : K ≅ L)
    (hL : moduleTorsionCohomology J Λ L) : moduleTorsionCohomology J Λ K := by
  intro n
  exact moduleIsTorsion_of_iso J Λ
    ((DerivedCategory.homologyFunctor (ModuleSheaf.{u, v, r, w} J Λ) n).mapIso e) (hL n)

variable [J.WEqualsLocallyBijective RingCat.{r}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- A positive scalar-unit annihilator is sufficient for every original
derived object to lie in this same range. -/
theorem moduleTorsionCohomology_of_nsmul_one_eq_zero
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)
    (K : DerivedCategory (ModuleSheaf.{u, v, r, w} J Λ)) :
    moduleTorsionCohomology J Λ K := by
  intro n
  exact moduleIsTorsion_of_nsmul_one_eq_zero J Λ N hN hΛ
    ((DerivedCategory.homologyFunctor (ModuleSheaf.{u, v, r, w} J Λ) n).obj K)

end ModuleCat.Sheaf.ConstantRing
