/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.SmallAcyclic.EpiLifting
public import Mathlib.CategoryTheory.Limits.MonoCoprod

/-!
# A uniform cardinal bound for lifting subobjects

For a fixed separator and a cardinal bound on the number of subobjects of a
quotient, one regular cardinal bounds the size of a covering subobject of
every source. This is the cardinal-uniform form of the lifting step in
Stacks 079J. The bound and all indexing types live in the Grothendieck universe.
-/

@[expose] public noncomputable section

universe w v u

namespace CategoryTheory.IsGrothendieckAbelian

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {G : C} (hG : IsSeparator G)

include hG

/-- Every bound on the number of subobjects of the quotient gives a uniform
regular bound on a subobject of the source that still covers the quotient.
Neither the bound nor the coproduct used to obtain it depends on the source. -/
lemma exists_regular_cardinal_lifting_bound (κ : Cardinal.{w}) :
    ∃ μ : Cardinal.{w}, μ.IsRegular ∧
      ∀ {M N : C} (p : M ⟶ N) [Epi p],
        Cardinal.mk (Shrink.{w} (Subobject N)) ≤ κ →
        ∃ A : Subobject M, Epi (A.arrow ≫ p) ∧ HasCardinalLT (Subobject (A : C)) μ := by
  obtain ⟨μ, hμ, hbound⟩ := HasCardinalLT.exists_regular_cardinal.{w}
    (Subobject (∐ fun _ : κ.out ↦ G))
  refine ⟨μ, hμ, ?_⟩
  intro M N p hp hN
  have hN' : Cardinal.mk (Shrink.{w} (Subobject N)) ≤ Cardinal.mk κ.out := by
    simpa using hN
  obtain ⟨i⟩ := (Cardinal.le_def _ _).1 hN'
  let a : (∐ fun _ : Shrink.{w} (Subobject N) ↦ G) ⟶ (∐ fun _ : κ.out ↦ G) :=
    Sigma.desc (fun j ↦ Sigma.ι (fun _ : κ.out ↦ G) (i j))
  have : Mono a := MonoCoprod.mono_of_injective' (fun _ : κ.out ↦ G) i i.injective
  exact exists_subobject_epi_of_subobject_coproduct_bound hG p
    (Subobject.hasCardinalLT_of_mono hbound a)

end CategoryTheory.IsGrothendieckAbelian
