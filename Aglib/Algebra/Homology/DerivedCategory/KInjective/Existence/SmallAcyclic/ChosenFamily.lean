/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.SmallAcyclic.Family

/-! # A fixed choice of the constructed small acyclic family -/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.IsGrothendieckAbelian

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {G : C} (hG : IsSeparator G)

/-- The small index chosen from the proved family existence theorem. -/
def smallAcyclicFamilyIndex : Type w := (exists_small_acyclic_family hG).choose

/-- A single fixed native family, shared by every filtration stage. -/
def smallAcyclicFamily : smallAcyclicFamilyIndex hG → CochainComplex C ℤ :=
  (exists_small_acyclic_family hG).choose_spec.choose

lemma smallAcyclicFamily_acyclic (i : smallAcyclicFamilyIndex hG) :
    (smallAcyclicFamily hG i).Acyclic :=
  (exists_small_acyclic_family hG).choose_spec.choose_spec.1 i

lemma smallAcyclicFamily_boundedAbove (i : smallAcyclicFamilyIndex hG) :
    ∃ n : ℤ, (smallAcyclicFamily hG i).IsStrictlyLE n :=
  (exists_small_acyclic_family hG).choose_spec.choose_spec.2.1 i

lemma smallAcyclicFamily_size (i : smallAcyclicFamilyIndex hG) (n : ℤ) :
    HasCardinalLT (Subobject ((smallAcyclicFamily hG i).X n)) (smallAcyclicCardinal hG) :=
  (exists_small_acyclic_family hG).choose_spec.choose_spec.2.2.1 i n

lemma smallAcyclicFamily_factorization (M : CochainComplex C ℤ) (hM : M.Acyclic)
    (n : ℤ) (ψ : G ⟶ M.X n) :
    ∃ (i : smallAcyclicFamilyIndex hG) (f : smallAcyclicFamily hG i ⟶ M)
      (a : G ⟶ (smallAcyclicFamily hG i).X n),
      (∀ m, Mono (f.f m)) ∧ a ≫ f.f n = ψ :=
  (exists_small_acyclic_family hG).choose_spec.choose_spec.2.2.2 M hM n ψ

end CochainComplex
