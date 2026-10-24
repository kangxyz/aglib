/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.SmallAcyclic.CardinalLadder
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Compatible adjacent pairs for the downward acyclic construction

An adjacent pair consists of two monic maps into consecutive terms of an
actual natural-number chain complex, with its restricted differential.
The successor keeps the old left term literally as its right term. This
compatibility permits a single chain complex to be assembled by recursion;
no unrelated choices of terms or homotopies are used.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.IsGrothendieckAbelian

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Two consecutive subobjects with the actual restricted differential.
The cardinal bound is on the left term, which is the input to the next step. -/
structure SmallAcyclicPair (K : ChainComplex C ℕ) (κ : Cardinal.{w}) (n : ℕ) where
  /-- The chosen subobject in degree n. -/
  X₀ : C
  /-- The chosen subobject in degree n + 1. -/
  X₁ : C
  /-- The restricted ambient differential. -/
  d : X₁ ⟶ X₀
  /-- The original embedding into the degree-n term. -/
  f₀ : X₀ ⟶ K.X n
  /-- The original embedding into the degree-(n + 1) term. -/
  f₁ : X₁ ⟶ K.X (n + 1)
  mono_f₀ : Mono f₀
  mono_f₁ : Mono f₁
  comm : d ≫ f₀ = f₁ ≫ K.d (n + 1) n
  size : HasCardinalLT (Subobject X₁) κ

namespace SmallAcyclicPair

attribute [instance] mono_f₀ mono_f₁

variable [IsGrothendieckAbelian.{w} C] {G : C} (hG : IsSeparator G)
  {K : ChainComplex C ℕ} {κ : Cardinal.{w}} {n : ℕ}
  (s : SmallAcyclicPair K κ n)

/-- The new left term, with the maps and exactness supplied by the proved
cardinal-controlled kernel-covering construction. -/
structure SuccessorData where
  /-- The next chosen subobject, in degree n + 2. -/
  X : C
  /-- The original embedding of the next subobject. -/
  i : X ⟶ K.X (n + 2)
  /-- The epimorphism onto the preceding restricted kernel. -/
  e : X ⟶ kernel s.d
  mono_i : Mono i
  epi_e : Epi e
  comm : i ≫ K.d (n + 2) (n + 1) = e ≫ kernel.ι s.d ≫ s.f₁
  size : HasCardinalLT (Subobject X) (exactStepCardinal hG κ)
  exact : (ShortComplex.mk (e ≫ kernel.ι s.d) s.d (by simp)).Exact

/-- Existence of the compatible next term follows from ambient exactness. -/
lemma nonempty_successorData (hK : K.ExactAt (n + 1)) :
    Nonempty (SuccessorData hG s) := by
  have hS : (K.sc' (n + 2) (n + 1) n).Exact :=
    (K.exactAt_iff' (n + 2) (n + 1) n (by simp) (by simp)).1 hK
  obtain ⟨X, i, e, hi, he, hc, hs, hx⟩ :=
    @exists_exact_step C _ _ _ G hG κ (K.sc' (n + 2) (n + 1) n) hS
      s.X₁ s.X₀ s.f₁ s.mono_f₁ s.f₀ s.d s.comm s.size
  exact ⟨⟨X, i, e, hi, he, hc, hs, hx⟩⟩

/-- A choice of the proved next-term construction. -/
def successorData (hK : K.ExactAt (n + 1)) : SuccessorData hG s :=
  Classical.choice (nonempty_successorData hG s hK)

/-- The next adjacent pair retains the old left term as its right term. -/
def next (hK : K.ExactAt (n + 1)) :
    SmallAcyclicPair K (exactStepCardinal hG κ) (n + 1) where
  X₀ := s.X₁
  X₁ := (successorData hG s hK).X
  d := (successorData hG s hK).e ≫ kernel.ι s.d
  f₀ := s.f₁
  f₁ := (successorData hG s hK).i
  mono_f₀ := s.mono_f₁
  mono_f₁ := (successorData hG s hK).mono_i
  comm := by simpa only [Category.assoc] using (successorData hG s hK).comm.symm
  size := (successorData hG s hK).size

@[simp]
lemma next_X₀ (hK : K.ExactAt (n + 1)) : (next hG s hK).X₀ = s.X₁ := rfl

@[simp]
lemma next_d_comp (hK : K.ExactAt (n + 1)) : (next hG s hK).d ≫ s.d = 0 := by
  change ((successorData hG s hK).e ≫ kernel.ι s.d) ≫ s.d = 0
  rw [Category.assoc, kernel.condition, comp_zero]

lemma next_exact (hK : K.ExactAt (n + 1)) :
    (ShortComplex.mk (next hG s hK).d s.d (next_d_comp hG s hK)).Exact :=
  (successorData hG s hK).exact

end SmallAcyclicPair

end ChainComplex
