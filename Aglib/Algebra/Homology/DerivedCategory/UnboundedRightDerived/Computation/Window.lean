/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Computation.Cycles

/-! # A finite exactness window for unbounded derived computation

For a complex of acyclic coefficients, exactness in degrees `[q - N, q]`
implies exactness in degree `q` after applying a left exact functor with
uniform vanishing in degree `N + 1`. No vanishing in degree `q + 1` is needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe s u v w u' v' w'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [IsGrothendieckAbelian.{s} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive]
  (K : CochainComplex C ℤ)

/-- Local dimension shifting only uses the specified finite interval of exactness. -/
theorem isZero_rightDerived_cycles_of_window (k n : ℕ)
    (hbound : ∀ M : C, IsZero ((F.rightDerived (n + k + 1)).obj M)) (i : ℤ)
    (hterms : ∀ j : ℤ, ∀ m : ℕ, IsZero ((F.rightDerived (m + 1)).obj (K.X j)))
    (hexact : ∀ j : ℤ, i - (k : ℤ) < j → j ≤ i → K.ExactAt j) :
    IsZero ((F.rightDerived (n + 1)).obj (K.cycles i)) := by
  induction k generalizing n i with
  | zero => exact hbound _
  | succ k ih =>
    have hz : IsZero ((F.rightDerived (n + 1 + 1)).obj (K.cycles (i - 1))) :=
      ih (n + 1) (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hbound) (i - 1) (by
          intro j hj₁ hj₂
          exact hexact j (by omega) (by omega))
    have h := F.isZero_rightDerived_X₃_of_shortExact
      (K.cycleSequence_shortExact (i - 1) (by
        apply hexact <;> omega)) (n + 1) (hterms (i - 1) n) hz
    simpa only [CochainComplex.cycleSequence, sub_add_cancel] using h

variable [PreservesFiniteLimits F]

omit [HasDerivedCategory.{w} C] [IsGrothendieckAbelian.{s} C]
  [HasDerivedCategory.{w'} D] in
/-- Epimorphy onto the original cycles, together with preservation of the next
kernel, proves exactness of the original mapped differential pair. -/
theorem exactAt_map_of_shortExact_cycleSequence (q : ℤ)
    (h : ((K.cycleSequence (q - 1)).map F).ShortExact) :
    ((F.mapHomologicalComplex (.up ℤ)).obj K).ExactAt q := by
  let S : ShortComplex C := ShortComplex.mk (K.iCycles q) (K.d q (q + 1))
    (K.iCycles_d q (q + 1))
  have hS : S.Exact := S.exact_of_f_is_kernel (K.cyclesIsKernel q (q + 1) (by simp))
  have hSF : (S.map F).Exact := hS.map_of_mono_of_preservesKernel F
    (inferInstanceAs (Mono (K.iCycles q))) inferInstance
  let L := (F.mapHomologicalComplex (.up ℤ)).obj K
  let φ : L.sc' (q - 1) q (q + 1) ⟶ S.map F := {
    τ₁ := F.map (K.toCycles (q - 1) q)
    τ₂ := 𝟙 _
    τ₃ := 𝟙 _
    comm₁₂ := by
      change F.map (K.toCycles (q - 1) q) ≫ F.map (K.iCycles q) =
        F.map (K.d (q - 1) q) ≫ 𝟙 _
      rw [← F.map_comp, K.toCycles_i, Category.comp_id]
    comm₂₃ := by
      change 𝟙 _ ≫ F.map (K.d q (q + 1)) = F.map (K.d q (q + 1)) ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id] }
  have : Epi φ.τ₁ := by
    have he : Epi (F.map (K.toCycles (q - 1) (q - 1 + 1))) := h.epi_g
    have eq : q - 1 + 1 = q := by omega
    rw [eq] at he
    exact he
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 _))
  have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 _))
  exact (L.exactAt_iff' (q - 1) q (q + 1) (by simp) (by simp)).mpr
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hSF)

/-- The exactness window is closed at both endpoints, and includes the exact
`N = 0` case. The source complex has no global boundedness assumption. -/
theorem exactAt_map_of_acyclic_terms_of_window (N : ℕ)
    (hbound : ∀ M : C, IsZero ((F.rightDerived (N + 1)).obj M)) (q : ℤ)
    (hterms : ∀ j : ℤ, ∀ m : ℕ, IsZero ((F.rightDerived (m + 1)).obj (K.X j)))
    (hexact : ∀ j : ℤ, q - (N : ℤ) ≤ j → j ≤ q → K.ExactAt j) :
    ((F.mapHomologicalComplex (.up ℤ)).obj K).ExactAt q := by
  apply F.exactAt_map_of_shortExact_cycleSequence K q
  apply F.shortExact_map_of_isZero_rightDerived_one
    (K.cycleSequence_shortExact (q - 1) (by simpa using hexact q (by omega) le_rfl))
  exact F.isZero_rightDerived_cycles_of_window K N 0
    (by simpa only [Nat.zero_add] using hbound) (q - 1) hterms
    (fun j hj₁ hj₂ => hexact j (by omega) (by omega))

end CategoryTheory.Functor
