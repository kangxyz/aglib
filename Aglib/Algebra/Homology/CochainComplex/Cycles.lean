/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.KernelClosed
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Data.Int.Init
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Actual cycle sequences and acyclicity under additive functors

The maps use Mathlib cycles, their actual inclusions and the actual differential
lifts. Kernel closure propagates down from an upper bound in an acyclic complex.
An additive functor yields an acyclic image when these actual cycle sequences
map to short exact sequences; exactness on the ambient category is not required.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/Waldhausen/GilletWaldhausen/AcyclicCycles.lean`.
SHA-256: `009961771a2e9815f6b3ecfc940df6ea5c62a53399f94a7c4c8dca421bea0ba1`.
Selected source lines: 43–97.
`Quillen/Waldhausen/GilletWaldhausen/ExactFunctorCycles.lean`.
SHA-256: `7c88d4ec4c872ae7eb7eafa7b6ef5d159dc38b8fc2cb9f88475e0d0f29dc72a6`.
Selected source lines: 33–74.
Actual source objects, maps, hypotheses and independent universes are preserved.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u u' v'
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory.ExactCategory
namespace CochainComplex

section
variable {A : Type u} [Category.{v} A] [Abelian A]


/-- The genuine cycle inclusion followed by the next cycle projection vanishes. -/
@[reassoc (attr := simp)]
theorem iCycles_toCycles (K : CochainComplex A ℤ) (n : ℤ) :
    K.iCycles n ≫ K.toCycles n (n + 1) = 0 := by
  rw [← cancel_mono (K.iCycles (n + 1)), Category.assoc, K.toCycles_i,
    K.iCycles_d, zero_comp]

/-- The actual cycle/term/next-cycle sequence. -/
def cycleSequence (K : CochainComplex A ℤ) (n : ℤ) : ShortComplex A :=
  ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1)) (iCycles_toCycles K n)

/-- Exactness in the next degree makes the actual map onto its cycles epi. -/
theorem epi_toCycles_of_exactAt (K : CochainComplex A ℤ) (n : ℤ)
    (hK : K.ExactAt (n + 1)) : Epi (K.toCycles n (n + 1)) := by
  have hs := (K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp; omega)).1 hK
  let e := K.cyclesIsoSc' n (n + 1) (n + 2) (by simp) (by simp; omega)
  have : Epi (K.toCycles n (n + 1) ≫ e.hom) := by
    rw [K.toCycles_cyclesIsoSc'_hom]
    exact hs.epi_toCycles
  exact (epi_comp_iff_of_isIso (K.toCycles n (n + 1)) e.hom).1 inferInstance

/-- The cycle sequence is short exact whenever the next degree is exact. -/
theorem cycleSequence_shortExact (K : CochainComplex A ℤ) (n : ℤ)
    (hK : K.ExactAt (n + 1)) : (cycleSequence K n).ShortExact where
  mono_f := inferInstanceAs (Mono (K.iCycles n))
  epi_g := epi_toCycles_of_exactAt K n hK
  exact := (cycleSequence K n).exact_of_f_is_kernel
    (isKernelOfComp (K.iCycles (n + 1)) (K.d n (n + 1))
      (K.cyclesIsKernel n (n + 1) (by simp)) (iCycles_toCycles K n) (K.toCycles_i n (n + 1)))

attribute [local instance] Abelian.hasFiniteBiproducts

variable (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]
  (K : CochainComplex A ℤ) (hterms : ∀ n, P (K.X n))
  (hK : K.Acyclic) (b : ℤ) (hb : ∀ n, b < n → IsZero (K.X n))

include hterms hK hb in
/-- Downward induction from the strict upper bound puts every actual cycle
in the chosen kernel-closed subcategory. No lower bound is required. -/
theorem cycles_mem (n : ℤ) : P (K.cycles n) := by
  have top (i : ℤ) (hi : b ≤ i) : P (K.cycles i) :=
    P.prop_of_iso (K.iCyclesIso i (i + 1) (by simp)
      ((hb (i + 1) (by omega)).eq_of_tgt _ _)).symm (hterms i)
  by_cases hn : n ≤ b
  · induction n, hn using Int.leInductionDown with
    | base => exact top b le_rfl
    | pred n hn ih =>
        apply CategoryTheory.ExactCategory.ExactStructure.IsKernelClosed.prop_kernel (E :=
          abelianExactStructure A)
          (cycleSequence_shortExact K (n - 1) (hK _)) (hterms _)
        simpa only [cycleSequence, sub_add_cancel] using ih
  · exact top n (by omega)

end

section
variable {A : Type u} [Category.{v} A] [Abelian A]
  {B : Type u'} [Category.{v'} B] [Abelian B]

/-- Exactness of all actual mapped cycle sequences implies acyclicity of the
termwise image, without an ambient exactness assumption on the functor. -/
theorem acyclic_map_of_cycle_sequences (F : A ⥤ B) [F.Additive]
    (K : CochainComplex A ℤ)
    (h : ∀ n : ℤ, ((cycleSequence K n).map F).ShortExact) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic := by
  have he (n : ℤ) : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ExactAt (n + 1) := by
    let S : ShortComplex B := ShortComplex.mk
      (F.map (K.toCycles n (n + 1)) ≫ F.map (K.iCycles (n + 1)))
      (F.map (K.toCycles (n + 1) (n + 1 + 1))) (by
        rw [Category.assoc, ← F.map_comp, iCycles_toCycles, F.map_zero, comp_zero])
    let T := (cycleSequence K (n + 1)).map F
    let a : S ⟶ T :=
      { τ₁ := F.map (K.toCycles n (n + 1))
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by simp [S, T, cycleSequence]
        comm₂₃ := by simp [S, T, cycleSequence] }
    have : Epi a.τ₁ := (h n).epi_g
    have : IsIso a.τ₂ := inferInstanceAs (IsIso (𝟙 _))
    have : Mono a.τ₃ := inferInstanceAs (Mono (𝟙 _))
    have hs : S.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono a).mpr (h (n + 1)).exact
    let C := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    let b : S ⟶ C.sc' n (n + 1) (n + 1 + 1) :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := F.map (K.iCycles (n + 1 + 1))
        comm₁₂ := by
          change 𝟙 _ ≫ F.map (K.d n (n + 1)) =
            (F.map (K.toCycles n (n + 1)) ≫ F.map (K.iCycles (n + 1))) ≫ 𝟙 _
          rw [Category.id_comp, Category.comp_id, ← F.map_comp, K.toCycles_i]
        comm₂₃ := by
          change 𝟙 _ ≫ F.map (K.d (n + 1) (n + 1 + 1)) =
            F.map (K.toCycles (n + 1) (n + 1 + 1)) ≫ F.map (K.iCycles (n + 1 + 1))
          rw [Category.id_comp, ← F.map_comp, K.toCycles_i] }
    have : Epi b.τ₁ := inferInstanceAs (Epi (𝟙 _))
    have : IsIso b.τ₂ := inferInstanceAs (IsIso (𝟙 _))
    have : Mono b.τ₃ := (h (n + 1 + 1)).mono_f
    exact (C.exactAt_iff' n (n + 1) (n + 1 + 1) (by simp) (by simp)).mpr
      ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono b).mp hs)
  intro n
  simpa using he (n - 1)

end

end CochainComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- Compatibility theorem for the same native cycle sequence. The sole
short-exactness proof is `cycleSequence_shortExact`. -/
theorem shortExact_cycles (K : CochainComplex C ℤ) (n : ℤ) (h : K.ExactAt (n + 1)) :
    (ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1)) (by
      rw [← cancel_mono (K.iCycles (n + 1)), Category.assoc, toCycles_i,
        iCycles_d, zero_comp])).ShortExact :=
  cycleSequence_shortExact K n h

end CochainComplex
