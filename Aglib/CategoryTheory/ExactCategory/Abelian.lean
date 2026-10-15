/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Monomorphisms
/-!
# The standard exact structure on an abelian category

Every abelian category carries the exact structure whose conflations are all
short exact sequences. Its admissible monomorphisms are precisely all
monomorphisms, and its admissible epimorphisms are precisely all epimorphisms.
The Quillen axioms are proved from the abelian kernel/cokernel and base-change
theorems in mathlib.
-/
@[expose] public section


universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory

variable (C : Type u) [Category.{v} C] [Abelian C]

attribute [local instance] Abelian.hasFiniteBiproducts

/-- A map starts a short exact sequence exactly when it is a monomorphism. -/
theorem shortExact_inflation_iff {X Y : C} (i : X ⟶ Y) :
    Conflations.inflation C ShortComplex.ShortExact i ↔ Mono i := by
  constructor
  · rintro ⟨Z, p, h, hs⟩
    exact hs.mono_f
  · intro hi
    let _ := hi
    refine ⟨cokernel i, cokernel.π i, cokernel.condition i, ?_⟩
    exact { exact := ShortComplex.cokernelSequence_exact i }

/-- A map ends a short exact sequence exactly when it is an epimorphism. -/
theorem shortExact_deflation_iff {X Y : C} (p : X ⟶ Y) :
    Conflations.deflation C ShortComplex.ShortExact p ↔ Epi p := by
  constructor
  · rintro ⟨Z, i, h, hs⟩
    exact hs.epi_g
  · intro hp
    let _ := hp
    refine ⟨kernel p, kernel.ι p, kernel.condition p, ?_⟩
    exact { exact := ShortComplex.kernelSequence_exact p }

theorem shortExact_inflation_eq_monomorphisms :
    Conflations.inflation C ShortComplex.ShortExact = MorphismProperty.monomorphisms C := by
  funext X Y i
  exact propext (shortExact_inflation_iff C i)

theorem shortExact_deflation_eq_epimorphisms :
    Conflations.deflation C ShortComplex.ShortExact = MorphismProperty.epimorphisms C := by
  funext X Y p
  exact propext (shortExact_deflation_iff C p)

/-- The standard Quillen exact structure on an abelian category. -/
noncomputable def abelianExactStructure : ExactStructure C where
  conflation := ShortComplex.ShortExact
  kernel _ h := h.fIsKernel
  cokernel _ h := h.gIsCokernel
  iso_closed e h := ShortComplex.shortExact_of_iso e h
  inflation_id X := (shortExact_inflation_iff C (𝟙 X)).2 inferInstance
  deflation_id X := (shortExact_deflation_iff C (𝟙 X)).2 inferInstance
  inflation_comp i j hi hj := by
    rw [shortExact_inflation_iff] at hi hj ⊢
    let _ := hi
    let _ := hj
    infer_instance
  deflation_comp p q hp hq := by
    rw [shortExact_deflation_iff] at hp hq ⊢
    let _ := hp
    let _ := hq
    infer_instance
  inflation_hasPushouts := inferInstance
  inflation_cobaseChange := by
    rw [shortExact_inflation_eq_monomorphisms]
    infer_instance
  deflation_hasPullbacks := inferInstance
  deflation_baseChange := by
    rw [shortExact_deflation_eq_epimorphisms]
    infer_instance

@[simp]
theorem abelianExactStructure_conflation (S : ShortComplex C) :
    (abelianExactStructure C).conflation S ↔ S.ShortExact := Iff.rfl

@[simp]
theorem abelianExactStructure_inflation_iff {X Y : C} (i : X ⟶ Y) :
    (abelianExactStructure C).inflation i ↔ Mono i :=
  shortExact_inflation_iff C i

@[simp]
theorem abelianExactStructure_deflation_iff {X Y : C} (p : X ⟶ Y) :
    (abelianExactStructure C).deflation p ↔ Epi p :=
  shortExact_deflation_iff C p

end CategoryTheory.ExactCategory
