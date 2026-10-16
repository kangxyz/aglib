/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# An elementwise quasi-isomorphism criterion for module complexes

A morphism of short complexes induces an isomorphism on homology when cycles
lift and a cycle whose image is a boundary was already a boundary. The proof
uses the actual kernel/range-quotient homology data in the module category.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Ring R]

set_option backward.isDefEq.respectTransparency false in
/-- Cycle lifting and reflection of boundaries imply an actual quasi-isomorphism. -/
theorem quasiIso_of_liftCycles_of_reflectBoundaries
    {S T : ShortComplex (ModuleCat.{v} R)} (φ : S ⟶ T)
    (hcycle : ∀ y : T.X₂, T.g y = 0 → ∃ x : S.X₂, S.g x = 0 ∧ φ.τ₂ x = y)
    (hboundary : ∀ x : S.X₂, S.g x = 0 →
      (∃ y : T.X₁, T.f y = φ.τ₂ x) → ∃ z : S.X₁, S.f z = x) :
    ShortComplex.QuasiIso φ := by
  let γ : ShortComplex.LeftHomologyMapData φ
      S.moduleCatLeftHomologyData T.moduleCatLeftHomologyData := default
  have hK (x : LinearMap.ker S.g.hom) : (γ.φK x).val = φ.τ₂ x.val :=
    by
      have h := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp γ.commi) x
      exact h
  have hH (x : LinearMap.ker S.g.hom) :
      γ.φH (Submodule.Quotient.mk x) = Submodule.Quotient.mk (γ.φK x) :=
    ConcreteCategory.congr_hom γ.commπ x
  rw [γ.quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  constructor
  · apply (injective_iff_map_eq_zero γ.φH.hom).mpr
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      rw [hH] at hx
      obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
      obtain ⟨z, hz⟩ := hboundary x.val x.property ⟨y, by
        exact (congrArg Subtype.val hy).trans (hK x)⟩
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨z, Subtype.ext hz⟩
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      obtain ⟨x, hx, hxy⟩ := hcycle y.val y.property
      refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
      rw [hH]
      congr 1
      exact Subtype.ext ((hK ⟨x, hx⟩).trans hxy)

end CategoryTheory.ShortComplex
