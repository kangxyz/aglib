/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Finite orbit spans without finite underlying coefficients

A finite group acting linearly on a finite module over a field algebra admits
a finite-dimensional stable subspace over the field whose scalar span is the
whole module. This is a bridge to finite-field representation arguments, not
an assertion that the original module is finite-dimensional over that field.
-/

@[expose] public noncomputable section

namespace Representation

universe u v w z

variable {k : Type u} [Field k] {R : Type v} [CommRing R] [Algebra k R]
  {M : Type w} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [Module.Finite R M] {G : Type z} [Group G] [Finite G]

/-- A finite orbit span is stable over the smaller field and still generates
the whole original module over its original coefficient ring. -/
theorem exists_finiteDimensional_stable_span (ρ : Representation R G M) :
    ∃ W : Submodule k M, Module.Finite k W ∧
      (∀ g x, x ∈ W → ρ g x ∈ W) ∧ Submodule.span R (W : Set M) = ⊤ := by
  classical
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp (Module.Finite.fg_top (R := R) (M := M))
  let := hs.fintype
  let O : Set M := Set.range (fun a : G × s ↦ ρ a.1 a.2.val)
  let W : Submodule k M := Submodule.span k O
  have hO : O.Finite := Set.finite_range _
  have hW : Module.Finite k W := Module.Finite.of_fg (Submodule.fg_span hO)
  have hstable (g : G) : W ≤ W.comap ((ρ g).restrictScalars k) := by
    apply Submodule.span_le.mpr
    rintro x ⟨⟨h, y⟩, rfl⟩
    change ρ g (ρ h y.val) ∈ W
    apply Submodule.subset_span
    refine ⟨(g * h, y), ?_⟩
    exact congrArg (fun f : Module.End R M ↦ f y.val) (ρ.map_mul g h)
  refine ⟨W, hW, fun g x hx ↦ hstable g hx, ?_⟩
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  intro x hx
  apply Submodule.subset_span
  apply Submodule.subset_span
  refine ⟨(1, ⟨x, hx⟩), ?_⟩
  exact congrArg (fun f : Module.End R M ↦ f x) ρ.map_one

end Representation
