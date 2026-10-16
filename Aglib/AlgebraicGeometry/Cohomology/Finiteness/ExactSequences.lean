/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Exact.LongExact
public import Aglib.RingTheory.Finiteness.Exact

/-!
# Finiteness under actual cohomology exact sequences

The actual linear connecting maps transfer finite-dimensionality across
module-sheaf extensions. Every finite-dimensional or vanishing input is
explicit; no proper finiteness or dimension-vanishing family is used.

Source: `R5Lab.AlgebraicGeometry.Curves.RiemannRoch.CurveEuler` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`. LinearAlgebra and module-cohomology
  finite-middle/left/H0-H1 declarations only.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {K : Type u} [Field K] (X : FScheme K)

section LinearAlgebra
variable {k A B C : Type*} [Field k] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module k A] [Module k B] [Module k C]
/-- Finite outer vector spaces force a finite middle term, without a surjectivity hypothesis. -/
theorem finite_middle_of_exact (f : A →ₗ[k] B) (g : B →ₗ[k] C)
    (h : Function.Exact f g) [Module.Finite k A] [Module.Finite k C] :
    Module.Finite k B :=
  Module.Finite.of_exact_of_isNoetherian f g h
end LinearAlgebra

/-- Finiteness of actual cohomology is preserved under module-sheaf extensions. -/
theorem moduleCohomology_finite_middle (S : ShortComplex X.left.Modules)
    (hS : S.ShortExact) (n : ℕ)
    [Module.Finite K (moduleCohomology K X S.X₁ n)]
    [Module.Finite K (moduleCohomology K X S.X₃ n)] :
    Module.Finite K (moduleCohomology K X S.X₂ n) :=
  finite_middle_of_exact _ _ (moduleCohomologyMap_exact X S hS n)

/-- The actual connecting map transfers finiteness to the next left cohomology group. -/
theorem moduleCohomology_finite_left_succ (S : ShortComplex X.left.Modules)
    (hS : S.ShortExact) (n : ℕ)
    [Module.Finite K (moduleCohomology K X S.X₃ n)]
    [Module.Finite K (moduleCohomology K X S.X₂ (n + 1))] :
    Module.Finite K (moduleCohomology K X S.X₁ (n + 1)) :=
  finite_middle_of_exact _ _ (moduleCohomologyConnecting_exact_right X S hS n)

/-- Actual H0 of a submodule sheaf embeds in actual H0 of the containing sheaf. -/
theorem moduleH0_finite_left (S : ShortComplex X.left.Modules)
    (hS : S.ShortExact) [Module.Finite K (moduleCohomology K X S.X₂ 0)] :
    Module.Finite K (moduleCohomology K X S.X₁ 0) :=
  Module.Finite.of_injective (moduleCohomologyMap X S.f 0) (moduleH0Map_injective_of_shortExact
    X S hS)

/-- A quotient with finite H0 and H1 gives finiteness in both directions for H0 and H1. -/
theorem moduleH0H1_finite_iff (S : ShortComplex X.left.Modules) (hS : S.ShortExact)
    [Module.Finite K (moduleCohomology K X S.X₃ 0)]
    [Module.Finite K (moduleCohomology K X S.X₃ 1)] :
    (Module.Finite K (moduleCohomology K X S.X₁ 0) ∧
      Module.Finite K (moduleCohomology K X S.X₁ 1)) ↔
    (Module.Finite K (moduleCohomology K X S.X₂ 0) ∧
      Module.Finite K (moduleCohomology K X S.X₂ 1)) := by
  constructor
  · rintro ⟨h0, h1⟩
    let := h0
    let := h1
    exact ⟨moduleCohomology_finite_middle X S hS 0,
      moduleCohomology_finite_middle X S hS 1⟩
  · rintro ⟨h0, h1⟩
    let := h0
    let := h1
    exact ⟨moduleH0_finite_left X S hS, moduleCohomology_finite_left_succ X S hS 0⟩

end AlgebraicGeometry.Scheme.Cohomology
