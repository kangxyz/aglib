/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Exact.Modules
public import Mathlib.Algebra.Exact.Sequence
public import Mathlib.RingTheory.Finiteness.Finsupp
/-!
# Actual linear cohomology sequences and finite-support Euler identities

The connecting maps here have literally the native additive `Sheaf.H.δ`
underlying maps. Their field linearity follows from naturality under the
structural scalar endomorphisms of an actual module-sheaf short exact sequence.
The coefficient maps retain the original `moduleCohomologyMap`.

Stalk scalar compatibility, extension finiteness and finite-support Euler
consequences are separate subject leaves.

These constructions do not assume proper cohomology finiteness, Riemann–Roch,
Picard degree, or a dimension-vanishing family. They serve both the actual H1
comparison and the finite-support Euler calculation.

This module retains the structural-field specializations of the generic
results in `Exact.Modules`, including injectivity of H⁰ for coefficient
monomorphisms. The short-exact specialization is named
`moduleH0Map_injective_of_shortExact`; both original hypothesis scopes are retained.

Authoring basis: project `3397a339b6a52fbba586dae127aa729d873b771d`,
Lean 4.34.1, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, and
Quillen `83629578a3d70787d41ec631f5234af8758716af`.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.RiemannRoch.CurveEuler` at R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
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
/-- The original module short complex, with only its module structure forgotten. -/
abbrev coefficientSequence (S : ShortComplex X.left.Modules) :
    ShortComplex (Sheaf (Opens.grothendieckTopology X.left) AddCommGrpCat.{u}) :=
  moduleCoefficientSequence X.left S

/-- Actual module short exactness gives actual additive-sheaf short exactness. -/
theorem coefficientSequence_shortExact (S : ShortComplex X.left.Modules) (hS : S.ShortExact) :
    (coefficientSequence X S).ShortExact :=
  moduleCoefficientSequence_shortExact X.left S hS

/-- Structural field scalars form an endomorphism of the actual short complex. -/
def coefficientSequenceScalar (S : ShortComplex X.left.Modules) (a : K) :
    coefficientSequence X S ⟶ coefficientSequence X S :=
  moduleCoefficientSequenceScalar X.left S (constants X a)

/-- The native connecting map, linear for the original structural field action. -/
def moduleCohomologyConnecting (S : ShortComplex X.left.Modules)
    (hS : S.ShortExact) (n : ℕ) :
    moduleCohomology K X S.X₃ n →ₗ[K] moduleCohomology K X S.X₁ (n + 1) :=
  moduleCohomologyConnectingOfHom X.left (constants X) S hS n

theorem moduleCohomologyMap_exact (S : ShortComplex X.left.Modules)
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (moduleCohomologyMap X S.f n) (moduleCohomologyMap X S.g n) :=
  moduleCohomologyMapOfHom_exact X.left (constants X) S hS n

theorem moduleCohomologyConnecting_exact_right (S : ShortComplex X.left.Modules)
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (moduleCohomologyConnecting X S hS n)
      (moduleCohomologyMap X S.f (n + 1)) :=
  moduleCohomologyConnectingOfHom_exact_right X.left (constants X) S hS n

theorem moduleCohomologyConnecting_exact_left (S : ShortComplex X.left.Modules)
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (moduleCohomologyMap X S.g n)
      (moduleCohomologyConnecting X S hS n) :=
  moduleCohomologyConnectingOfHom_exact_left X.left (constants X) S hS n

/-- A coefficient monomorphism induces an injective map on actual structural-field H⁰.
Extracted from `R5Lab.AlgebraicGeometry.Curves.Cohomology.QuotientEuler:113–128`
at R5Lab revision `95a3772b895fbc19a81684be4ffd519d0fdcd6b3`. -/
theorem moduleH0Map_injective {M N : X.left.Modules} (f : M ⟶ N) [Mono f] :
    Function.Injective (moduleCohomologyMap X f 0) :=
  moduleH0MapOfHom_injective X.left (constants X) f

/-- A module-sheaf monomorphism in a short exact sequence induces an injective actual H0 map. -/
theorem moduleH0Map_injective_of_shortExact (S : ShortComplex X.left.Modules)
    (hS : S.ShortExact) :
    Function.Injective (moduleCohomologyMap X S.f 0) := by
  let := hS.mono_f
  exact moduleH0Map_injective X S.f

end AlgebraicGeometry.Scheme.Cohomology
