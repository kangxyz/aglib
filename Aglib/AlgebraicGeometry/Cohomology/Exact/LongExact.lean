/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Modules.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Aglib.AlgebraicGeometry.Cohomology.Flasque.Basic
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

This module owns generic cohomology exactness and injectivity of H⁰ for
coefficient monomorphisms. The short-exact specialization is named
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
    ShortComplex (Sheaf (Opens.grothendieckTopology X.left) AddCommGrpCat.{u}) := by
  let F : X.left.Modules ⥤ Sheaf (Opens.grothendieckTopology X.left) AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf X.left.ringCatSheaf
  let : F.Additive := ⟨by intros; rfl⟩
  exact S.map F

/-- Actual module short exactness gives actual additive-sheaf short exactness. -/
theorem coefficientSequence_shortExact (S : ShortComplex X.left.Modules) (hS : S.ShortExact) :
    (coefficientSequence X S).ShortExact :=
  AlgebraicGeometry.Scheme.Modules.shortExact_toSheaf hS

/-- Structural field scalars form an endomorphism of the actual short complex. -/
def coefficientSequenceScalar (S : ShortComplex X.left.Modules) (a : K) :
    coefficientSequence X S ⟶ coefficientSequence X S where
  τ₁ := moduleScalar X S.X₁ a
  τ₂ := moduleScalar X S.X₂ a
  τ₃ := moduleScalar X S.X₃ a
  comm₁₂ := moduleScalar_naturality X S.f a
  comm₂₃ := moduleScalar_naturality X S.g a

/-- The native connecting map, linear for the original structural field action. -/
def moduleCohomologyConnecting (S : ShortComplex X.left.Modules)
    (hS : S.ShortExact) (n : ℕ) :
    moduleCohomology K X S.X₃ n →ₗ[K] moduleCohomology K X S.X₁ (n + 1) := by
  let : HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X.left) AddCommGrpCat.{u}) :=
    structureSheafHasExt X.left
  refine { __ := Sheaf.H.δ.{u + 1, u, u, u} (coefficientSequence_shortExact X S hS) n (n + 1) rfl
           map_smul' := ?_ }
  intro a x
  exact Sheaf.H.δ_naturality.{u + 1, u, u, u} n (n + 1) rfl (coefficientSequence_shortExact X S hS)
      (coefficientSequence_shortExact X S hS)
      (coefficientSequenceScalar X S a) x

theorem moduleCohomologyMap_exact (S : ShortComplex X.left.Modules)
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (moduleCohomologyMap X S.f n) (moduleCohomologyMap X S.g n) := by
  let : HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X.left) AddCommGrpCat.{u}) :=
    structureSheafHasExt X.left
  exact (ShortComplex.ab_exact_iff_function_exact _).mp (Sheaf.H.longSequence_exact₂'.{u + 1, u,
    u, u} (coefficientSequence_shortExact X S hS) n)

theorem moduleCohomologyConnecting_exact_right (S : ShortComplex X.left.Modules)
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (moduleCohomologyConnecting X S hS n)
      (moduleCohomologyMap X S.f (n + 1)) := by
  let : HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X.left) AddCommGrpCat.{u}) :=
    structureSheafHasExt X.left
  exact (ShortComplex.ab_exact_iff_function_exact _).mp (Sheaf.H.longSequence_exact₁'.{u + 1, u,
    u, u} (coefficientSequence_shortExact X S hS) n (n + 1) rfl)

theorem moduleCohomologyConnecting_exact_left (S : ShortComplex X.left.Modules)
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (moduleCohomologyMap X S.g n)
      (moduleCohomologyConnecting X S hS n) := by
  let : HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X.left) AddCommGrpCat.{u}) :=
    structureSheafHasExt X.left
  exact (ShortComplex.ab_exact_iff_function_exact _).mp (Sheaf.H.longSequence_exact₃'.{u + 1, u,
    u, u} (coefficientSequence_shortExact X S hS) n (n + 1) rfl)

/-- A coefficient monomorphism induces an injective map on actual structural-field H⁰.
Extracted from `R5Lab.AlgebraicGeometry.Curves.Cohomology.QuotientEuler:113–128`
at R5Lab revision `95a3772b895fbc19a81684be4ffd519d0fdcd6b3`. -/
theorem moduleH0Map_injective {M N : X.left.Modules} (f : M ⟶ N) [Mono f] :
    Function.Injective (moduleCohomologyMap X f 0) := by
  let ev : X.left.Modules ⥤ ModuleCat Γ(X.left,⊤) := SheafOfModules.evaluation
    X.left.ringCatSheaf (op ⊤)
  have : PreservesLimits ev := inferInstanceAs
    (PreservesLimits (SheafOfModules.evaluation X.left.ringCatSheaf (op ⊤)))
  have hinj : Function.Injective (f.app ⊤) := (ModuleCat.mono_iff_injective (ev.map f)).mp
    inferInstance
  intro a b hab
  apply (moduleH0Equiv X M).injective
  apply hinj
  have h := congrArg (moduleH0Equiv X N) hab
  change Sheaf.H.equiv₀.{u + 1,u,u,u} (moduleAddSheaf X.left N) isTerminalTop
    (Sheaf.H.map (coefficientSheafMap X f) 0 a) =
      Sheaf.H.equiv₀.{u + 1,u,u,u} (moduleAddSheaf X.left N) isTerminalTop
        (Sheaf.H.map (coefficientSheafMap X f) 0 b) at h
  rw [← Sheaf.H.equiv₀_naturality, ← Sheaf.H.equiv₀_naturality] at h
  exact h

/-- A module-sheaf monomorphism in a short exact sequence induces an injective actual H0 map. -/
theorem moduleH0Map_injective_of_shortExact (S : ShortComplex X.left.Modules)
    (hS : S.ShortExact) :
    Function.Injective (moduleCohomologyMap X S.f 0) := by
  let : HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X.left) AddCommGrpCat.{u}) :=
    structureSheafHasExt X.left
  let : Mono (coefficientSequence X S).f := (coefficientSequence_shortExact X S hS).mono_f
  intro x y h
  apply (Ext.addEquiv₀.{u + 1}).injective
  apply (cancel_mono (coefficientSequence X S).f).mp
  change Sheaf.H.map (coefficientSequence X S).f 0 x =
    Sheaf.H.map (coefficientSequence X S).f 0 y at h
  simpa only [Sheaf.H.addEquiv₀_map] using! congrArg (Ext.addEquiv₀.{u + 1}) h

end AlgebraicGeometry.Scheme.Cohomology
