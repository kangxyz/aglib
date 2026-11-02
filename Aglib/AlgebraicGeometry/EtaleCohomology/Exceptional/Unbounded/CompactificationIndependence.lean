/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompactificationDiagram
public import Aglib.AlgebraicGeometry.Compactification.Refinements.Cofiltered
public import Aglib.CategoryTheory.Filtered.InvertibleDiagram

/-! # Canonical independence of the actual unbounded compactification functors

The actual contravariant diagram and actual common refinements supply canonical
comparisons. Every comparison retains the original unit transitions and obeys
their cocycle, on all unbounded objects over the stated torsion ring.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM
variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [middleModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The proved original refinement transition, regarded as an isomorphism. -/
def moduleUnboundedCompactificationTransitionIso {C D : Hom.DenseCompactification f}
    (a : C ⟶ D) :
    moduleUnboundedCompactificationFunctor f Λ D ≅
      moduleUnboundedCompactificationFunctor f Λ C := by
  let := moduleUnboundedCompactificationTransition_isIso Λ N hN hΛ a
  exact asIso (moduleUnboundedCompactificationTransition Λ a)

/-- Canonical comparisons between any two actual unbounded compactification values. -/
def moduleUnboundedCompactificationComparison (C D : Hom.DenseCompactification f) :
    moduleUnboundedCompactificationFunctor f Λ C ≅
      moduleUnboundedCompactificationFunctor f Λ D := by
  letI := moduleUnboundedCompactificationDiagram_map_isIso (f := f) Λ N hN hΛ
  exact (moduleUnboundedCompactificationDiagram (f := f) Λ).cofilteredComparison C D

/-- Every actual common refinement computes the original canonical comparison. -/
theorem moduleUnboundedCompactificationComparison_eq_span
    {C D E : Hom.DenseCompactification f} (a : E ⟶ C) (b : E ⟶ D) :
    moduleUnboundedCompactificationComparison f Λ N hN hΛ C D =
      moduleUnboundedCompactificationTransitionIso f Λ N hN hΛ a ≪≫
        (moduleUnboundedCompactificationTransitionIso f Λ N hN hΛ b).symm := by
  let := moduleUnboundedCompactificationDiagram_map_isIso (f := f) Λ N hN hΛ
  exact (moduleUnboundedCompactificationDiagram (f := f) Λ).cofilteredComparison_eq_span a b

/-- The canonical self-comparison is the identity. -/
@[simp]
theorem moduleUnboundedCompactificationComparison_self (C : Hom.DenseCompactification f) :
    moduleUnboundedCompactificationComparison f Λ N hN hΛ C C = Iso.refl _ := by
  let := moduleUnboundedCompactificationDiagram_map_isIso (f := f) Λ N hN hΛ
  exact (moduleUnboundedCompactificationDiagram (f := f) Λ).cofilteredComparison_self C

/-- Canonical comparisons satisfy the actual choice-independent cocycle. -/
@[simp]
theorem moduleUnboundedCompactificationComparison_trans (C D E : Hom.DenseCompactification f) :
    moduleUnboundedCompactificationComparison f Λ N hN hΛ C D ≪≫
      moduleUnboundedCompactificationComparison f Λ N hN hΛ D E =
    moduleUnboundedCompactificationComparison f Λ N hN hΛ C E := by
  let := moduleUnboundedCompactificationDiagram_map_isIso (f := f) Λ N hN hΛ
  exact (moduleUnboundedCompactificationDiagram (f := f) Λ).cofilteredComparison_trans C D E

/-- Reversing compactifications inverts the same canonical comparison. -/
@[simp]
theorem moduleUnboundedCompactificationComparison_symm (C D : Hom.DenseCompactification f) :
    (moduleUnboundedCompactificationComparison f Λ N hN hΛ C D).symm =
      moduleUnboundedCompactificationComparison f Λ N hN hΛ D C := by
  let := moduleUnboundedCompactificationDiagram_map_isIso (f := f) Λ N hN hΛ
  exact (moduleUnboundedCompactificationDiagram (f := f) Λ).cofilteredComparison_symm C D

/-- On an actual refinement the comparison is the inverse original transition. -/
theorem moduleUnboundedCompactificationComparison_refinement
    {C D : Hom.DenseCompactification f} (a : C ⟶ D) :
    moduleUnboundedCompactificationComparison f Λ N hN hΛ C D =
      (moduleUnboundedCompactificationTransitionIso f Λ N hN hΛ a).symm := by
  let := moduleUnboundedCompactificationDiagram_map_isIso (f := f) Λ N hN hΛ
  exact (moduleUnboundedCompactificationDiagram (f := f) Λ).cofilteredComparison_eq_inv_map a

/-- Every original refinement map commutes with the canonical comparison. -/
@[reassoc]
theorem moduleUnboundedCompactificationComparison_naturality
    {C C' D : Hom.DenseCompactification f} (a : C' ⟶ C) :
    moduleUnboundedCompactificationTransition Λ a ≫
      (moduleUnboundedCompactificationComparison f Λ N hN hΛ C' D).hom =
    (moduleUnboundedCompactificationComparison f Λ N hN hΛ C D).hom := by
  let := moduleUnboundedCompactificationDiagram_map_isIso (f := f) Λ N hN hΛ
  exact (moduleUnboundedCompactificationDiagram (f := f) Λ).cofilteredComparison_naturality a

end AlgebraicGeometry.Scheme.EtaleCohomology
