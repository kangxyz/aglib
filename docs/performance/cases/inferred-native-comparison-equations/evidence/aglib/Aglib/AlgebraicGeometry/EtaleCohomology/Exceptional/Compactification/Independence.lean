/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.Diagram
public import Aglib.AlgebraicGeometry.Compactification.Refinements.Cofiltered
public import Aglib.CategoryTheory.Filtered.InvertibleDiagram

/-!
# Canonical independence of the original compactification functors

Actual common refinements and the proved original transition laws identify
any two compactification functors. The comparison is computed by any common
refinement and satisfies identity and cocycle equations. Its source is the
native torsion full subcategory and its target is the ambient native D+.
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

/-- The original proper-image/open-extension functors have canonical comparisons,
independent of the chosen common refinement. -/
def moduleCompactificationComparison (C D : Hom.DenseCompactification f) :
    moduleCompactificationFunctor f Λ C ≅ moduleCompactificationFunctor f Λ D :=
  (moduleCompactificationDiagram (f := f) Λ).cofilteredComparison C D

/-- Every actual common refinement computes the same canonical comparison. -/
theorem moduleCompactificationComparison_eq_span
    {C D E : Hom.DenseCompactification f} (a : E ⟶ C) (b : E ⟶ D) :
    moduleCompactificationComparison f Λ C D =
      asIso (moduleCompactificationTransition Λ a) ≪≫
        (asIso (moduleCompactificationTransition Λ b)).symm :=
  (moduleCompactificationDiagram (f := f) Λ).cofilteredComparison_eq_span a b

/-- The canonical self-comparison is the identity natural isomorphism. -/
@[simp]
theorem moduleCompactificationComparison_self (C : Hom.DenseCompactification f) :
    moduleCompactificationComparison f Λ C C = Iso.refl _ :=
  (moduleCompactificationDiagram (f := f) Λ).cofilteredComparison_self C

/-- Canonical comparisons obey the original choice-independent cocycle equation. -/
@[simp]
theorem moduleCompactificationComparison_trans (C D E : Hom.DenseCompactification f) :
    moduleCompactificationComparison f Λ C D ≪≫ moduleCompactificationComparison f Λ D E =
      moduleCompactificationComparison f Λ C E :=
  (moduleCompactificationDiagram (f := f) Λ).cofilteredComparison_trans C D E

/-- Reversing the two compactifications inverts the canonical comparison. -/
@[simp]
theorem moduleCompactificationComparison_symm (C D : Hom.DenseCompactification f) :
    (moduleCompactificationComparison f Λ C D).symm = moduleCompactificationComparison f Λ D C :=
  (moduleCompactificationDiagram (f := f) Λ).cofilteredComparison_symm C D

/-- On an actual refinement, the comparison retains the inverse of the original
contravariant transition, rather than choosing an unrelated isomorphism. -/
theorem moduleCompactificationComparison_refinement
    {C D : Hom.DenseCompactification f} (a : C ⟶ D) :
    moduleCompactificationComparison f Λ C D =
      (asIso (moduleCompactificationTransition Λ a)).symm :=
  (moduleCompactificationDiagram (f := f) Λ).cofilteredComparison_eq_inv_map a

/-- The canonical comparisons are compatible with every original refinement map. -/
@[reassoc]
theorem moduleCompactificationComparison_naturality
    {C C' D : Hom.DenseCompactification f} (a : C' ⟶ C) :
    moduleCompactificationTransition Λ a ≫ (moduleCompactificationComparison f Λ C' D).hom =
      (moduleCompactificationComparison f Λ C D).hom :=
  (moduleCompactificationDiagram (f := f) Λ).cofilteredComparison_naturality a

end AlgebraicGeometry.Scheme.EtaleCohomology
