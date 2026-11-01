/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompactificationIndependence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.DirectImage

/-!
# Choice-independent actual unbounded exceptional direct image

The existing actual Nagata compactification selects the original exact open
extension followed by native unbounded proper direct image. Over a torsion ring,
actual proper base change and actual common refinements give canonical comparison
with every compactification, retaining the original transition maps and cocycle.
This construction uses no bounded-below transport. Composition and base-change
coherence of this unbounded endpoint are separate subsequent statements.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wM

variable {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
  (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

variable (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]


section Value

variable [HasDerivedCategory.{wM}
  (ModuleSheaf (moduleExceptionalCompactification f).Xbar Λ)]

/-- Actual unbounded exceptional image: original exact open extension followed by proper R*. -/
def moduleExceptionalDirectImageUnbounded :
    DerivedCategory (ModuleSheaf X Λ) ⥤
      DerivedCategory (ModuleSheaf S Λ) :=
  moduleUnboundedCompactificationFunctor f Λ (moduleExceptionalCompactification f)

end Value

variable [middleModels : ∀ C : Hom.DenseCompactification f,
  HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- Canonical comparison of the exceptional functor with every actual compactification. -/
def moduleExceptionalDirectImageUnboundedIso (C : Hom.DenseCompactification f) :
    moduleExceptionalDirectImageUnbounded f Λ ≅ moduleUnboundedCompactificationFunctor f Λ C :=
  moduleUnboundedCompactificationComparison f Λ N hN hΛ (moduleExceptionalCompactification f) C

/-- Changing compactification uses the same choice-independent cocycle. -/
theorem moduleExceptionalDirectImageUnboundedIso_trans (C D : Hom.DenseCompactification f) :
    moduleExceptionalDirectImageUnboundedIso f Λ N hN hΛ C ≪≫
      moduleUnboundedCompactificationComparison f Λ N hN hΛ C D =
      moduleExceptionalDirectImageUnboundedIso f Λ N hN hΛ D :=
  moduleUnboundedCompactificationComparison_trans f Λ N hN hΛ
    (moduleExceptionalCompactification f) C D

/-- Comparison with the compactification used in the definition is the identity. -/
@[simp]
theorem moduleExceptionalDirectImageUnboundedIso_self :
    moduleExceptionalDirectImageUnboundedIso f Λ N hN hΛ (moduleExceptionalCompactification f) =
      Iso.refl _ :=
  moduleUnboundedCompactificationComparison_self f Λ N hN hΛ (moduleExceptionalCompactification f)

/-- The chosen comparison commutes with the original proper-refinement transition. -/
theorem moduleExceptionalDirectImageUnboundedIso_refinement
    {C D : Hom.DenseCompactification f} (a : C ⟶ D) :
    moduleExceptionalDirectImageUnboundedIso f Λ N hN hΛ D ≪≫
      moduleUnboundedCompactificationTransitionIso f Λ N hN hΛ a =
    moduleExceptionalDirectImageUnboundedIso f Λ N hN hΛ C := by
  rw [← moduleExceptionalDirectImageUnboundedIso_trans f Λ N hN hΛ C D,
    moduleUnboundedCompactificationComparison_refinement f Λ N hN hΛ a]
  simp

end AlgebraicGeometry.Scheme.EtaleCohomology
