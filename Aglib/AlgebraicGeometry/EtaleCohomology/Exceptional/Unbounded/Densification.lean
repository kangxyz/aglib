/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.Densification
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawTransition

/-! # Original unbounded closed-densification comparison

The schematic-image normalization is related to the raw model by its original
proper-refinement transition. No density preservation under pullback is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wC wD

variable {X S : Scheme.{u}} {f : X ⟶ S}
  (C : Hom.Compactification f) [QuasiCompact C.j]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf (Hom.Compactification.densify C).Xbar Λ)]

/-- The original unit-induced closed-densification map on the full unbounded category. -/
def moduleUnboundedCompactificationDensificationMap :
    moduleUnboundedRawCompactificationFunctor C Λ ⟶
      moduleUnboundedRawCompactificationFunctor
        (Hom.Compactification.densify C).toCompactification Λ :=
  moduleUnboundedRawCompactificationTransition
    (Hom.Compactification.densify C).toCompactification C
    (Hom.Compactification.densifyι C) (Hom.Compactification.isPullback_densify C)
    (Hom.Compactification.densifyι_p C) Λ

/-- The same actual closed-densification map is an isomorphism over the torsion ring. -/
def moduleUnboundedCompactificationDensificationIso
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0) :
    moduleUnboundedRawCompactificationFunctor C Λ ≅
      moduleUnboundedRawCompactificationFunctor
        (Hom.Compactification.densify C).toCompactification Λ :=
  moduleUnboundedRawCompactificationTransitionIso
    (Hom.Compactification.densify C).toCompactification C
    (Hom.Compactification.densifyι C) (Hom.Compactification.isPullback_densify C)
    (Hom.Compactification.densifyι_p C) Λ N hN hΛ

/-- The forward map is the original map, not a newly selected isomorphism. -/
theorem moduleUnboundedCompactificationDensificationIso_hom
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0) :
    (moduleUnboundedCompactificationDensificationIso C Λ N hN hΛ).hom =
      moduleUnboundedCompactificationDensificationMap C Λ := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
