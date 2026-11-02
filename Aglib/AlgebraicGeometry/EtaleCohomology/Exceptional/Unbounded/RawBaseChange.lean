/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompactifiedBaseChange
public import Aglib.AlgebraicGeometry.Compactification.Refinements.CartesianBaseChange

/-! # Genuine unbounded base change for the literal raw compactification

Only the existing geometric Cartesian open square is reused from the
bounded-below leaf. Every functor and map below is genuinely unbounded. The
pullback compactification is not asserted dense; the new base is arbitrary.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wY wX' wY' wT

variable {X S T : Scheme.{u}} {f : X ⟶ S}
  (C : Hom.Compactification f) (b : T ⟶ S)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wY} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wY'} (ModuleSheaf (pullback b C.p) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]

/-- Reuse the selected derived category on `pullback b C.p` for the raw base-change ambient
scheme. -/
local instance unboundedRawBaseChangeModel :
    HasDerivedCategory.{wY'} (ModuleSheaf (C.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wY'} (ModuleSheaf (pullback b C.p) Λ))

/-- The specified raw model is the original exact open extension followed by unbounded R*. -/
def moduleUnboundedRawCompactificationFunctor :
    DerivedCategory (ModuleSheaf X Λ) ⥤ DerivedCategory (ModuleSheaf S Λ) :=
  moduleUnboundedDerivedLowerShriek C.j Λ ⋙ moduleUnboundedDerivedDirectImage Λ C.p

/-- Actual arbitrary base change with the literal raw pullback compactification. -/
def moduleUnboundedRawCompactificationBaseChangeIso
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0) :
    moduleUnboundedRawCompactificationFunctor C Λ ⋙ moduleUnboundedDerivedInverseImage Λ b ≅
      moduleUnboundedDerivedInverseImage Λ (pullback.snd b f) ⋙
        moduleUnboundedRawCompactificationFunctor (C.baseChange b) Λ :=
  moduleUnboundedCompactifiedBaseChangeIso C.j C.p (C.baseChange b).j
    (pullback.fst b C.p) (pullback.snd b f) (pullback.snd b C.p) b
    (isPullback_rawCompactificationOpen C b) (IsPullback.of_hasPullback b C.p).flip Λ N hN hΛ

/-- The raw comparison retains the literal original unbounded exchange. -/
theorem moduleUnboundedRawCompactificationBaseChangeIso_hom
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0) :
    (moduleUnboundedRawCompactificationBaseChangeIso C b Λ N hN hΛ).hom =
      moduleUnboundedCompactifiedBaseChangeMap C.j C.p (C.baseChange b).j
        (pullback.fst b C.p) (pullback.snd b f) (pullback.snd b C.p) b
        (isPullback_rawCompactificationOpen C b) (IsPullback.of_hasPullback b C.p).flip Λ := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
