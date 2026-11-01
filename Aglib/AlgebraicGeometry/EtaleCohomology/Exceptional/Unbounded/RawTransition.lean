/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawBaseChange
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperRefinementIsomorphism
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RefinementDirectImage
public import Aglib.CategoryTheory.Functor.ImageComparison

/-! # Original unbounded transitions between raw compactifications

The map uses the original adjunction unit followed by the original structural
proper-image comparison. Density is not needed; all intermediate models remain
independent. Invertibility is proved for the stated torsion coefficient ring.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wC wD

variable {X S : Scheme.{u}} {f : X ⟶ S}
  (C D : Hom.Compactification f) (h : C.Xbar ⟶ D.Xbar)
  (sq : IsPullback C.j (𝟙 X) h D.j) (hp : h ≫ D.p = C.p)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)]

/-- The actual unit-induced raw compactification transition. -/
def moduleUnboundedRawCompactificationTransition :
    moduleUnboundedRawCompactificationFunctor D Λ ⟶
      moduleUnboundedRawCompactificationFunctor C Λ :=
  imageComparison (moduleUnboundedDerivedProperRefinementComparison C.j D.j h sq Λ)
    (moduleUnboundedDerivedDirectImageOverIso Λ C.p D.p h hp)

/-- Properness and the actual torsion-ring PBC theorem make this same transition invertible. -/
theorem moduleUnboundedRawCompactificationTransition_isIso [IsProper h]
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0) :
    IsIso (moduleUnboundedRawCompactificationTransition C D h sq hp Λ) := by
  have (K : DerivedCategory (ModuleSheaf X Λ)) :
      IsIso ((moduleUnboundedRawCompactificationTransition C D h sq hp Λ).app K) := by
    let := moduleUnboundedDerivedProperRefinementComparison_isIso C.j D.j h sq Λ N hN hΛ K
    exact imageComparison_isIso_app _ _ K
  exact NatIso.isIso_of_isIso_app _

/-- The isomorphism attached to the unchanged original raw transition. -/
def moduleUnboundedRawCompactificationTransitionIso [IsProper h]
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0) :
    moduleUnboundedRawCompactificationFunctor D Λ ≅
      moduleUnboundedRawCompactificationFunctor C Λ := by
  let := moduleUnboundedRawCompactificationTransition_isIso C D h sq hp Λ N hN hΛ
  exact asIso (moduleUnboundedRawCompactificationTransition C D h sq hp Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
