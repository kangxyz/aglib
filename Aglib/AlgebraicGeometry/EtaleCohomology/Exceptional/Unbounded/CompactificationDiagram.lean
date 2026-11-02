/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ComparisonAlgebra
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RefinementDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RefinementCoherence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RefinementIsomorphism

/-!
# The original unbounded compactification diagram

The value is the actual exact open extension followed by the native unbounded
proper right-derived image. Its contravariant arrows retain the original
adjunction unit and structural direct-image comparison. Their original coherence
makes a genuine diagram; actual proper base change makes all arrows invertible
for a torsion coefficient ring. No boundedness restriction is imposed.
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


section Value

variable (C : Hom.DenseCompactification f)
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- The actual functor through a specified compactification on all native derived objects. -/
def moduleUnboundedCompactificationFunctor :
    DerivedCategory (ModuleSheaf X Λ) ⥤
      DerivedCategory (ModuleSheaf S Λ) :=
  moduleUnboundedDerivedLowerShriek C.j Λ ⋙ moduleUnboundedDerivedDirectImage Λ C.p

end Value

variable [middleModels : ∀ C : Hom.DenseCompactification f,
  HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

variable {f}

/-- The actual contravariant transition attached to a proper refinement. -/
def moduleUnboundedCompactificationTransition {C D : Hom.DenseCompactification f} (a : C ⟶ D) :
    moduleUnboundedCompactificationFunctor f Λ D ⟶
      moduleUnboundedCompactificationFunctor f Λ C :=
  imageComparison (moduleUnboundedDerivedRefinementComparison a Λ)
    (moduleUnboundedDerivedRefinementDirectImageIso Λ a)

/-- Components retain the original refinement map and direct-image identification. -/
theorem moduleUnboundedCompactificationTransition_app {C D : Hom.DenseCompactification f}
    (a : C ⟶ D) (K : DerivedCategory (ModuleSheaf X Λ)) :
    (moduleUnboundedCompactificationTransition Λ a).app K =
      (moduleUnboundedDerivedDirectImage Λ D.p).map
          ((moduleUnboundedDerivedRefinementComparison a Λ).app K) ≫
        (moduleUnboundedDerivedRefinementDirectImageIso Λ a).hom.app
          ((moduleUnboundedDerivedLowerShriek C.j Λ).obj K) :=
  imageComparison_app _ _ K

/-- Identity refinements act by the literal identity natural transformation. -/
theorem moduleUnboundedCompactificationTransition_id (C : Hom.DenseCompactification f) :
    moduleUnboundedCompactificationTransition Λ (𝟙 C) =
      𝟙 (moduleUnboundedCompactificationFunctor f Λ C) := by
  have h := imageComparison_id (moduleUnboundedDerivedRefinementComparison (𝟙 C) Λ)
    (moduleUnboundedDerivedDirectImageIdIso Λ C.Xbar)
    (moduleUnboundedDerivedRefinementDirectImageIso Λ (𝟙 C))
    (moduleUnboundedDerivedRefinementComparison_id Λ C)
    (moduleUnboundedDerivedRefinementDirectImageIso_id Λ C)
  exact h

/-- The unchanged original refinement transitions compose contravariantly. -/
theorem moduleUnboundedCompactificationTransition_comp {C D E : Hom.DenseCompactification f}
    (a : C ⟶ D) (b : D ⟶ E) :
    moduleUnboundedCompactificationTransition Λ (a ≫ b) =
      moduleUnboundedCompactificationTransition Λ b ≫
        moduleUnboundedCompactificationTransition Λ a := by
  have h := imageComparison_comp (moduleUnboundedDerivedRefinementComparison a Λ)
    (moduleUnboundedDerivedRefinementComparison b Λ)
    (moduleUnboundedDerivedRefinementComparison (a ≫ b) Λ)
    (moduleUnboundedDerivedDirectImageCompIso Λ b.hom a.hom)
    (moduleUnboundedDerivedRefinementDirectImageIso Λ a)
    (moduleUnboundedDerivedRefinementDirectImageIso Λ b)
    (moduleUnboundedDerivedRefinementDirectImageIso Λ (a ≫ b))
    (moduleUnboundedDerivedRefinementComparison_comp Λ a b)
    (moduleUnboundedDerivedRefinementDirectImageIso_comp Λ a b)
  exact h

/-- Proper base change makes every original transition invertible over a torsion ring. -/
theorem moduleUnboundedCompactificationTransition_isIso
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)
    {C D : Hom.DenseCompactification f} (a : C ⟶ D) :
    IsIso (moduleUnboundedCompactificationTransition Λ a) := by
  have (K : DerivedCategory (ModuleSheaf X Λ)) :
      IsIso ((moduleUnboundedCompactificationTransition Λ a).app K) := by
    let : IsIso ((moduleUnboundedDerivedRefinementComparison a Λ).app K) :=
      moduleUnboundedDerivedRefinementComparison_isIso a Λ N hN hΛ K
    exact imageComparison_isIso_app (moduleUnboundedDerivedRefinementComparison a Λ)
      (moduleUnboundedDerivedRefinementDirectImageIso Λ a) K
  exact NatIso.isIso_of_isIso_app _

/-- The original proper-image/open-extension construction is a contravariant
functor on dense compactifications, not merely a collection of isomorphic objects. -/
def moduleUnboundedCompactificationDiagram :
    (Hom.DenseCompactification f)ᵒᵖ ⥤
      (DerivedCategory (ModuleSheaf X Λ) ⥤
        DerivedCategory (ModuleSheaf S Λ)) where
  obj C := moduleUnboundedCompactificationFunctor f Λ C.unop
  map a := moduleUnboundedCompactificationTransition Λ a.unop
  map_id C := moduleUnboundedCompactificationTransition_id Λ C.unop
  map_comp a b := moduleUnboundedCompactificationTransition_comp Λ b.unop a.unop

/-- Every arrow of the actual compactification diagram is invertible. -/
theorem moduleUnboundedCompactificationDiagram_map_isIso
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)
    (C D : (Hom.DenseCompactification f)ᵒᵖ) (a : C ⟶ D) :
    IsIso ((moduleUnboundedCompactificationDiagram Λ).map a) :=
  moduleUnboundedCompactificationTransition_isIso Λ N hN hΛ a.unop

end AlgebraicGeometry.Scheme.EtaleCohomology
