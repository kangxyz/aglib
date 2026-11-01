/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionSingleModelFormula
public import Aglib.CategoryTheory.Functor.ImageCartesianCompositionIso

/-! # Original single-value composition formula with explicit map arguments

The actual isomorphism and actual Cartesian map stay explicit at the regular
formula boundary. The proof reuses the original single-value component theorem.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wY wZ wF wG wFG wRaw wTop

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [QuasiCompact f] [QuasiCompact g]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [hZ : HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  [firstModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wF} (ModuleSheaf C.Xbar Λ)]
  [secondModels : ∀ C : Hom.DenseCompactification g,
    HasDerivedCategory.{wG} (ModuleSheaf C.Xbar Λ)]
  [compositeModels : ∀ C : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wFG} (ModuleSheaf C.Xbar Λ)]

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

variable (C : Hom.CompactifiedComposition f g) (F : Hom.DenseCompactification f)
  (hRaw : HasDerivedCategory.{wRaw} (ModuleSheaf F.Xbar Λ))
  (hTop : HasDerivedCategory.{wTop} (ModuleSheaf C.composite.Xbar Λ))

variable (m : F.Xbar ⟶ C.sourceCompactification.Xbar) [IsOpenImmersion m]
  (sq : IsPullback m F.p C.sourceCompactification.p C.targetCompactification.j)
  (a : F ⟶ C.first)
  (sqMid : IsPullback m a.hom (𝟙 C.sourceCompactification.Xbar) C.middleOpen)
  (hj : F.j ≫ m = C.sourceCompactification.j)

include sqMid in
/-- Keep both actual maps opaque while exporting the proved original component formula. -/
theorem moduleExceptionalUnboundedCompositionSingleModelIso_formula
    (E : @moduleUnboundedCompactificationFunctor X Y f Λ _ hX hY F hRaw ⋙
        @moduleUnboundedCompactificationFunctor Y Z g Λ _ hY hZ C.targetCompactification
          (secondModels C.targetCompactification) ≅
      @moduleUnboundedCompactificationFunctor X Z (f ≫ g) Λ _ hX hZ C.composite hTop)
    (α : @moduleUnboundedCompactificationFunctor X Y f Λ _ hX hY F hRaw ⋙
        @moduleUnboundedCompactificationFunctor Y Z g Λ _ hY hZ C.targetCompactification
          (secondModels C.targetCompactification) ⟶
      @moduleUnboundedCompactificationFunctor X Z (f ≫ g) Λ _ hX hZ C.composite hTop)
    (hE : E = moduleExceptionalUnboundedCompositionSingleModelIso f g Λ N hN hΛ
      C F hRaw hTop)
    (hα : α = moduleUnboundedCartesianCompositionUnderlyingMap C F m sq hj Λ
      hX hY hZ hRaw (secondModels C.targetCompactification) hTop) :
    OriginalIsoHomFormula E α := by
  subst E
  subst α
  intro K
  exact moduleExceptionalUnboundedCompositionSingleModelIso_hom_app f g Λ N hN hΛ
    C F hRaw hTop m sq a sqMid hj K

end AlgebraicGeometry.Scheme.EtaleCohomology
