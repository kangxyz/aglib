/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionRawSquare
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CartesianFirstTargetComparison
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CartesianCompositionCanonical

/-!
# Choice-independent composition of exceptional direct images

The original compactified composition maps are transported to the chosen native
unbounded functors. Their actual refinement cube and an actual common
refinement prove independence of the supplied compactification tower. This file
addresses binary composition; associativity and unit coherence are separate.
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
  (K : DerivedCategory (ModuleSheaf X Λ))

include sqMid in
/-- The transported original compositor is the actual Cartesian map on every object. -/
theorem moduleExceptionalUnboundedCompositionSingleModelIso_hom_app :
    (moduleExceptionalUnboundedCompositionSingleModelIso f g Λ N hN hΛ C F hRaw hTop).hom.app K =
      (moduleUnboundedCartesianCompositionUnderlyingMap C F m sq hj Λ hX hY hZ hRaw
        (secondModels C.targetCompactification) hTop).app K := by
  let source := compositionPairIso
    (moduleExceptionalUnboundedSingleValueIso f Λ N hN hΛ F hRaw)
    (moduleExceptionalUnboundedSingleValueIso g Λ N hN hΛ C.targetCompactification
      (secondModels C.targetCompactification))
  have hc := congrArg (fun e => e.hom.app K)
    (moduleExceptionalUnboundedCompositionSingleModelIso_comparison f g Λ N hN hΛ
      C F hRaw hTop)
  simp only [Iso.trans_hom, NatTrans.comp_app] at hc
  have hr := moduleExceptionalUnboundedCompositionRawSquare f g Λ N hN hΛ
    C F hRaw hTop m sq a sqMid hj K
  exact (cancel_epi (source.hom.app K)).1 (hc.trans hr.symm)

end AlgebraicGeometry.Scheme.EtaleCohomology
