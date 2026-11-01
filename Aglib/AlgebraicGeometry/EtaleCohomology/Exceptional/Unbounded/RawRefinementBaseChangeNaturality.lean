/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.RawRefinementBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawBaseChangeNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.Densification

/-! # Original unbounded raw exchange under arbitrary common-open refinement -/

@[expose] public noncomputable section
open CategoryTheory Limits
universe u wX wS wC wD wX' wT wCR wDR

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable {X S T : Scheme.{u}} {f : X ⟶ S}
  (C D : Hom.Compactification f) (h : C.Xbar ⟶ D.Xbar)
  (sq : IsPullback C.j (𝟙 X) h D.j) (hp : h ≫ D.p = C.p) (b : T ⟶ S)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wCR} (ModuleSheaf (pullback b C.p) Λ)]
  [HasDerivedCategory.{wDR} (ModuleSheaf (pullback b D.p) Λ)]

local instance unboundedRawRefinementNaturalityCModel :
    HasDerivedCategory.{wCR} (ModuleSheaf (C.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wCR} (ModuleSheaf (pullback b C.p) Λ))
local instance unboundedRawRefinementNaturalityDModel :
    HasDerivedCategory.{wDR} (ModuleSheaf (D.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wDR} (ModuleSheaf (pullback b D.p) Λ))

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The same original raw exchange is natural for any specified Cartesian open
refinement. No density, properness of the refinement, or new-base qcqs premise
is required for this equality of the original maps. -/
theorem moduleUnboundedRawRefinementBaseChangeIso_naturality :
    Functor.whiskerRight (moduleUnboundedRawCompactificationTransition C D h sq hp Λ)
        (moduleUnboundedDerivedInverseImage Λ b) ≫
      (moduleUnboundedRawCompactificationBaseChangeIso C b Λ N hN hΛ).hom =
    (moduleUnboundedRawCompactificationBaseChangeIso D b Λ N hN hΛ).hom ≫
      Functor.whiskerLeft (moduleUnboundedDerivedInverseImage Λ (pullback.snd b f))
        (moduleUnboundedRawCompactificationTransition (C.baseChange b) (D.baseChange b)
          (Hom.Compactification.refinementBaseChangeMap C D h hp b)
          (Hom.Compactification.isPullback_refinementBaseChangeMap_open C D h hp b sq)
          (Hom.Compactification.refinementBaseChangeMap_fst C D h hp b) Λ) := by
  have hc := moduleUnboundedCompactifiedBaseChangeMap_refinement_naturality
    C.j D.j h sq (C.baseChange b).j (D.baseChange b).j
    (Hom.Compactification.refinementBaseChangeMap C D h hp b)
    (Hom.Compactification.isPullback_refinementBaseChangeMap_open C D h hp b sq)
    (pullback.snd b f) (pullback.snd b C.p) (pullback.snd b D.p)
    (isPullback_rawCompactificationOpen C b) (isPullback_rawCompactificationOpen D b)
    (Hom.Compactification.isPullback_refinementBaseChangeMap C D h hp b) Λ
    C.p D.p hp (pullback.fst b C.p) (pullback.fst b D.p)
    (Hom.Compactification.refinementBaseChangeMap_fst C D h hp b) b
    (IsPullback.of_hasPullback b C.p).flip (IsPullback.of_hasPullback b D.p).flip
  exact hc

end AlgebraicGeometry.Scheme.EtaleCohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable {X S T : Scheme.{u}} {f : X ⟶ S}
  (E : Hom.Compactification f) [QuasiCompact E.j] (b : T ⟶ S)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf (Hom.Compactification.densify E).Xbar Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf E.Xbar Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wCR}
    (ModuleSheaf (pullback b (Hom.Compactification.densify E).p) Λ)]
  [HasDerivedCategory.{wDR} (ModuleSheaf (pullback b E.p) Λ)]

local instance unboundedDensificationPullbackDenseModel :
    HasDerivedCategory.{wCR}
      (ModuleSheaf ((Hom.Compactification.densify E).toCompactification.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wCR}
    (ModuleSheaf (pullback b (Hom.Compactification.densify E).p) Λ))
local instance unboundedDensificationPullbackRawModel :
    HasDerivedCategory.{wDR} (ModuleSheaf (E.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wDR} (ModuleSheaf (pullback b E.p) Λ))

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The original closed-densification comparison commutes with the next raw
base change, through the actual ambient pullback of its closed inclusion. -/
theorem moduleUnboundedDensificationBaseChangeIso_naturality :
    Functor.whiskerRight (moduleUnboundedCompactificationDensificationMap E Λ)
        (moduleUnboundedDerivedInverseImage Λ b) ≫
      (moduleUnboundedRawCompactificationBaseChangeIso
        (Hom.Compactification.densify E).toCompactification b Λ N hN hΛ).hom =
    (moduleUnboundedRawCompactificationBaseChangeIso E b Λ N hN hΛ).hom ≫
      Functor.whiskerLeft (moduleUnboundedDerivedInverseImage Λ (pullback.snd b f))
        (moduleUnboundedRawCompactificationTransition
          ((Hom.Compactification.densify E).toCompactification.baseChange b) (E.baseChange b)
          (Hom.Compactification.refinementBaseChangeMap
            (Hom.Compactification.densify E).toCompactification E
            (Hom.Compactification.densifyι E) (Hom.Compactification.densifyι_p E) b)
          (Hom.Compactification.isPullback_refinementBaseChangeMap_open
            (Hom.Compactification.densify E).toCompactification E
            (Hom.Compactification.densifyι E) (Hom.Compactification.densifyι_p E) b
            (Hom.Compactification.isPullback_densify E))
          (Hom.Compactification.refinementBaseChangeMap_fst
            (Hom.Compactification.densify E).toCompactification E
            (Hom.Compactification.densifyι E) (Hom.Compactification.densifyι_p E) b) Λ) :=
  moduleUnboundedRawRefinementBaseChangeIso_naturality
    (Hom.Compactification.densify E).toCompactification E
    (Hom.Compactification.densifyι E) (Hom.Compactification.isPullback_densify E)
    (Hom.Compactification.densifyι_p E) b Λ N hN hΛ

end AlgebraicGeometry.Scheme.EtaleCohomology
