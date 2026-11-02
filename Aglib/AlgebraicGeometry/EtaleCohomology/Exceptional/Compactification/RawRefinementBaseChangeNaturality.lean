/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.RawRefinementBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawBaseChangeNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.Densification

/-!
# Base-change naturality for arbitrary raw refinements

The actual ambient pullback lift retains the supplied refinement and both
projections. The original raw exchange commutes with the same original unit
transition even when the target compactification is not dense. Densification
is a specialization, not an assumption that density survives pullback.
-/

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

/-- Derived-category instance on module sheaves over `(C.baseChange b).Xbar`, using the instance on
`(pullback b C.p)`.
-/
local instance rawRefinementNaturalityCModel :
    HasDerivedCategory.{wCR} (ModuleSheaf (C.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wCR} (ModuleSheaf (pullback b C.p) Λ))
/-- Derived-category instance on module sheaves over `(D.baseChange b).Xbar`, using the instance on
`(pullback b D.p)`.
-/
local instance rawRefinementNaturalityDModel :
    HasDerivedCategory.{wDR} (ModuleSheaf (D.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wDR} (ModuleSheaf (pullback b D.p) Λ))

/-- The same original raw exchange is natural for any specified Cartesian open
refinement. No density, properness of the refinement, or new-base qcqs premise
is required for this equality of the original maps. -/
theorem moduleRawRefinementBaseChangeIso_naturality :
    Functor.whiskerRight (moduleRawCompactificationTransition C D h sq hp Λ)
        (moduleDerivedInverseImage Λ b) ≫
      (moduleRawCompactificationBaseChangeIso C b Λ).hom =
    (moduleRawCompactificationBaseChangeIso D b Λ).hom ≫
      Functor.whiskerLeft (moduleDerivedInverseImageTorsion (pullback.snd b f) Λ)
        (moduleRawCompactificationTransition (C.baseChange b) (D.baseChange b)
          (Hom.Compactification.refinementBaseChangeMap C D h hp b)
          (Hom.Compactification.isPullback_refinementBaseChangeMap_open C D h hp b sq)
          (Hom.Compactification.refinementBaseChangeMap_fst C D h hp b) Λ) := by
  have hc := moduleCompactifiedBaseChangeMap_refinement_naturality
    C.j D.j h sq (C.baseChange b).j (D.baseChange b).j
    (Hom.Compactification.refinementBaseChangeMap C D h hp b)
    (Hom.Compactification.isPullback_refinementBaseChangeMap_open C D h hp b sq)
    (pullback.snd b f) (pullback.snd b C.p) (pullback.snd b D.p)
    (isPullback_rawCompactificationOpen C b) (isPullback_rawCompactificationOpen D b)
    (Hom.Compactification.isPullback_refinementBaseChangeMap C D h hp b) Λ
    C.p D.p hp (pullback.fst b C.p) (pullback.fst b D.p)
    (Hom.Compactification.refinementBaseChangeMap_fst C D h hp b) b
    (IsPullback.of_hasPullback b C.p).flip (IsPullback.of_hasPullback b D.p).flip
  exact compositeExchange_restriction_naturality _ _
    (moduleDerivedInverseImageTorsionForgetIso (pullback.snd b f) Λ).symm _ _ hc

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

/-- Derived-category instance on module sheaves over `((Hom.Compactification.densify
E).toCompactification.baseChange b).Xbar`, using the instance on `(pullback b
(Hom.Compactification.densify E).p)`.
-/
local instance densificationPullbackDenseModel :
    HasDerivedCategory.{wCR}
      (ModuleSheaf ((Hom.Compactification.densify E).toCompactification.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wCR}
    (ModuleSheaf (pullback b (Hom.Compactification.densify E).p) Λ))
/-- Derived-category instance on module sheaves over `(E.baseChange b).Xbar`, using the instance on
`(pullback b E.p)`.
-/
local instance densificationPullbackRawModel :
    HasDerivedCategory.{wDR} (ModuleSheaf (E.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wDR} (ModuleSheaf (pullback b E.p) Λ))

/-- The original closed-densification comparison commutes with the next raw
base change, through the actual ambient pullback of its closed inclusion. -/
theorem moduleDensificationBaseChangeIso_naturality :
    Functor.whiskerRight (moduleCompactificationDensificationMap E Λ)
        (moduleDerivedInverseImage Λ b) ≫
      (moduleRawCompactificationBaseChangeIso
        (Hom.Compactification.densify E).toCompactification b Λ).hom =
    (moduleRawCompactificationBaseChangeIso E b Λ).hom ≫
      Functor.whiskerLeft (moduleDerivedInverseImageTorsion (pullback.snd b f) Λ)
        (moduleRawCompactificationTransition
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
  moduleRawRefinementBaseChangeIso_naturality
    (Hom.Compactification.densify E).toCompactification E
    (Hom.Compactification.densifyι E) (Hom.Compactification.isPullback_densify E)
    (Hom.Compactification.densifyι_p E) b Λ

end AlgebraicGeometry.Scheme.EtaleCohomology
