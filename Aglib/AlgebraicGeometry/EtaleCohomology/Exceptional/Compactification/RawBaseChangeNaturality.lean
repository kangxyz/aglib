/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.CompositeExchangeRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.BaseChangeCompatibility
public import Aglib.AlgebraicGeometry.Compactification.Refinements.CartesianBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawComparisonCoherence

/-!
# Naturality of the original raw compactification base-change isomorphism

The arbitrary-model exchange square is restricted to native torsion inputs by
an abstract source-inclusion calculation. The actual geometric refinement and
its supplied ambient pullback are retained throughout.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wC wD wX' wT wCR wDR

section Formula

variable {X S T : Scheme.{u}} {f : X ⟶ S}
  (C : Hom.Compactification f) (b : T ⟶ S)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wCR} (ModuleSheaf (pullback b C.p) Λ)]

/-- Derived-category instance on module sheaves over `(C.baseChange b).Xbar`, using the instance on
`(pullback b C.p)`.
-/
local instance rawBaseChangeFormulaModel :
    HasDerivedCategory.{wCR} (ModuleSheaf (C.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wCR} (ModuleSheaf (pullback b C.p) Λ))

/-- The whole original raw isomorphism is the abstract restriction of its
original compactified exchange; no concrete component expansion is needed. -/
theorem moduleRawCompactificationBaseChangeIso_hom_fac :
    (moduleRawCompactificationBaseChangeIso C b Λ).hom =
      compositeExchange
        (moduleCompactifiedBaseChangeMap C.j C.p (C.baseChange b).j
          (pullback.fst b C.p) (pullback.snd b f) (pullback.snd b C.p) b
          (isPullback_rawCompactificationOpen C b)
          (IsPullback.of_hasPullback b C.p).flip Λ)
        (moduleDerivedInverseImageTorsionForgetIso (pullback.snd b f) Λ).symm := rfl

end Formula

variable {X S T : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  {C D : Hom.DenseCompactification f} (r : C ⟶ D) (b : T ⟶ S)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wCR} (ModuleSheaf (pullback b C.p) Λ)]
  [HasDerivedCategory.{wDR} (ModuleSheaf (pullback b D.p) Λ)]

/-- Derived-category instance on module sheaves over `(C.toCompactification.baseChange b).Xbar`,
using the instance on `(pullback b C.p)`.
-/
local instance rawBaseChangeNaturalityCModel :
    HasDerivedCategory.{wCR}
    (ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wCR} (ModuleSheaf (pullback b C.p) Λ))
/-- Derived-category instance on module sheaves over `(D.toCompactification.baseChange b).Xbar`,
using the instance on `(pullback b D.p)`.
-/
local instance rawBaseChangeNaturalityDModel :
    HasDerivedCategory.{wDR}
    (ModuleSheaf (D.toCompactification.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wDR} (ModuleSheaf (pullback b D.p) Λ))

/-- Original raw base change is natural in actual dense refinements, with the
literal raw pullback transition on the other side. -/
theorem moduleRawCompactificationBaseChangeIso_naturality :
    Functor.whiskerRight
        (moduleRawCompactificationTransition C.toCompactification D.toCompactification r.hom
          (Hom.DenseCompactification.isPullback_open r) r.base_fac Λ)
        (moduleDerivedInverseImage Λ b) ≫
      (moduleRawCompactificationBaseChangeIso C.toCompactification b Λ).hom =
    (moduleRawCompactificationBaseChangeIso D.toCompactification b Λ).hom ≫
      Functor.whiskerLeft (moduleDerivedInverseImageTorsion (pullback.snd b f) Λ)
        (moduleRawCompactificationTransition (C.toCompactification.baseChange b)
          (D.toCompactification.baseChange b) (Hom.DenseCompactification.baseChangeAmbientMap r b)
          (Hom.DenseCompactification.isPullback_baseChangeAmbientMap_open r b)
          (Hom.DenseCompactification.baseChangeAmbientMap_fst r b) Λ) := by
  have hc := moduleCompactifiedBaseChangeMap_refinement_naturality
    C.j D.j r.hom (Hom.DenseCompactification.isPullback_open r)
    (C.toCompactification.baseChange b).j (D.toCompactification.baseChange b).j
    (Hom.DenseCompactification.baseChangeAmbientMap r b)
    (Hom.DenseCompactification.isPullback_baseChangeAmbientMap_open r b)
    (pullback.snd b f) (pullback.snd b C.p) (pullback.snd b D.p)
    (isPullback_rawCompactificationOpen C.toCompactification b)
    (isPullback_rawCompactificationOpen D.toCompactification b)
    (Hom.DenseCompactification.isPullback_baseChangeAmbientMap r b) Λ
    C.p D.p r.base_fac (pullback.fst b C.p) (pullback.fst b D.p)
    (Hom.DenseCompactification.baseChangeAmbientMap_fst r b) b
    (IsPullback.of_hasPullback b C.p).flip (IsPullback.of_hasPullback b D.p).flip
  exact compositeExchange_restriction_naturality _ _
    (moduleDerivedInverseImageTorsionForgetIso (pullback.snd b f) Λ).symm _ _ hc

end AlgebraicGeometry.Scheme.EtaleCohomology
