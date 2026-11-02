/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.NormalizedExchangeNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.NormalizedBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawBaseChangeNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.DensificationNaturality

/-!
# Naturality of normalized model base change

The original raw-exchange naturality square is pasted with the original
closed-densification square. This concerns the specified normalized models;
transport to a chosen exceptional functor and its coherence remain separate.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wC wD wX' wT wCR wDR wCN wDN

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
  [HasDerivedCategory.{wCN}
    (ModuleSheaf (Hom.DenseCompactification.baseChangeObj b C).Xbar Λ)]
  [HasDerivedCategory.{wDN}
    (ModuleSheaf (Hom.DenseCompactification.baseChangeObj b D).Xbar Λ)]

/-- Derived-category instance on module sheaves over `(C.toCompactification.baseChange b).Xbar`,
using the instance on `(pullback b C.p)`.
-/
local instance normalizedNaturalityCRawModel :
    HasDerivedCategory.{wCR}
    (ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wCR} (ModuleSheaf (pullback b C.p) Λ))
/-- Derived-category instance on module sheaves over `(D.toCompactification.baseChange b).Xbar`,
using the instance on `(pullback b D.p)`.
-/
local instance normalizedNaturalityDRawModel :
    HasDerivedCategory.{wDR}
    (ModuleSheaf (D.toCompactification.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wDR} (ModuleSheaf (pullback b D.p) Λ))
/-- Derived-category instance on module sheaves over `(Hom.Compactification.densify
(C.toCompactification.baseChange b)).Xbar`, using the instance on
`(Hom.DenseCompactification.baseChangeObj b C).Xbar`.
-/
local instance normalizedNaturalityCDenseModel :
    HasDerivedCategory.{wCN}
    (ModuleSheaf (Hom.Compactification.densify (C.toCompactification.baseChange b)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wCN}
    (ModuleSheaf (Hom.DenseCompactification.baseChangeObj b C).Xbar Λ))
/-- Derived-category instance on module sheaves over `(Hom.Compactification.densify
(D.toCompactification.baseChange b)).Xbar`, using the instance on
`(Hom.DenseCompactification.baseChangeObj b D).Xbar`.
-/
local instance normalizedNaturalityDDenseModel :
    HasDerivedCategory.{wDN}
    (ModuleSheaf (Hom.Compactification.densify (D.toCompactification.baseChange b)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wDN}
    (ModuleSheaf (Hom.DenseCompactification.baseChangeObj b D).Xbar Λ))

/-- The original normalized base-change model isomorphisms intertwine the
original refinement transitions and the actual normalized pullback functor. -/
theorem moduleNormalizedCompactificationBaseChangeIso_naturality :
    ExchangeNaturalityEquation
      (moduleRawCompactificationTransition C.toCompactification D.toCompactification r.hom
        (Hom.DenseCompactification.isPullback_open r) r.base_fac Λ)
      (moduleNormalizedCompactificationBaseChangeIso C b Λ).hom
      (moduleNormalizedCompactificationBaseChangeIso D b Λ).hom
      (moduleRawCompactificationTransition
        (Hom.DenseCompactification.baseChangeObj b C).toCompactification
        (Hom.DenseCompactification.baseChangeObj b D).toCompactification
        ((Hom.DenseCompactification.baseChange b).map r).hom
        (Hom.DenseCompactification.isPullback_open
          ((Hom.DenseCompactification.baseChange b).map r))
        ((Hom.DenseCompactification.baseChange b).map r).base_fac Λ) := by
  have hd := moduleCompactificationDensificationMap_naturality
    (C.toCompactification.baseChange b) (D.toCompactification.baseChange b)
    (Hom.DenseCompactification.baseChangeAmbientMap r b)
    (Hom.DenseCompactification.baseChange_j_ambientMap r b)
    (Hom.DenseCompactification.isPullback_baseChangeAmbientMap_open r b)
    (Hom.DenseCompactification.baseChangeAmbientMap_fst r b) Λ
  exact normalizedExchangeNaturality _ _ _ _ _ _ _ _ _
    (moduleRawCompactificationBaseChangeIso_naturality r b Λ) hd
    (moduleNormalizedCompactificationBaseChangeIso_hom C b Λ)
    (moduleNormalizedCompactificationBaseChangeIso_hom D b Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
