/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.NormalizedExchangeNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.NormalizedBaseChange
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawBaseChangeNaturality
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.DensificationNaturality

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

/-- Reuse the selected derived category on `pullback b C.p` for the raw base-change ambient
scheme of `C`. -/
local instance unboundedNormalizedNaturalityCRawModel :
    HasDerivedCategory.{wCR}
    (ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wCR} (ModuleSheaf (pullback b C.p) Λ))
/-- Reuse the selected derived category on `pullback b D.p` for the raw base-change ambient
scheme of `D`. -/
local instance unboundedNormalizedNaturalityDRawModel :
    HasDerivedCategory.{wDR}
    (ModuleSheaf (D.toCompactification.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wDR} (ModuleSheaf (pullback b D.p) Λ))
/-- Reuse the selected derived category on the dense base-change ambient scheme of `C` for its
densified raw base change. -/
local instance unboundedNormalizedNaturalityCDenseModel :
    HasDerivedCategory.{wCN}
    (ModuleSheaf (Hom.Compactification.densify (C.toCompactification.baseChange b)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wCN}
    (ModuleSheaf (Hom.DenseCompactification.baseChangeObj b C).Xbar Λ))
/-- Reuse the selected derived category on the dense base-change ambient scheme of `D` for its
densified raw base change. -/
local instance unboundedNormalizedNaturalityDDenseModel :
    HasDerivedCategory.{wDN}
    (ModuleSheaf (Hom.Compactification.densify (D.toCompactification.baseChange b)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wDN}
    (ModuleSheaf (Hom.DenseCompactification.baseChangeObj b D).Xbar Λ))

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The original normalized base-change model isomorphisms intertwine the
original refinement transitions and the actual normalized pullback functor. -/
theorem moduleUnboundedNormalizedCompactificationBaseChangeIso_naturality :
    ExchangeNaturalityEquation
      (moduleUnboundedRawCompactificationTransition C.toCompactification D.toCompactification r.hom
        (Hom.DenseCompactification.isPullback_open r) r.base_fac Λ)
      (moduleUnboundedNormalizedCompactificationBaseChangeIso C b Λ N hN hΛ).hom
      (moduleUnboundedNormalizedCompactificationBaseChangeIso D b Λ N hN hΛ).hom
      (moduleUnboundedRawCompactificationTransition
        (Hom.DenseCompactification.baseChangeObj b C).toCompactification
        (Hom.DenseCompactification.baseChangeObj b D).toCompactification
        ((Hom.DenseCompactification.baseChange b).map r).hom
        (Hom.DenseCompactification.isPullback_open
          ((Hom.DenseCompactification.baseChange b).map r))
        ((Hom.DenseCompactification.baseChange b).map r).base_fac Λ) := by
  have hd := moduleUnboundedCompactificationDensificationMap_naturality
    (C.toCompactification.baseChange b) (D.toCompactification.baseChange b)
    (Hom.DenseCompactification.baseChangeAmbientMap r b)
    (Hom.DenseCompactification.baseChange_j_ambientMap r b)
    (Hom.DenseCompactification.isPullback_baseChangeAmbientMap_open r b)
    (Hom.DenseCompactification.baseChangeAmbientMap_fst r b) Λ
  exact normalizedExchangeNaturality _ _ _ _ _ _ _ _ _
    (moduleUnboundedRawCompactificationBaseChangeIso_naturality r b Λ N hN hΛ) hd
    (moduleUnboundedNormalizedCompactificationBaseChangeIso_hom C b Λ N hN hΛ)
    (moduleUnboundedNormalizedCompactificationBaseChangeIso_hom D b Λ N hN hΛ)

end AlgebraicGeometry.Scheme.EtaleCohomology
