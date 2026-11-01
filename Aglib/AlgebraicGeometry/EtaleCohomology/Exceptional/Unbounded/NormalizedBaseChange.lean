/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.BaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.Densification

/-!
# Actual unbounded base change for a normalized compactification

The actual raw exchange is followed by the original closed-densification
comparison. This is a model-level isomorphism only: compatibility with refinement
transitions, independence of a chosen compactification and base-change coherence
are separate statements. No schematic density is presumed to survive pullback.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wC wX' wT wR wN

variable {X S T : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (C : Hom.DenseCompactification f) (b : T ⟶ S)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ)]
  [HasDerivedCategory.{wN} (ModuleSheaf (Hom.DenseCompactification.baseChangeObj b C).Xbar Λ)]

/-- Reuse the selected derived category on `pullback b C.p` for the raw base-change ambient
scheme. -/
local instance unboundedNormalizedRawModel : HasDerivedCategory.{wR}
    (ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ))

/-- Reuse the selected derived category on the dense base-change ambient scheme for the
densified raw base change. -/
local instance unboundedNormalizedDenseModel : HasDerivedCategory.{wN}
    (ModuleSheaf (Hom.Compactification.densify (C.toCompactification.baseChange b)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN}
    (ModuleSheaf (Hom.DenseCompactification.baseChangeObj b C).Xbar Λ))

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The specified dense model commutes with arbitrary base change after the
actual schematic-image normalization of its raw pullback. -/
def moduleUnboundedNormalizedCompactificationBaseChangeIso :
    moduleUnboundedRawCompactificationFunctor C.toCompactification Λ ⋙
        moduleUnboundedDerivedInverseImage Λ b ≅
      moduleUnboundedDerivedInverseImage Λ (pullback.snd b f) ⋙
        moduleUnboundedRawCompactificationFunctor
          (Hom.DenseCompactification.baseChangeObj b C).toCompactification Λ :=
  moduleUnboundedRawCompactificationBaseChangeIso C.toCompactification b Λ N hN hΛ ≪≫
    Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ (pullback.snd b f))
      (moduleUnboundedCompactificationDensificationIso
        (C.toCompactification.baseChange b) Λ N hN hΛ)

/-- Normalization retains precisely the original raw exchange followed by the
original closed-densification comparison. -/
theorem moduleUnboundedNormalizedCompactificationBaseChangeIso_hom :
    (moduleUnboundedNormalizedCompactificationBaseChangeIso C b Λ N hN hΛ).hom =
      (moduleUnboundedRawCompactificationBaseChangeIso C.toCompactification b Λ N hN hΛ).hom ≫
        Functor.whiskerLeft (moduleUnboundedDerivedInverseImage Λ (pullback.snd b f))
          (moduleUnboundedCompactificationDensificationMap
            (C.toCompactification.baseChange b) Λ) := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
