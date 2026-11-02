/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChangeCompatibility
public import Aglib.AlgebraicGeometry.Compactification.Refinements.CartesianBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawTransition

/-!
# Naturality of the original raw compactification base-change isomorphism

The actual arbitrary-model exchange square is specialized to the supplied raw
compactification refinements. The actual geometric refinement and
its supplied ambient pullback are retained throughout.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wC wD wX' wT wCR wDR

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

/-- Reuse the selected derived category on `pullback b C.p` for the raw base-change ambient
scheme of `C`. -/
local instance unboundedRawBaseChangeNaturalityCModel :
    HasDerivedCategory.{wCR}
    (ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wCR} (ModuleSheaf (pullback b C.p) Λ))
/-- Reuse the selected derived category on `pullback b D.p` for the raw base-change ambient
scheme of `D`. -/
local instance unboundedRawBaseChangeNaturalityDModel :
    HasDerivedCategory.{wDR}
    (ModuleSheaf (D.toCompactification.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wDR} (ModuleSheaf (pullback b D.p) Λ))

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- Original raw base change is natural in actual dense refinements, with the
literal raw pullback transition on the other side. -/
theorem moduleUnboundedRawCompactificationBaseChangeIso_naturality :
    Functor.whiskerRight
        (moduleUnboundedRawCompactificationTransition
          C.toCompactification D.toCompactification r.hom
          (Hom.DenseCompactification.isPullback_open r) r.base_fac Λ)
        (moduleUnboundedDerivedInverseImage Λ b) ≫
      (moduleUnboundedRawCompactificationBaseChangeIso C.toCompactification b Λ N hN hΛ).hom =
    (moduleUnboundedRawCompactificationBaseChangeIso D.toCompactification b Λ N hN hΛ).hom ≫
      Functor.whiskerLeft (moduleUnboundedDerivedInverseImage Λ (pullback.snd b f))
        (moduleUnboundedRawCompactificationTransition (C.toCompactification.baseChange b)
          (D.toCompactification.baseChange b) (Hom.DenseCompactification.baseChangeAmbientMap r b)
          (Hom.DenseCompactification.isPullback_baseChangeAmbientMap_open r b)
          (Hom.DenseCompactification.baseChangeAmbientMap_fst r b) Λ) := by
  have hc := moduleUnboundedCompactifiedBaseChangeMap_refinement_naturality
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
  exact hc

end AlgebraicGeometry.Scheme.EtaleCohomology
