/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.BaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.Densification

/-!
# Base change for a specified normalized compactification model

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

local instance : HasDerivedCategory.{wR}
    (ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ))

local instance : HasDerivedCategory.{wN}
    (ModuleSheaf (Hom.Compactification.densify (C.toCompactification.baseChange b)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN}
    (ModuleSheaf (Hom.DenseCompactification.baseChangeObj b C).Xbar Λ))

/-- The specified dense model commutes with arbitrary base change after the
actual schematic-image normalization of its raw pullback. -/
def moduleNormalizedCompactificationBaseChangeIso :
    moduleRawCompactificationFunctor C.toCompactification Λ ⋙
        moduleDerivedInverseImage Λ b ≅
      moduleDerivedInverseImageTorsion (pullback.snd b f) Λ ⋙
        moduleRawCompactificationFunctor
          (Hom.DenseCompactification.baseChangeObj b C).toCompactification Λ :=
  moduleRawCompactificationBaseChangeIso C.toCompactification b Λ ≪≫
    Functor.isoWhiskerLeft (moduleDerivedInverseImageTorsion (pullback.snd b f) Λ)
      (moduleCompactificationDensificationIso (C.toCompactification.baseChange b) Λ)

/-- Normalization retains precisely the original raw exchange followed by the
original closed-densification comparison. -/
theorem moduleNormalizedCompactificationBaseChangeIso_hom :
    (moduleNormalizedCompactificationBaseChangeIso C b Λ).hom =
      (moduleRawCompactificationBaseChangeIso C.toCompactification b Λ).hom ≫
        Functor.whiskerLeft (moduleDerivedInverseImageTorsion (pullback.snd b f) Λ)
          (moduleCompactificationDensificationMap (C.toCompactification.baseChange b) Λ) := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
