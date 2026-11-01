/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SuppliedDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChangeDiagram

/-!
# Canonical arbitrary base change for the actual unbounded exceptional functor

The component at the chosen source compactification is the original normalized
model exchange. Its target is transported by the canonical cofiltered
comparison, not by a fresh arbitrary isomorphism. Compatibility with every
source and target compactification proves independence of both choices.
Compactifiability after pullback comes from the actual normalized pullback;
no qcqs assumption is imposed on the new base. Pasting of successive base
changes is a separate result.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wM wX' wT wN wR

variable {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  [Nonempty (Hom.DenseCompactification f)] (b : T ⟶ S)

local instance unboundedBaseChangeSuppliedNonempty :
    Nonempty (Hom.DenseCompactification (pullback.fst b f)) :=
  ⟨Hom.DenseCompactification.baseChangeObj b (moduleExceptionalSuppliedCompactification f)⟩

variable (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [targetModels : ∀ C : Hom.DenseCompactification (pullback.fst b f),
    HasDerivedCategory.{wN} (ModuleSheaf C.Xbar Λ)]

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The original normalized exchange, canonically transported to any specified target model. -/
def moduleUnboundedCompactificationBaseChangeIsoTo
    (C : Hom.DenseCompactification f) (D : Hom.DenseCompactification (pullback.fst b f))
    [sourceModel : HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
    [rawModel : HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ)] :
    moduleUnboundedCompactificationFunctor f Λ C ⋙ moduleUnboundedDerivedInverseImage Λ b ≅
      moduleUnboundedDerivedInverseImage Λ (pullback.snd b f) ⋙
        moduleUnboundedCompactificationFunctor (pullback.fst b f) Λ D :=
  moduleUnboundedNormalizedCompactificationBaseChangeIso C b Λ N hN hΛ ≪≫
    Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ (pullback.snd b f))
      (moduleUnboundedCompactificationComparison (pullback.fst b f) Λ N hN hΛ
        (Hom.DenseCompactification.baseChangeObj b C) D)

section Chosen
variable [chosenSourceModel : HasDerivedCategory.{wM}
  (ModuleSheaf (moduleExceptionalSuppliedCompactification f).Xbar Λ)]
  [chosenRawModel : HasDerivedCategory.{wR}
    (ModuleSheaf (pullback b (moduleExceptionalSuppliedCompactification f).p) Λ)]

/-- Canonical exceptional base change on the full native unbounded derived categories. -/
def moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty :
    moduleExceptionalDirectImageUnboundedOfNonempty f Λ
        (chosenMiddleModel := chosenSourceModel) ⋙ moduleUnboundedDerivedInverseImage Λ b ≅
      moduleUnboundedDerivedInverseImage Λ (pullback.snd b f) ⋙
        moduleExceptionalDirectImageUnboundedOfNonempty (pullback.fst b f) Λ
          (chosenMiddleModel := targetModels
            (moduleExceptionalSuppliedCompactification (pullback.fst b f))) :=
  moduleUnboundedCompactificationBaseChangeIsoTo f b Λ N hN hΛ
    (moduleExceptionalSuppliedCompactification f)
    (moduleExceptionalSuppliedCompactification (pullback.fst b f))
    (sourceModel := chosenSourceModel) (rawModel := chosenRawModel)

end Chosen

variable
  [sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [rawModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ)]


/-- Transport through any source and target compactifications computes the same
chosen base-change map. This is actual comparison independence, not an isomorphism choice. -/
theorem moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty_model
    (C : Hom.DenseCompactification f) (D : Hom.DenseCompactification (pullback.fst b f)) :
    Functor.isoWhiskerRight (moduleExceptionalDirectImageUnboundedOfNonemptyIso f Λ N hN hΛ C)
        (moduleUnboundedDerivedInverseImage Λ b) ≪≫
      moduleUnboundedCompactificationBaseChangeIsoTo f b Λ N hN hΛ C D =
      moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty f b Λ N hN hΛ ≪≫
        Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ (pullback.snd b f))
          (moduleExceptionalDirectImageUnboundedOfNonemptyIso (pullback.fst b f) Λ N hN hΛ D) := by
  exact isoComparison_model_transport
    ((Functor.whiskeringLeft _ _ _).obj
      (moduleUnboundedDerivedInverseImage Λ (pullback.snd b f)))
    (moduleUnboundedNormalizedCompactificationBaseChangeIso
      (moduleExceptionalSuppliedCompactification f) b Λ N hN hΛ)
    (moduleUnboundedNormalizedCompactificationBaseChangeIso C b Λ N hN hΛ)
    (Functor.isoWhiskerRight
      (moduleUnboundedCompactificationComparison f Λ N hN hΛ
        (moduleExceptionalSuppliedCompactification f) C)
      (moduleUnboundedDerivedInverseImage Λ b))
    (moduleUnboundedCompactificationComparison (pullback.fst b f) Λ N hN hΛ
      (Hom.DenseCompactification.baseChangeObj b (moduleExceptionalSuppliedCompactification f))
      (Hom.DenseCompactification.baseChangeObj b C))
    (moduleUnboundedCompactificationComparison (pullback.fst b f) Λ N hN hΛ
      (Hom.DenseCompactification.baseChangeObj b C) D)
    (moduleUnboundedCompactificationComparison (pullback.fst b f) Λ N hN hΛ
      (Hom.DenseCompactification.baseChangeObj b (moduleExceptionalSuppliedCompactification f))
      (moduleExceptionalSuppliedCompactification (pullback.fst b f)))
    (moduleUnboundedCompactificationComparison (pullback.fst b f) Λ N hN hΛ
      (moduleExceptionalSuppliedCompactification (pullback.fst b f)) D)
    (moduleUnboundedCompactificationBaseChangeComparison f b Λ N hN hΛ
      (moduleExceptionalSuppliedCompactification f) C)
    ((moduleUnboundedCompactificationComparison_trans (pullback.fst b f) Λ N hN hΛ
      (Hom.DenseCompactification.baseChangeObj b (moduleExceptionalSuppliedCompactification f))
      (Hom.DenseCompactification.baseChangeObj b C) D).trans
      (moduleUnboundedCompactificationComparison_trans (pullback.fst b f) Λ N hN hΛ
        (Hom.DenseCompactification.baseChangeObj b (moduleExceptionalSuppliedCompactification f))
        (moduleExceptionalSuppliedCompactification (pullback.fst b f)) D).symm)

end AlgebraicGeometry.Scheme.EtaleCohomology
