/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceIso
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawSourceToDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.MixedToDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SuppliedToDirectImage
public import Aglib.CategoryTheory.NatTrans.TargetComparisonWhiskering

/-! # The same canonical comparison under actual source isomorphism -/
@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wX' wS wM wN
variable {X X' S : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S)
  [QuasiCompact f] [QuasiCompact f'] (e : X' ≅ X) (he : e.hom ≫ f = f')
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hX' : HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [targetModels : ∀ D : Hom.DenseCompactification f',
    HasDerivedCategory.{wN} (ModuleSheaf D.Xbar Λ)]

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

omit [QuasiCompact f] in
/-- The actual model source isomorphism retains b with independent target models. -/
theorem moduleUnboundedCompactificationSourceIsoModel_toDirectImage
    (C : Hom.DenseCompactification f) :
    TargetComparisonEquation
      (moduleUnboundedCompactificationSourceIsoModel f f' e he Λ N hN hΛ C).hom
      (Functor.whiskerLeft (moduleUnboundedDerivedInverseImage Λ e.hom)
        (moduleUnboundedCompactificationToDirectImage f' Λ
          ((Hom.DenseCompactification.sourceIso f' e he).obj C)))
      (moduleUnboundedCompactificationToDirectImage f Λ C ≫
        moduleUnboundedDirectImageSourceTransport f f' e he Λ) := by
  let D := (Hom.DenseCompactification.sourceIso f' e he).obj C
  let hOld : HasDerivedCategory.{wM} (ModuleSheaf D.Xbar Λ) := sourceModels C
  let := @moduleUnboundedCompactificationMixedTransition_isIso X' S f' _ Λ _ hX' hS D D
    (𝟙 D) (targetModels D) hOld N hN hΛ
  let m := asIso (@moduleUnboundedCompactificationMixedTransition X' S f' _ Λ _ hX' hS D D
    (𝟙 D) (targetModels D) hOld)
  let bOld := @moduleUnboundedRawCompactificationToDirectImage X' S f' D.toCompactification
    Λ _ hX' hS hOld
  let : HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ) := sourceModels C
  exact targetComparison_iso_trans
    (moduleUnboundedRawCompactificationSourceIso e Λ f' he C.toCompactification)
    (Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ e.hom) m)
    _ (Functor.whiskerLeft (moduleUnboundedDerivedInverseImage Λ e.hom) bOld) _
    (moduleUnboundedRawCompactificationSourceIso_toDirectImage e f' he C.toCompactification Λ)
    (targetComparison_whiskerLeft (moduleUnboundedDerivedInverseImage Λ e.hom) m.hom
      (moduleUnboundedCompactificationToDirectImage f' Λ D) bOld
      (@moduleUnboundedCompactificationMixedTransition_toDirectImage X' S f' _ Λ _ hX' hS
        D D (𝟙 D) (targetModels D) hOld))

omit [QuasiCompact f] in
/-- Canonical comparison to any target model preserves the original source square. -/
theorem moduleUnboundedCompactificationSourceIsoTo_toDirectImage
    (C : Hom.DenseCompactification f) (D : Hom.DenseCompactification f') :
    TargetComparisonEquation
      (moduleUnboundedCompactificationSourceIsoTo f f' e he Λ N hN hΛ C D).hom
      (Functor.whiskerLeft (moduleUnboundedDerivedInverseImage Λ e.hom)
        (moduleUnboundedCompactificationToDirectImage f' Λ D))
      (moduleUnboundedCompactificationToDirectImage f Λ C ≫
        moduleUnboundedDirectImageSourceTransport f f' e he Λ) :=
  targetComparison_iso_trans
    (moduleUnboundedCompactificationSourceIsoModel f f' e he Λ N hN hΛ C)
    (Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ e.hom)
      (moduleUnboundedCompactificationComparison f' Λ N hN hΛ
        ((Hom.DenseCompactification.sourceIso f' e he).obj C) D))
    _ _ _ (moduleUnboundedCompactificationSourceIsoModel_toDirectImage f f' e he Λ N hN hΛ C)
    (targetComparison_whiskerLeft _ _ _ _
      (moduleUnboundedCompactificationToDirectImage_comparison f' Λ N hN hΛ
        ((Hom.DenseCompactification.sourceIso f' e he).obj C) D))

variable [Nonempty (Hom.DenseCompactification f)] [Nonempty (Hom.DenseCompactification f')]

omit [QuasiCompact f] in
/-- Actual chosen source transport commutes with the same canonical !→* map. -/
theorem moduleExceptionalToDirectImageUnbounded_sourceIso :
    TargetComparisonEquation
      (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty f f' e he Λ N hN hΛ).hom
      (Functor.whiskerLeft (moduleUnboundedDerivedInverseImage Λ e.hom)
        (moduleExceptionalToDirectImageUnboundedOfNonempty f' Λ))
      (moduleExceptionalToDirectImageUnboundedOfNonempty f Λ ≫
        moduleUnboundedDirectImageSourceTransport f f' e he Λ) :=
  moduleUnboundedCompactificationSourceIsoTo_toDirectImage f f' e he Λ N hN hΛ
    (moduleExceptionalSuppliedCompactification f) (moduleExceptionalSuppliedCompactification f')
end AlgebraicGeometry.Scheme.EtaleCohomology
