/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.CategoryTheory.NatTrans.CartesianSourceExchange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ExceptionalBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceIso
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.StructuralComparisons

/-!
# Canonical exceptional base change for a given Cartesian square

The given source is not relabelled as the library pullback. The actual universal
source isomorphism, its canonical exceptional source comparison, and the original
native inverse-image compositor transport the original literal-pullback exchange.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wL wT wX' wM wN wP wR
variable {X S X' T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ T)
  (g : T ⟶ S) (g' : X' ⟶ X) (sq : IsPullback g' f' f g)
  [QuasiCompact f] [QuasiCompact f']
  [Nonempty (Hom.DenseCompactification f)]

local instance unboundedCartesianLiteralNonempty :
    Nonempty (Hom.DenseCompactification (pullback.fst g f)) :=
  ⟨Hom.DenseCompactification.baseChangeObj g (moduleExceptionalSuppliedCompactification f)⟩

include sq in
omit [QuasiCompact f'] in
/-- Actual source transport of the normalized pullback supplies compactifiability. -/
theorem moduleUnboundedCartesianBaseChangeTargetNonempty : Nonempty
      (Hom.DenseCompactification f') :=
  moduleUnboundedSourceIsoTargetNonempty (pullback.fst g f) f' sq.flip.isoPullback
    sq.flip.isoPullback_hom_fst

variable (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wL} (ModuleSheaf (pullback g f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [literalModels : ∀ C : Hom.DenseCompactification (pullback.fst g f),
    HasDerivedCategory.{wN} (ModuleSheaf C.Xbar Λ)]
  [presentationModels : ∀ C : Hom.DenseCompactification f',
    HasDerivedCategory.{wP} (ModuleSheaf C.Xbar Λ)]

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The actual source projection equation precedes the original native compositor. -/
def moduleUnboundedCartesianBaseChangeSourceIso :
    moduleUnboundedDerivedInverseImage Λ g' ≅
      moduleUnboundedDerivedInverseImage Λ (pullback.snd g f) ⋙
        moduleUnboundedDerivedInverseImage Λ sq.flip.isoPullback.hom :=
  eqToIso (congrArg (fun a => moduleUnboundedDerivedInverseImage Λ a)
      sq.flip.isoPullback_hom_snd.symm) ≪≫
    moduleUnboundedDerivedInverseImageCompIso Λ (pullback.snd g f) sq.flip.isoPullback.hom

/-- The original literal model exchange and actual canonical source transport
compute the Cartesian comparison on any supplied three models. -/
def moduleUnboundedCompactificationCartesianBaseChangeIsoTo
    (C : Hom.DenseCompactification f)
    (D : Hom.DenseCompactification (pullback.fst g f)) (E : Hom.DenseCompactification f')
    [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
    [HasDerivedCategory.{wR} (ModuleSheaf (pullback g C.p) Λ)] :
    moduleUnboundedCompactificationFunctor f Λ C ⋙ moduleUnboundedDerivedInverseImage Λ g ≅
      moduleUnboundedDerivedInverseImage Λ g' ⋙ moduleUnboundedCompactificationFunctor f' Λ E :=
  cartesianSourceExchange (moduleUnboundedCompactificationBaseChangeIsoTo f g Λ N hN hΛ C D)
    (moduleUnboundedCompactificationSourceIsoTo (pullback.fst g f) f'
      sq.flip.isoPullback sq.flip.isoPullback_hom_fst Λ N hN hΛ D E)
    (moduleUnboundedCartesianBaseChangeSourceIso f f' g g' sq Λ)

section Chosen
variable [chosenSourceModel : HasDerivedCategory.{wM}
  (ModuleSheaf (moduleExceptionalSuppliedCompactification f).Xbar Λ)]
  [chosenRawModel : HasDerivedCategory.{wR}
    (ModuleSheaf (pullback g (moduleExceptionalSuppliedCompactification f).p) Λ)]

include f f' g g' sq in
/-- Original chosen exceptional exchange for the specified Cartesian presentation. -/
def moduleExceptionalDirectImageUnboundedCartesianBaseChangeIsoOfNonempty :
    (letI : Nonempty (Hom.DenseCompactification f') :=
       moduleUnboundedCartesianBaseChangeTargetNonempty f f' g g' sq
     moduleExceptionalDirectImageUnboundedOfNonempty f Λ
         (chosenMiddleModel := chosenSourceModel) ⋙ moduleUnboundedDerivedInverseImage Λ g ≅
       moduleUnboundedDerivedInverseImage Λ g' ⋙
         moduleExceptionalDirectImageUnboundedOfNonempty f' Λ
           (chosenMiddleModel := presentationModels
             (moduleExceptionalSuppliedCompactification f'))) := by
  letI : Nonempty (Hom.DenseCompactification f') :=
    moduleUnboundedCartesianBaseChangeTargetNonempty f f' g g' sq
  exact cartesianSourceExchange
    (moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty f g Λ N hN hΛ
      (chosenSourceModel := chosenSourceModel) (chosenRawModel := chosenRawModel))
    (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty (pullback.fst g f) f'
      sq.flip.isoPullback sq.flip.isoPullback_hom_fst Λ N hN hΛ
      (chosenSourceModel := literalModels
        (moduleExceptionalSuppliedCompactification (pullback.fst g f))))
    (moduleUnboundedCartesianBaseChangeSourceIso f f' g g' sq Λ)

include f f' g g' sq in
/-- The actual hom is the original literal exchange, original source comparison,
and original inverse source compositor, in that order. -/
theorem moduleExceptionalDirectImageUnboundedCartesianBaseChangeIsoOfNonempty_hom_app
    (K : DerivedCategory (ModuleSheaf X Λ)) :
    (letI : Nonempty (Hom.DenseCompactification f') :=
       moduleUnboundedCartesianBaseChangeTargetNonempty f f' g g' sq
     (moduleExceptionalDirectImageUnboundedCartesianBaseChangeIsoOfNonempty f f' g g' sq Λ N
         hN hΛ).hom.app K =
       (moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty f g Λ N hN hΛ).hom.app K ≫
         (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty (pullback.fst g f) f'
           sq.flip.isoPullback sq.flip.isoPullback_hom_fst Λ N hN hΛ).hom.app
           ((moduleUnboundedDerivedInverseImage Λ (pullback.snd g f)).obj K) ≫
         (moduleExceptionalDirectImageUnboundedOfNonempty f' Λ).map
           ((moduleUnboundedCartesianBaseChangeSourceIso f f' g g' sq Λ).inv.app K)) := by
  let : Nonempty (Hom.DenseCompactification f') :=
    moduleUnboundedCartesianBaseChangeTargetNonempty f f' g g' sq
  exact cartesianSourceExchange_hom_app _ _ _ K

end Chosen

variable
  [sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [rawModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wR} (ModuleSheaf (pullback g C.p) Λ)]


include f f' g g' sq in
/-- Canonicality for all actual source, literal intermediate, and presentation models. -/
theorem moduleExceptionalDirectImageUnboundedCartesianBaseChangeIsoOfNonempty_model
    (C : Hom.DenseCompactification f)
    (D : Hom.DenseCompactification (pullback.fst g f)) (E : Hom.DenseCompactification f') :
    (letI : Nonempty (Hom.DenseCompactification f') :=
       moduleUnboundedCartesianBaseChangeTargetNonempty f f' g g' sq
     Functor.isoWhiskerRight (moduleExceptionalDirectImageUnboundedOfNonemptyIso f Λ N hN hΛ C)
         (moduleUnboundedDerivedInverseImage Λ g) ≪≫
         moduleUnboundedCompactificationCartesianBaseChangeIsoTo f f' g g' sq Λ N hN hΛ C D E =
       moduleExceptionalDirectImageUnboundedCartesianBaseChangeIsoOfNonempty f f' g g' sq Λ N
         hN hΛ ≪≫
         Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ g')
           (moduleExceptionalDirectImageUnboundedOfNonemptyIso f' Λ N hN hΛ E)) := by
  let : Nonempty (Hom.DenseCompactification f') :=
    moduleUnboundedCartesianBaseChangeTargetNonempty f f' g g' sq
  exact cartesianSourceExchange_model
    (moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty f g Λ N hN hΛ)
    (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty (pullback.fst g f) f'
      sq.flip.isoPullback sq.flip.isoPullback_hom_fst Λ N hN hΛ)
    (moduleUnboundedCompactificationBaseChangeIsoTo f g Λ N hN hΛ C D)
    (moduleUnboundedCompactificationSourceIsoTo (pullback.fst g f) f'
      sq.flip.isoPullback sq.flip.isoPullback_hom_fst Λ N hN hΛ D E)
    (moduleUnboundedCartesianBaseChangeSourceIso f f' g g' sq Λ)
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso f Λ N hN hΛ C)
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso (pullback.fst g f) Λ N hN hΛ D)
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso f' Λ N hN hΛ E)
    (moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty_model f g Λ N hN hΛ C D)
    (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty_model (pullback.fst g f) f'
      sq.flip.isoPullback sq.flip.isoPullback_hom_fst Λ N hN hΛ D E)


end AlgebraicGeometry.Scheme.EtaleCohomology
