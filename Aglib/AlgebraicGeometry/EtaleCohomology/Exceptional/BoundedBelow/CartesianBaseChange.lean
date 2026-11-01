/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.CartesianSourceExchange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.BaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.SourceIso
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.InverseImageTorsionCoherence

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

local instance cartesianLiteralNonempty :
    Nonempty (Hom.DenseCompactification (pullback.fst g f)) :=
  ⟨Hom.DenseCompactification.baseChangeObj g (moduleExceptionalSuppliedCompactification f)⟩

include sq in
omit [QuasiCompact f'] in
/-- Actual source transport of the normalized pullback supplies compactifiability. -/
theorem moduleCartesianBaseChangeTargetNonempty : Nonempty (Hom.DenseCompactification f') :=
  moduleSourceIsoTargetNonempty (pullback.fst g f) f' sq.flip.isoPullback
    sq.flip.isoPullback_hom_fst

variable [Nonempty (Hom.DenseCompactification f')]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wL} (ModuleSheaf (pullback g f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [literalModels : ∀ C : Hom.DenseCompactification (pullback.fst g f),
    HasDerivedCategory.{wN} (ModuleSheaf C.Xbar Λ)]
  [presentationModels : ∀ C : Hom.DenseCompactification f',
    HasDerivedCategory.{wP} (ModuleSheaf C.Xbar Λ)]
  [rawModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wR} (ModuleSheaf (pullback g C.p) Λ)]

/-- The actual source projection equation precedes the original native compositor. -/
def moduleCartesianBaseChangeSourceIso :
    moduleDerivedInverseImageTorsion g' Λ ≅
      moduleDerivedInverseImageTorsion (pullback.snd g f) Λ ⋙
        moduleDerivedInverseImageTorsion sq.flip.isoPullback.hom Λ :=
  eqToIso (congrArg (fun a => moduleDerivedInverseImageTorsion a Λ)
      sq.flip.isoPullback_hom_snd.symm) ≪≫
    moduleDerivedInverseImageTorsionCompIso Λ (pullback.snd g f) sq.flip.isoPullback.hom

/-- Original chosen exceptional exchange for the specified Cartesian presentation. -/
def moduleExceptionalDirectImagePlusCartesianBaseChangeIsoOfNonempty :
    moduleExceptionalDirectImagePlusOfNonempty f Λ ⋙ moduleDerivedInverseImage Λ g ≅
      moduleDerivedInverseImageTorsion g' Λ ⋙ moduleExceptionalDirectImagePlusOfNonempty f' Λ :=
  cartesianSourceExchange
    (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty f g Λ)
    (moduleExceptionalDirectImagePlusSourceIsoOfNonempty (pullback.fst g f) f'
      sq.flip.isoPullback sq.flip.isoPullback_hom_fst Λ)
    (moduleCartesianBaseChangeSourceIso f f' g g' sq Λ)

/-- The original literal model exchange and actual canonical source transport
compute the Cartesian comparison on any supplied three models. -/
def moduleCompactificationCartesianBaseChangeIsoTo
    (C : Hom.DenseCompactification f)
    (D : Hom.DenseCompactification (pullback.fst g f)) (E : Hom.DenseCompactification f') :
    moduleCompactificationFunctor f Λ C ⋙ moduleDerivedInverseImage Λ g ≅
      moduleDerivedInverseImageTorsion g' Λ ⋙ moduleCompactificationFunctor f' Λ E :=
  cartesianSourceExchange (moduleCompactificationBaseChangeIsoTo f g Λ C D)
    (moduleCompactificationSourceIsoTo (pullback.fst g f) f'
      sq.flip.isoPullback sq.flip.isoPullback_hom_fst Λ D E)
    (moduleCartesianBaseChangeSourceIso f f' g g' sq Λ)

/-- Canonicality for all actual source, literal intermediate, and presentation models. -/
theorem moduleExceptionalDirectImagePlusCartesianBaseChangeIsoOfNonempty_model
    (C : Hom.DenseCompactification f)
    (D : Hom.DenseCompactification (pullback.fst g f)) (E : Hom.DenseCompactification f') :
    Functor.isoWhiskerRight (moduleExceptionalDirectImagePlusOfNonemptyIso f Λ C)
        (moduleDerivedInverseImage Λ g) ≪≫
        moduleCompactificationCartesianBaseChangeIsoTo f f' g g' sq Λ C D E =
      moduleExceptionalDirectImagePlusCartesianBaseChangeIsoOfNonempty f f' g g' sq Λ ≪≫
        Functor.isoWhiskerLeft (moduleDerivedInverseImageTorsion g' Λ)
          (moduleExceptionalDirectImagePlusOfNonemptyIso f' Λ E) :=
  cartesianSourceExchange_model
    (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty f g Λ)
    (moduleExceptionalDirectImagePlusSourceIsoOfNonempty (pullback.fst g f) f'
      sq.flip.isoPullback sq.flip.isoPullback_hom_fst Λ)
    (moduleCompactificationBaseChangeIsoTo f g Λ C D)
    (moduleCompactificationSourceIsoTo (pullback.fst g f) f'
      sq.flip.isoPullback sq.flip.isoPullback_hom_fst Λ D E)
    (moduleCartesianBaseChangeSourceIso f f' g g' sq Λ)
    (moduleExceptionalDirectImagePlusOfNonemptyIso f Λ C)
    (moduleExceptionalDirectImagePlusOfNonemptyIso (pullback.fst g f) Λ D)
    (moduleExceptionalDirectImagePlusOfNonemptyIso f' Λ E)
    (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty_model f g Λ C D)
    (moduleExceptionalDirectImagePlusSourceIsoOfNonempty_model (pullback.fst g f) f'
      sq.flip.isoPullback sq.flip.isoPullback_hom_fst Λ D E)

/-- The actual hom is the original literal exchange, original source comparison,
and original inverse source compositor, in that order. -/
theorem moduleExceptionalDirectImagePlusCartesianBaseChangeIsoOfNonempty_hom_app
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    (moduleExceptionalDirectImagePlusCartesianBaseChangeIsoOfNonempty f f' g g' sq Λ).hom.app K =
      (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty f g Λ).hom.app K ≫
        (moduleExceptionalDirectImagePlusSourceIsoOfNonempty (pullback.fst g f) f'
          sq.flip.isoPullback sq.flip.isoPullback_hom_fst Λ).hom.app
          ((moduleDerivedInverseImageTorsion (pullback.snd g f) Λ).obj K) ≫
        (moduleExceptionalDirectImagePlusOfNonempty f' Λ).map
          ((moduleCartesianBaseChangeSourceIso f f' g g' sq Λ).inv.app K) :=
  cartesianSourceExchange_hom_app _ _ _ K

/-- Native torsion output retains this identical canonical Cartesian exchange. -/
def moduleExceptionalDirectImagePlusTorsionCartesianBaseChangeIsoOfNonempty :
    moduleExceptionalDirectImagePlusTorsionOfNonempty f Λ ⋙
        moduleDerivedInverseImageTorsion g Λ ≅
      moduleDerivedInverseImageTorsion g' Λ ⋙
        moduleExceptionalDirectImagePlusTorsionOfNonempty f' Λ :=
  (moduleTorsionCohomologyPlus T Λ).liftFunctorIso
    (moduleExceptionalDirectImagePlusOfNonempty f Λ ⋙ moduleDerivedInverseImage Λ g)
    (moduleDerivedInverseImageTorsion g' Λ ⋙ moduleExceptionalDirectImagePlusOfNonempty f' Λ)
    (fun K => ((moduleExceptionalDirectImagePlusTorsionOfNonempty f Λ ⋙
      moduleDerivedInverseImageTorsion g Λ).obj K).property)
    (fun K => ((moduleDerivedInverseImageTorsion g' Λ ⋙
      moduleExceptionalDirectImagePlusTorsionOfNonempty f' Λ).obj K).property)
    (moduleExceptionalDirectImagePlusCartesianBaseChangeIsoOfNonempty f f' g g' sq Λ)

/-- Restriction to native torsion output preserves the literal original component. -/
theorem moduleExceptionalDirectImagePlusTorsionCartesianBaseChangeIsoOfNonempty_hom_app
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    ((moduleExceptionalDirectImagePlusTorsionCartesianBaseChangeIsoOfNonempty
      f f' g g' sq Λ).hom.app K).hom =
      (moduleExceptionalDirectImagePlusCartesianBaseChangeIsoOfNonempty
        f f' g g' sq Λ).hom.app K := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
