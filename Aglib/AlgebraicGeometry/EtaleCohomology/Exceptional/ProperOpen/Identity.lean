/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.ProperOpen.Mate
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.OpenBaseChangeIdentity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleRefinementComposition
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.PullbackCoherence
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.IdentityNormalization

/-! # Identity normalization of the original proper/open mixed mate

The ordinary Cartesian identity is transported by the native exact-derived
comparison. Actual adjunction conjugacy then gives the original mixed-mate
identity, without replacing any unit, counit or identity comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wU wX

variable (Λ : Type (u + 1)) [Ring Λ]
  {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
  (h : IsPullback (𝟙 U) j j (𝟙 X))
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

/-- The original derived Cartesian open comparison has its native identity value. -/
theorem moduleDerivedOpenComparison_identity
    (K : DerivedCategory.Plus (ModuleSheaf U Λ)) :
    IdentitySquareEquation
      (TwoSquare.mk _ _ _ _
        (moduleDerivedLowerShriekCartesianBaseChangeIso (𝟙 U) j j (𝟙 X) h Λ).hom)
      (moduleDerivedInverseImageIdIso Λ U) (moduleDerivedInverseImageIdIso Λ X) K := by
  have hn := moduleDerivedLowerShriekCartesianBaseChangeIso_identity_source j j (𝟙 X) h Λ
  have hi := Functor.rightDerivedFunctorPlusPullbackIso_id
    (moduleLowerShriek j Λ) (moduleInverseImage (𝟙 X) Λ)
    (moduleLowerShriekCartesianIdentityIso j j (𝟙 X) h Λ)
    (moduleInverseImageIdIso Λ X)
    (moduleLowerShriekCartesianIdentityIso_id j h Λ)
  have he := congrArg (fun e => e.hom.app K) (hn.trans hi)
  simpa only [IdentitySquareEquation, moduleDerivedInverseImageIdIso,
    TwoSquare.mk, TwoSquare.natTrans, Functor.comp_obj, Functor.id_obj,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app,
    Category.comp_id] using he.symm

/-- Native identity normalization of the actual mixed mate, in the original
adjunction-mate predicate. -/
theorem moduleProperOpenMate_identity_mate
    (K : DerivedCategory.Plus (ModuleSheaf U Λ)) :
    IdentityMateEquation
      (TwoSquare.mk _ _ _ _
        (moduleDerivedLowerShriekCartesianBaseChangeIso (𝟙 U) j j (𝟙 X) h Λ).hom)
      (moduleDerivedDirectImageIdIso Λ U) (moduleDerivedDirectImageIdIso Λ X)
      (moduleDerivedAdjunction Λ (𝟙 U)) (moduleDerivedAdjunction Λ (𝟙 X)) K :=
  identityMateEquation
    (TwoSquare.mk _ _ _ _
      (moduleDerivedLowerShriekCartesianBaseChangeIso (𝟙 U) j j (𝟙 X) h Λ).hom)
    (moduleDerivedInverseImageIdIso Λ U) (moduleDerivedInverseImageIdIso Λ X)
    (moduleDerivedDirectImageIdIso Λ U) (moduleDerivedDirectImageIdIso Λ X)
    (moduleDerivedAdjunction Λ (𝟙 U)) (moduleDerivedAdjunction Λ (𝟙 X))
    (conjugateEquiv_moduleDerivedInverseImageIdIso_hom Λ U)
    (conjugateEquiv_moduleDerivedInverseImageIdIso_hom Λ X)
    (moduleDerivedOpenComparison_identity Λ j h) K

/-- The actual proper/open mate at identity proper maps is normalized by the
original direct-image identity comparisons. -/
theorem moduleProperOpenMate_identity
    (K : DerivedCategory.Plus (ModuleSheaf U Λ)) :
    (moduleDerivedLowerShriek j Λ).map ((moduleDerivedDirectImageIdIso Λ U).hom.app K) =
      (moduleProperOpenMate Λ j j (𝟙 U) (𝟙 X) h).app K ≫
        (moduleDerivedDirectImageIdIso Λ X).hom.app
          ((moduleDerivedLowerShriek j Λ).obj K) :=
  moduleProperOpenMate_identity_mate Λ j h K

end AlgebraicGeometry.Scheme.EtaleCohomology
