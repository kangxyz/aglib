/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Underlying
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.NativeAdjunctionUnderlying
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.OriginalUnitUniqueness
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.PullbackCoherence
public import
Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.CoherenceRawNormalization

/-!
# The original module-derived adjunction under scalar forgetting

The fixed inverse-image comparison and the acyclicity-based direct-image comparison
are mates under the original derived adjunctions. Their identification uses the
original complex-unit equations, cancelling only exact scalar-forgetting units.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wMX wMS wAX wAS

attribute [local instance] hasSheafifyLarge

variable (Λ : Type (u + 1)) [Ring Λ] {X S : Scheme.{u}} (f : X ⟶ S)
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]

/-- The inverse scalar comparison retains the original exact complex square. -/
theorem moduleDerivedInverseImageUnderlyingIso_exactComparison
    (K : CochainComplex.Plus (ModuleSheaf S Λ)) :
    ExactComparisonSquareEquation (moduleInverseImage f Λ)
      (SheafOfModules.toSheaf (constantRing X Λ))
      (SheafOfModules.toSheaf (constantRing S Λ)) (inverseImage f)
      (TwoSquare.mk _ _ _ _ (moduleInverseImageUnderlyingIso Λ f).inv)
      (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageUnderlyingIso Λ f).inv) K := by
  let : Limits.PreservesFiniteLimits
      (SheafOfModules.toSheaf (constantRing S Λ)) :=
    (SheafOfModules.toSheaf (constantRing S Λ)).preservesFiniteLimits_of_preservesHomology
  let : Limits.PreservesFiniteColimits
      (SheafOfModules.toSheaf (constantRing S Λ)) :=
    (SheafOfModules.toSheaf (constantRing S Λ)).preservesFiniteColimits_of_preservesHomology
  let : Limits.PreservesFiniteLimits
      (SheafOfModules.toSheaf (constantRing X Λ)) :=
    (SheafOfModules.toSheaf (constantRing X Λ)).preservesFiniteLimits_of_preservesHomology
  let : Limits.PreservesFiniteColimits
      (SheafOfModules.toSheaf (constantRing X Λ)) :=
    (SheafOfModules.toSheaf (constantRing X Λ)).preservesFiniteColimits_of_preservesHomology
  let : Limits.PreservesFiniteLimits (moduleInverseImage f Λ) :=
    (moduleInverseImage f Λ).preservesFiniteLimits_of_preservesHomology
  let : Limits.PreservesFiniteColimits (moduleInverseImage f Λ) :=
    (moduleInverseImage f Λ).preservesFiniteColimits_of_preservesHomology
  let : Limits.PreservesFiniteLimits (inverseImage f) :=
    (inverseImage f).preservesFiniteLimits_of_preservesHomology
  let : Limits.PreservesFiniteColimits (inverseImage f) :=
    (inverseImage f).preservesFiniteColimits_of_preservesHomology
  have h := exactComparisonSquareEquation (moduleInverseImage f Λ)
    (SheafOfModules.toSheaf (constantRing X Λ))
    (SheafOfModules.toSheaf (constantRing S Λ)) (inverseImage f)
    (SheafOfModules.toSheaf (constantRing S Λ) ⋙ inverseImage f)
    (moduleInverseImage f Λ ⋙ SheafOfModules.toSheaf (constantRing X Λ))
    (Iso.refl _) (Iso.refl _) (moduleInverseImageUnderlyingIso Λ f).symm K
  simpa only [moduleDerivedInverseImageUnderlyingIso_eq_original,
    rightDerivedFunctorPlusIso_refl, rightDerivedFunctorPlusIso_symm,
    Iso.refl_symm, Iso.refl_trans, Iso.trans_refl, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Category.assoc] using h

/-- The fixed direct-image comparison satisfies the normalized original-unit equation. -/
theorem moduleDerivedDirectImageUnderlyingIso_originalUnit
    (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    (moduleDerivedUnderlying Λ S).map
        ((moduleDirectImage f Λ).rightDerivedFunctorPlusUnit.app K) ≫
      (moduleDerivedDirectImageUnderlyingIso Λ f).hom.app (DerivedCategory.Plus.Q.obj K) ≫
      (derivedDirectImage f).map
        ((SheafOfModules.toSheaf (constantRing X Λ)).rightDerivedFunctorPlusExactComparison.hom.app
          K) =
    (SheafOfModules.toSheaf (constantRing S Λ)).rightDerivedFunctorPlusExactComparison.hom.app
        ((moduleDirectImage f Λ).mapCochainComplexPlus.obj K) ≫
      DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (moduleDirectImageUnderlyingIso f Λ)).hom.app K) ≫
      (directImage f).rightDerivedFunctorPlusUnit.app
        ((SheafOfModules.toSheaf (constantRing X Λ)).mapCochainComplexPlus.obj K) := by
  let G := SheafOfModules.toSheaf (constantRing S Λ)
  let H := SheafOfModules.toSheaf (constantRing X Λ)
  refine exchangeCoherence_rotate_start
    (G.rightDerivedFunctorPlusUnit.app ((moduleDirectImage f Λ).mapCochainComplexPlus.obj K))
    (G.rightDerivedFunctorPlusExactComparison.hom.app
      ((moduleDirectImage f Λ).mapCochainComplexPlus.obj K))
    (G.rightDerivedFunctorPlus.map ((moduleDirectImage f Λ).rightDerivedFunctorPlusUnit.app K))
    ((moduleDerivedDirectImageUnderlyingIso Λ f).hom.app (DerivedCategory.Plus.Q.obj K))
    (DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (moduleDirectImageUnderlyingIso f Λ)).hom.app K) ≫
      (directImage f).rightDerivedFunctorPlusUnit.app (H.mapCochainComplexPlus.obj K))
    ((derivedDirectImage f).map (H.rightDerivedFunctorPlusUnit.app K))
    ((derivedDirectImage f).map (H.rightDerivedFunctorPlusExactComparison.hom.app K))
    ?_ ?_ ?_
  · exact G.rightDerivedFunctorPlusExactComparison.hom_inv_id_app
      ((moduleDirectImage f Λ).mapCochainComplexPlus.obj K)
  · exact ((derivedDirectImage f).mapIso
      (H.rightDerivedFunctorPlusExactComparison.app K)).inv_hom_id
  · simpa only [rightDerivedFunctorPlusCompUnit_app, Category.assoc] using
      moduleDerivedDirectImageUnderlyingIso_unit Λ f K

/-- The original derived direct-image comparison is the mate of the fixed inverse
scalar comparison, rather than a separately chosen isomorphism. -/
theorem mate_moduleDerivedInverseImageUnderlyingIso_inv :
    (mateEquiv (moduleDerivedAdjunction Λ f) (derivedImageAdjunction f)
      (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageUnderlyingIso Λ f).inv)).natTrans =
      (moduleDerivedDirectImageUnderlyingIso Λ f).hom := by
  let α := TwoSquare.mk _ _ _ _ (moduleInverseImageUnderlyingIso Λ f).inv
  have hα : (mateEquiv (moduleInverseImageAdjunction f Λ)
      (inverseImageAdjunction f) α).natTrans =
      (moduleDirectImageUnderlyingIso f Λ).hom :=
    mate_moduleInverseImageUnderlyingIso_inv (Λ := Λ) (f := f)
  apply derivedMate_eq_of_originalUnit (moduleInverseImageAdjunction f Λ)
    (inverseImageAdjunction f) α
    (TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageUnderlyingIso Λ f).inv)
    (moduleDerivedInverseImageUnderlyingIso_exactComparison Λ f)
  intro K
  have hm : ((mateEquiv (moduleInverseImageAdjunction f Λ)
        (inverseImageAdjunction f) α).mapCochainComplexPlus).natTrans.app K =
      (NatIso.mapCochainComplexPlus (moduleDirectImageUnderlyingIso f Λ)).hom.app K := by
    apply ObjectProperty.hom_ext
    apply HomologicalComplex.hom_ext
    intro n
    change (𝟙 _ ≫ (mateEquiv (moduleInverseImageAdjunction f Λ)
        (inverseImageAdjunction f) α).natTrans.app (K.obj.X n) ≫ 𝟙 _) =
      (moduleDirectImageUnderlyingIso f Λ).hom.app (K.obj.X n)
    simpa only [Category.id_comp, Category.comp_id] using congr_app hα (K.obj.X n)
  change _ = _ ≫ DerivedCategory.Plus.Q.map
    (((mateEquiv (moduleInverseImageAdjunction f Λ)
      (inverseImageAdjunction f) α).mapCochainComplexPlus).natTrans.app K) ≫ _
  rw [hm]
  exact moduleDerivedDirectImageUnderlyingIso_originalUnit Λ f K

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
