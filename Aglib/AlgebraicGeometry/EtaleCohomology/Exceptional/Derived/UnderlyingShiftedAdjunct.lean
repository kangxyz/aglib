/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Shift
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.UnderlyingAdjunction
public import Aglib.CategoryTheory.Adjunction.ShiftedHom

/-! The original shifted module adjunct under scalar forgetting. -/

open CategoryTheory CategoryTheory.Functor

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wMX wMS wAX wAS

attribute [local instance] hasSheafifyLarge hasSheafifyModules

variable (Λ : Type (u + 1)) [Ring Λ] {X S : Scheme.{u}} (f : X ⟶ S)
  [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]

/-- The original scalar-forgetting direct-image comparison retains the installed shifts. -/
theorem moduleDerivedDirectImageUnderlyingIso_commShift :
    NatTrans.CommShift (moduleDerivedDirectImageUnderlyingIso Λ f).hom ℤ := by
  rw [moduleDerivedDirectImageUnderlyingIso_eq_original]
  let F := moduleDirectImage f Λ
  let G := SheafOfModules.toSheaf (constantRing S Λ)
  let U := SheafOfModules.toSheaf (constantRing X Λ)
  let V := directImage f
  let e := Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology F G
  let i := (F ⋙ G).rightDerivedFunctorPlusIso (moduleDirectImageUnderlyingIso f Λ)
  let j := Functor.rightDerivedFunctorPlusCompIsoOfAcyclic U V
    (fun I _ n => higherDirectImage_moduleInjective_isZero f Λ I n)
  let : NatTrans.CommShift e.hom ℤ :=
    Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology_commShift F G
  let : NatTrans.CommShift i.hom ℤ :=
    Functor.rightDerivedFunctorPlusIso_commShift (F ⋙ G) (moduleDirectImageUnderlyingIso f Λ)
  let : NatTrans.CommShift j.hom ℤ := by
    change NatTrans.CommShift (Functor.rightDerivedFunctorPlusCompComparison U V) ℤ
    infer_instance
  change NatTrans.CommShift (e.inv ≫ i.hom ≫ j.hom) ℤ
  infer_instance

/-- The original shifted adjunct commutes with the original scalar-forgetting mate. -/
abbrev moduleDerivedAdjunctionShiftedUnderlyingValue
    (q : ℤ)
    {I : DerivedCategory.Plus (ModuleSheaf S Λ)}
    {J : DerivedCategory.Plus (ModuleSheaf X Λ)}
    (x : ShiftedHom ((moduleDerivedInverseImage Λ f).obj I) J q) :=
  let d := (moduleDerivedDirectImageUnderlyingIso Λ f).hom
  let s := TwoSquare.mk _ _ _ _ (moduleDerivedInverseImageUnderlyingIso Λ f).inv
  letI : NatTrans.CommShift d ℤ := moduleDerivedDirectImageUnderlyingIso_commShift Λ f
  shiftedHomEquiv_of_mate (moduleDerivedAdjunction Λ f) (derivedImageAdjunction f)
    s d (mate_moduleDerivedInverseImageUnderlyingIso_inv Λ f) I J q x

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
