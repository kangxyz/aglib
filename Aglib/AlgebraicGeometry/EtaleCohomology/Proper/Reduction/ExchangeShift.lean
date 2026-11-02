/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChange
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Shift

/-!
# Native shift compatibility of the original derived exchange

The lower derived-adjunction owner proves the general installed-unit argument.
The geometry here supplies only the original inverse-image composition and
scheme-map equality comparison, then takes the same native adjunction mate.
The old public generic names remain proof delegations for existing callers.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

section Derived

universe uA vA dA uB vB dB

variable {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{dA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [EnoughInjectives B]
  [HasDerivedCategory.{dB} B]
  {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive] [L.PreservesHomology]

/-- The actual original bounded-below derived adjunction is compatible with
the installed shifts, as forced by its native unit factorization. -/
theorem derivedAdjunction_commShift (adj : L ⊣ R) :
    adj.rightDerivedFunctorPlus.CommShift ℤ :=
  CategoryTheory.Adjunction.rightDerivedFunctorPlus_commShift adj

end Derived

section Mate

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] [HasShift F ℤ]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  {G : C ⥤ E} {H : D ⥤ F}
  [L₁.CommShift ℤ] [R₁.CommShift ℤ] [L₂.CommShift ℤ] [R₂.CommShift ℤ]
  [G.CommShift ℤ] [H.CommShift ℤ]

/-- Taking the original adjunction mate retains native shift compatibility. -/
theorem mate_commShift (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    [a₁.CommShift ℤ] [a₂.CommShift ℤ]
    (α : TwoSquare G L₁ L₂ H) [NatTrans.CommShift α.natTrans ℤ] :
    NatTrans.CommShift (mateEquiv a₁ a₂ α).natTrans ℤ :=
  CategoryTheory.mateEquiv_commShift a₁ a₂ α

end Mate

universe u dX dS dX' dS'

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

private theorem inverseImageComp_commShift
    {Y Z W : Scheme.{u}}
    [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} Y)]
    [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} Z)]
    [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} W)]
    (a : Z ⟶ Y) (b : W ⟶ Z) :
    NatTrans.CommShift (derivedInverseImageCompIso a b).hom ℤ := by
  have := Functor.rightDerivedFunctorPlusIso_commShift
    (inverseImage (b ≫ a)) (inverseImageComp a b)
  have := Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology_commShift
    (inverseImage a) (inverseImage b)
  change NatTrans.CommShift
    (((inverseImage (b ≫ a)).rightDerivedFunctorPlusIso (inverseImageComp a b)).hom ≫
      (Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology
        (inverseImage a) (inverseImage b)).hom) ℤ
  infer_instance

private theorem inverseImageEquality_commShift
    {Y Z : Scheme.{u}}
    [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} Y)]
    [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} Z)]
    {a b : Y ⟶ Z} (e : a = b) :
    NatTrans.CommShift
      (eqToIso (congrArg (fun k : Y ⟶ Z => derivedInverseImage k) e)).hom ℤ := by
  subst e
  change NatTrans.CommShift (𝟙 (derivedInverseImage a)) ℤ
  infer_instance

/-- The original canonical derived exchange commutes with the native integer
shifts at its four independent derived-category universes. -/
theorem derivedBaseChangeMap_commShift :
    NatTrans.CommShift (derivedBaseChangeMap f f' g g' h) ℤ := by
  have : (derivedImageAdjunction f).CommShift ℤ :=
    derivedAdjunction_commShift (inverseImageAdjunction f)
  have : (derivedImageAdjunction f').CommShift ℤ :=
    derivedAdjunction_commShift (inverseImageAdjunction f')
  have := inverseImageComp_commShift g f'
  have := inverseImageComp_commShift f g'
  have := inverseImageEquality_commShift h
  have : NatTrans.CommShift (derivedInverseImageSquareIso f f' g g' h).hom ℤ := by
    change NatTrans.CommShift
      ((derivedInverseImageCompIso g f').inv ≫
        (eqToIso (congrArg (fun k : X' ⟶ S => derivedInverseImage k) h)).hom ≫
        (derivedInverseImageCompIso f g').hom) ℤ
    infer_instance
  exact mate_commShift (derivedImageAdjunction f) (derivedImageAdjunction f')
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom)

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction
