/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChange
public import Aglib.Algebra.Homology.CochainComplexPlus.Shift
public import Aglib.Algebra.Homology.CochainComplexPlus.QuasiIsoShift
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TransformationShift
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition.Shift
public import Mathlib.CategoryTheory.Shift.Adjunction

/-! # Native shift compatibility of the original derived exchange

The original derived adjunction unit is characterized by its original
localization equation. That equation consists of the degreewise adjunction
unit and the two native right-derived units, so it commutes with the installed
integer shifts. The actual canonical exchange is consequently a compatible
mate, with the same unit, counit and inverse-image square comparison.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction

section Complex

universe uA vA uB vB

variable {A : Type uA} [Category.{vA} A] [Abelian A]
  {B : Type uB} [Category.{vB} B] [Abelian B]

private theorem complexId_commShift :
    NatTrans.CommShift (Functor.mapCochainComplexPlusIdIso A).hom ℤ := by
  refine NatTrans.CommShift.of_comp_faithful (CochainComplex.Plus.ι A) (h := ?_)
  have h :
      Functor.whiskerRight (Functor.mapCochainComplexPlusIdIso A).hom
          (CochainComplex.Plus.ι A) =
        (𝟭 A).mapCochainComplexPlusCompι.hom ≫
          Functor.whiskerLeft (CochainComplex.Plus.ι A)
            (Functor.mapHomologicalComplexIdIso A (.up ℤ)).hom ≫
          (CochainComplex.Plus.ι A).rightUnitor.hom ≫
          (CochainComplex.Plus.ι A).leftUnitor.inv := by
    ext K i
    simp [Functor.mapCochainComplexPlusIdIso]
  rw [h]
  infer_instance

private theorem complexAdjunction_commShift
    {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive] (adj : L ⊣ R) :
    adj.mapCochainComplexPlus.CommShift ℤ := by
  have := complexId_commShift (A := A)
  apply Adjunction.CommShift.mk'
  have h : adj.mapCochainComplexPlus.unit =
      (Functor.mapCochainComplexPlusIdIso A).inv ≫
        NatTrans.mapCochainComplexPlus adj.unit ≫
        (Functor.mapCochainComplexPlusCompIso L R).hom := by
    ext K i
    simp [Adjunction.mapCochainComplexPlus, Adjunction.mapHomologicalComplex,
      Functor.mapCochainComplexPlusIdIso,
      Functor.mapCochainComplexPlusCompIso, NatTrans.mapCochainComplexPlus]
  rw [h]
  infer_instance

end Complex

section DerivedComparisons

universe uA vA dA uB vB dB uC vC dC

variable {A : Type uA} [Category.{vA} A] [Abelian A] [EnoughInjectives A]
  [HasDerivedCategory.{dA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{dB} B]
  (L : A ⥤ B) [L.Additive]

private theorem derivedIso_commShift {L' : A ⥤ B} [L'.Additive] (e : L ≅ L') :
    NatTrans.CommShift (L.rightDerivedFunctorPlusIso e).hom ℤ := by
  have : NatTrans.CommShift (NatIso.mapCochainComplexPlus e).hom ℤ := by
    change NatTrans.CommShift (NatTrans.mapCochainComplexPlus e.hom) ℤ
    infer_instance
  let β := Functor.whiskerRight (NatIso.mapCochainComplexPlus e).hom
      DerivedCategory.Plus.Q ≫ L'.rightDerivedFunctorPlusUnit
  apply Functor.commShift_of_rightDerived_factorization DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso A) L.rightDerivedFunctorPlusUnit β
  apply NatTrans.ext
  funext K
  exact L.rightDerivedFunctorPlusIso_hom_app e K

variable [EnoughInjectives B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{dC} C]
  (M : B ⥤ C) [M.Additive] [M.PreservesHomology]

private theorem derivedCompIso_commShift :
    NatTrans.CommShift (Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology L M).hom
      ℤ := by
  apply Functor.commShift_of_rightDerived_factorization DerivedCategory.Plus.Q
    (CochainComplex.Plus.quasiIso A) (L ⋙ M).rightDerivedFunctorPlusUnit
    (Functor.rightDerivedFunctorPlusCompUnit L M)
  apply NatTrans.ext
  funext K
  rw [Functor.rightDerivedFunctorPlusCompUnit_app]
  exact Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app L M K

end DerivedComparisons

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
    adj.rightDerivedFunctorPlus.CommShift ℤ := by
  have := complexAdjunction_commShift adj
  let Q : CochainComplex.Plus A ⥤ DerivedCategory.Plus A := DerivedCategory.Plus.Q
  let W : MorphismProperty (CochainComplex.Plus A) := CochainComplex.Plus.quasiIso A
  have : (𝟭 (DerivedCategory.Plus A)).IsRightDerivedFunctor Q.rightUnitor.inv W :=
    Functor.isRightDerivedFunctor_of_inverts W _ Q.rightUnitor
  let β : Q ⟶ Q ⋙ (L.rightDerivedFunctorPlus ⋙ R.rightDerivedFunctorPlus) :=
    Q.leftUnitor.inv ≫
      Functor.whiskerRight adj.mapCochainComplexPlus.unit Q ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft L.mapCochainComplexPlus R.rightDerivedFunctorPlusUnit ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight L.rightDerivedFunctorPlusUnit R.rightDerivedFunctorPlus ≫
      (Functor.associator _ _ _).hom
  have : NatTrans.CommShift β ℤ := by
    dsimp [β]
    infer_instance
  apply Adjunction.CommShift.mk'
  apply Functor.commShift_of_rightDerived_factorization Q W Q.rightUnitor.inv β
  apply NatTrans.ext
  funext K
  simp only [β, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_inv_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  change _ = DerivedCategory.Plus.Q.map (adj.mapCochainComplexPlus.unit.app K) ≫
    R.rightDerivedFunctorPlusUnit.app (L.mapCochainComplexPlus.obj K) ≫
      R.rightDerivedFunctorPlus.map (L.rightDerivedFunctorPlusUnit.app K)
  let e := L.rightDerivedFunctorPlusExactComparison
  calc
    _ = (adj.rightDerivedFunctorPlus.unit.app (DerivedCategory.Plus.Q.obj K) ≫
          R.rightDerivedFunctorPlus.map (e.hom.app K)) ≫
          R.rightDerivedFunctorPlus.map (L.rightDerivedFunctorPlusUnit.app K) := by
      have : IsIso L.rightDerivedFunctorPlusUnit :=
        L.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
      simp [Q, e, Functor.rightDerivedFunctorPlusExactComparison, Category.assoc]
    _ = _ := by
      rw [adj.rightDerivedFunctorPlus_unit_fac K]
      exact Category.assoc _ _ _

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
    NatTrans.CommShift (mateEquiv a₁ a₂ α).natTrans ℤ := by
  dsimp only [mateEquiv, Equiv.coe_fn_mk, TwoSquare.natTrans]
  infer_instance

end Mate

section IsoChains

variable {C D : Type*} [Category* C] [Category* D]
  [HasShift C ℤ] [HasShift D ℤ]
  {F G H I : C ⥤ D}
  [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ] [I.CommShift ℤ]

private theorem isoTrans_commShift (e : F ≅ G) (d : G ≅ H)
    [NatTrans.CommShift e.hom ℤ] [NatTrans.CommShift d.hom ℤ] :
    NatTrans.CommShift (e ≪≫ d).hom ℤ := by
  change NatTrans.CommShift (e.hom ≫ d.hom) ℤ
  infer_instance

private theorem isoChain_commShift (e : F ≅ G) (d : G ≅ H) (c : H ≅ I)
    [NatTrans.CommShift e.hom ℤ] [NatTrans.CommShift d.hom ℤ]
    [NatTrans.CommShift c.hom ℤ] :
    NatTrans.CommShift (e ≪≫ d ≪≫ c).hom ℤ := by
  have := isoTrans_commShift d c
  exact isoTrans_commShift e (d ≪≫ c)

end IsoChains

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
  have := derivedIso_commShift (inverseImage (b ≫ a)) (inverseImageComp a b)
  have := derivedCompIso_commShift (inverseImage a) (inverseImage b)
  exact isoTrans_commShift
    ((inverseImage (b ≫ a)).rightDerivedFunctorPlusIso (inverseImageComp a b))
    (Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology (inverseImage a) (inverseImage b))

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
    exact isoChain_commShift (derivedInverseImageCompIso g f').symm
      (eqToIso (congrArg (fun k : X' ⟶ S => derivedInverseImage k) h))
      (derivedInverseImageCompIso f g')
  exact mate_commShift (derivedImageAdjunction f) (derivedImageAdjunction f')
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom)

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper.Reduction
