/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Composition.Acyclic

/-! # Three-factor comparisons of bounded-below right-derived functors

Two installed composition comparisons and the derived image of an ordinary
natural isomorphism construct one comparison between the composed derived
functors. Its whole unit equation retains the original composite units.
The composition comparisons agree with the native uniqueness, homology,
injective-preservation and acyclic-image constructions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe uA vA wA uB vB wB uC vC wC uD vD wD

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

section Composition

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  [EnoughInjectives A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  [EnoughInjectives B]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (F : A ⥤ B) (G : B ⥤ D) [F.Additive] [G.Additive]

/-- The installed canonical composition comparison satisfies the whole original unit equation. -/
theorem rightDerivedFunctorPlusCompComparison_unit :
    (F ⋙ G).rightDerivedFunctorPlusUnit ≫
        whiskerLeft DerivedCategory.Plus.Q (rightDerivedFunctorPlusCompComparison F G) =
      rightDerivedFunctorPlusCompUnit F G := by
  simpa only [rightDerivedFunctorPlusCompComparison, Category.id_comp] using
    rightDerivedNatTrans_fac (F ⋙ G).rightDerivedFunctorPlus
      (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)
      (F ⋙ G).rightDerivedFunctorPlusUnit (rightDerivedFunctorPlusCompUnit F G)
      (CochainComplex.Plus.quasiIso A) (𝟙 _)

variable
  [(F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor
    (rightDerivedFunctorPlusCompUnit F G) (CochainComplex.Plus.quasiIso A)]

/-- Native derivability identifies the canonical comparison with the original uniqueness map. -/
theorem rightDerivedFunctorPlusCompComparison_eq_rightDerivedUnique_hom :
    rightDerivedFunctorPlusCompComparison F G =
      (rightDerivedUnique (F ⋙ G).rightDerivedFunctorPlus
        (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)
        (F ⋙ G).rightDerivedFunctorPlusUnit (rightDerivedFunctorPlusCompUnit F G)
        (CochainComplex.Plus.quasiIso A)).hom := by
  change rightDerivedFunctorPlusCompComparison F G =
    rightDerivedNatTrans (F ⋙ G).rightDerivedFunctorPlus
      (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)
      (F ⋙ G).rightDerivedFunctorPlusUnit (rightDerivedFunctorPlusCompUnit F G)
      (CochainComplex.Plus.quasiIso A) (𝟙 _)
  apply (F ⋙ G).rightDerivedFunctorPlus.rightDerived_ext
    (F ⋙ G).rightDerivedFunctorPlusUnit (CochainComplex.Plus.quasiIso A)
  rw [rightDerivedFunctorPlusCompComparison_unit, rightDerivedNatTrans_fac, Category.id_comp]

/-- A proved native composite derivability condition makes the canonical comparison invertible. -/
theorem isIso_rightDerivedFunctorPlusCompComparison_of_isRightDerivedFunctor :
    IsIso (rightDerivedFunctorPlusCompComparison F G) := by
  rw [rightDerivedFunctorPlusCompComparison_eq_rightDerivedUnique_hom F G]
  infer_instance

omit [(F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor
  (rightDerivedFunctorPlusCompUnit F G) (CochainComplex.Plus.quasiIso A)] in
/-- Homology preservation supplies invertibility of the same canonical composition map. -/
theorem isIso_rightDerivedFunctorPlusCompComparison_of_preservesHomology
    [G.PreservesHomology] : IsIso (rightDerivedFunctorPlusCompComparison F G) := by
  let := isRightDerivedFunctor_comp_of_preservesHomology F G
  exact isIso_rightDerivedFunctorPlusCompComparison_of_isRightDerivedFunctor F G

omit [(F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor
  (rightDerivedFunctorPlusCompUnit F G) (CochainComplex.Plus.quasiIso A)] in
/-- Preservation of injectives supplies invertibility of the same canonical composition map. -/
theorem isIso_rightDerivedFunctorPlusCompComparison_of_preservesInjectives
    [F.PreservesInjectiveObjects] : IsIso (rightDerivedFunctorPlusCompComparison F G) := by
  let := isRightDerivedFunctor_comp_of_preservesInjectiveObjects F G
  exact isIso_rightDerivedFunctorPlusCompComparison_of_isRightDerivedFunctor F G

end Composition

section CompositionIso

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  [EnoughInjectives A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  [EnoughInjectives B]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (F : A ⥤ B) (G : B ⥤ D) [F.Additive] [G.Additive]
  [IsIso (rightDerivedFunctorPlusCompComparison F G)]

/-- The isomorphism of the installed canonical composition comparison. -/
def rightDerivedFunctorPlusCompIso :
    (F ⋙ G).rightDerivedFunctorPlus ≅
      F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus :=
  asIso (rightDerivedFunctorPlusCompComparison F G)

/-- The canonical composition isomorphism retains the whole composite unit. -/
theorem rightDerivedFunctorPlusCompIso_unit :
    (F ⋙ G).rightDerivedFunctorPlusUnit ≫
        whiskerLeft DerivedCategory.Plus.Q (rightDerivedFunctorPlusCompIso F G).hom =
      rightDerivedFunctorPlusCompUnit F G :=
  rightDerivedFunctorPlusCompComparison_unit F G

/-- The canonical isomorphism agrees with an actual native `rightDerivedUnique` construction. -/
theorem rightDerivedFunctorPlusCompIso_eq_rightDerivedUnique
    [(F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (rightDerivedFunctorPlusCompUnit F G) (CochainComplex.Plus.quasiIso A)] :
    rightDerivedFunctorPlusCompIso F G =
      rightDerivedUnique (F ⋙ G).rightDerivedFunctorPlus
        (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus)
        (F ⋙ G).rightDerivedFunctorPlusUnit (rightDerivedFunctorPlusCompUnit F G)
        (CochainComplex.Plus.quasiIso A) := by
  apply Iso.ext
  exact rightDerivedFunctorPlusCompComparison_eq_rightDerivedUnique_hom F G

/-- Whole unit uniqueness identifies the original homology-preservation branch. -/
theorem rightDerivedFunctorPlusCompIso_eq_of_preservesHomology [G.PreservesHomology] :
    rightDerivedFunctorPlusCompIso F G =
      rightDerivedFunctorPlusCompIsoOfPreservesHomology F G := by
  apply Iso.ext
  apply (F ⋙ G).rightDerivedFunctorPlus.rightDerived_ext
    (F ⋙ G).rightDerivedFunctorPlusUnit (CochainComplex.Plus.quasiIso A)
  rw [rightDerivedFunctorPlusCompIso_unit]
  apply NatTrans.ext
  funext K
  dsimp only [NatTrans.comp_app, whiskerLeft_app]
  symm
  simpa only [rightDerivedFunctorPlusCompUnit_app] using
    rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app F G K

/-- Whole unit uniqueness identifies the original injective-preservation branch. -/
theorem rightDerivedFunctorPlusCompIso_eq_of_preservesInjectives
    [F.PreservesInjectiveObjects] :
    rightDerivedFunctorPlusCompIso F G =
      rightDerivedFunctorPlusCompIsoOfPreservesInjectives F G := by
  apply Iso.ext
  apply (F ⋙ G).rightDerivedFunctorPlus.rightDerived_ext
    (F ⋙ G).rightDerivedFunctorPlusUnit (CochainComplex.Plus.quasiIso A)
  rw [rightDerivedFunctorPlusCompIso_unit]
  apply NatTrans.ext
  funext K
  dsimp only [NatTrans.comp_app, whiskerLeft_app]
  symm
  simpa only [rightDerivedFunctorPlusCompUnit_app] using
    rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app F G K

/-- Whole unit uniqueness identifies the original acyclic-image branch. -/
theorem rightDerivedFunctorPlusCompIso_eq_of_acyclic [PreservesFiniteLimits G]
    (hI : ∀ (J : A) [Injective J] (n : ℕ),
      IsZero ((G.rightDerived (n + 1)).obj (F.obj J))) :
    rightDerivedFunctorPlusCompIso F G =
      rightDerivedFunctorPlusCompIsoOfAcyclic F G hI := by
  apply Iso.ext
  apply (F ⋙ G).rightDerivedFunctorPlus.rightDerived_ext
    (F ⋙ G).rightDerivedFunctorPlusUnit (CochainComplex.Plus.quasiIso A)
  rw [rightDerivedFunctorPlusCompIso_unit]
  apply NatTrans.ext
  funext K
  dsimp only [NatTrans.comp_app, whiskerLeft_app]
  symm
  simpa only [rightDerivedFunctorPlusCompUnit_app] using
    rightDerivedFunctorPlusCompIsoOfAcyclic_hom_app F G hI K

end CompositionIso

section ThreeFactor

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  [EnoughInjectives A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  [EnoughInjectives B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [I.Additive]
  (e : F ⋙ G ≅ H ⋙ I)
  [IsIso (rightDerivedFunctorPlusCompComparison F G)]
  [IsIso (rightDerivedFunctorPlusCompComparison H I)]

/-- The original two composition comparisons and derived ordinary isomorphism,
constructed as one comparison of the composed bounded-below derived functors. -/
def rightDerivedFunctorPlusThreeFactorIso :
    F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus ≅
      H.rightDerivedFunctorPlus ⋙ I.rightDerivedFunctorPlus :=
  (rightDerivedFunctorPlusCompIso F G).symm ≪≫
    rightDerivedFunctorPlusIso (F ⋙ G) e ≪≫ rightDerivedFunctorPlusCompIso H I

/-- The shared comparison retains the three original factors, including their orientations. -/
theorem rightDerivedFunctorPlusThreeFactorIso_eq_original :
    rightDerivedFunctorPlusThreeFactorIso F G H I e =
      (asIso (rightDerivedFunctorPlusCompComparison F G)).symm ≪≫
        rightDerivedFunctorPlusIso (F ⋙ G) e ≪≫
        asIso (rightDerivedFunctorPlusCompComparison H I) := rfl

/-- The whole three-factor comparison commutes with the original composite units. -/
theorem rightDerivedFunctorPlusThreeFactorIso_unit :
    rightDerivedFunctorPlusCompUnit F G ≫
        whiskerLeft DerivedCategory.Plus.Q
          (rightDerivedFunctorPlusThreeFactorIso F G H I e).hom =
      whiskerRight (NatIso.mapCochainComplexPlus e).hom DerivedCategory.Plus.Q ≫
        rightDerivedFunctorPlusCompUnit H I := by
  apply NatTrans.ext
  funext K
  have hL := NatTrans.congr_app (rightDerivedFunctorPlusCompIso_unit F G) K
  have hM := rightDerivedFunctorPlusIso_hom_app (F ⋙ G) e K
  have hR := NatTrans.congr_app (rightDerivedFunctorPlusCompIso_unit H I) K
  dsimp only [NatTrans.comp_app, whiskerLeft_app] at hL hR
  dsimp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  rw [← hL]
  simp only [rightDerivedFunctorPlusThreeFactorIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, hM, Category.assoc, hR]

/-- The component of the whole unit law on an actual bounded-below complex. -/
theorem rightDerivedFunctorPlusThreeFactorIso_unit_app (K : CochainComplex.Plus A) :
    (rightDerivedFunctorPlusCompUnit F G).app K ≫
        (rightDerivedFunctorPlusThreeFactorIso F G H I e).hom.app
          (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map ((NatIso.mapCochainComplexPlus e).hom.app K) ≫
        (rightDerivedFunctorPlusCompUnit H I).app K := by
  simpa only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] using
    NatTrans.congr_app (rightDerivedFunctorPlusThreeFactorIso_unit F G H I e) K

end ThreeFactor

end CategoryTheory.Functor
