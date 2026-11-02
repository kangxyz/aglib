/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactAdjunction
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactTriangleIdentity
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.LocalizedConjugacy

/-!
# Original identity conjugacy for localized exact adjunctions

The specified original identity comparisons remain conjugate under the actual
localized adjunction. The proof compares the original units on all cochain
complexes and uses localization uniqueness, not bounded-below restriction.
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe u v w

namespace CategoryTheory.Adjunction

private theorem identity_unit_of_factors
    {C D : Type*} [Category* C] [Category* D]
    (Q : C ⥤ D) (R : C ⥤ C) (S : D ⥤ D)
    {X Y : C} {Z : D} (u : X ⟶ R.obj Y) (v : Q.obj X ⟶ S.obj Z)
    (l : Z ≅ Q.obj Y)
    (rX : S.obj (Q.obj X) ≅ Q.obj (R.obj X))
    (rY : S.obj (Q.obj Y) ≅ Q.obj (R.obj Y))
    (eL : Y ≅ X) (eR : R.obj X ≅ X)
    (eLD : Z ≅ Q.obj X) (eRD : S.obj (Q.obj X) ≅ Q.obj X)
    (hu : v ≫ S.map l.hom = Q.map u ≫ rY.inv)
    (hn : S.map (Q.map eL.hom) ≫ rX.hom = rY.hom ≫ Q.map (R.map eL.hom))
    (hL : eLD.hom = l.hom ≫ Q.map eL.hom)
    (hR : eRD.hom = rX.hom ≫ Q.map eR.hom)
    (hc : u ≫ R.map eL.hom ≫ eR.hom = 𝟙 X) :
    eRD.inv = v ≫ S.map eLD.hom := by
  apply (cancel_mono eRD.hom).mp
  rw [Iso.inv_hom_id]
  symm
  rw [hL, hR, S.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hu]
  simp only [Iso.inv_hom_id_assoc]
  rw [← Q.map_comp, ← Q.map_comp, hc, Q.map_id]

private theorem unit_of_specified_mate
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {U : C ⥤ C'} {V : D ⥤ D'}
    (a : L ⊣ R) (a' : L' ⊣ R')
    (α : U ⋙ L' ⟶ L ⋙ V) (β : R ⋙ U ⟶ V ⋙ R')
    (hβ : (mateEquiv a a' (TwoSquare.mk _ _ _ _ α)).natTrans = β) (X : C) :
    a'.unit.app (U.obj X) ≫ R'.map (α.app X) =
      U.map (a.unit.app X) ≫ β.app (L.obj X) := by
  have hu := unit_mateEquiv a a' (TwoSquare.mk _ _ _ _ α) X
  change U.map (a.unit.app X) ≫
      (mateEquiv a a' (TwoSquare.mk _ _ _ _ α)).natTrans.app (L.obj X) =
    a'.unit.app (U.obj X) ≫ R'.map (α.app X) at hu
  rw [hβ] at hu
  exact hu.symm

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {L R : A ⥤ A} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

omit [HasDerivedCategory.{w} A]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R] in
private theorem mapComplex_identity_unit (a : L ⊣ R)
    (eL : L ≅ 𝟭 A) (eR : R ≅ 𝟭 A)
    (h : conjugateEquiv Adjunction.id a eL.hom = eR.inv) (K : CochainComplex A ℤ) :
    (a.mapHomologicalComplex (.up ℤ)).unit.app K ≫
      (R.mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex eL (.up ℤ)).hom.app K) ≫
      (NatIso.mapHomologicalComplex eR (.up ℤ)).hom.app K = 𝟙 K := by
  ext n
  change a.unit.app (K.X n) ≫ R.map (eL.hom.app (K.X n)) ≫
    eR.hom.app (K.X n) = 𝟙 (K.X n)
  have hh := unit_conjugateEquiv Adjunction.id a eL.hom (K.X n)
  rw [h] at hh
  change (𝟙 _) ≫ eR.inv.app (K.X n) =
    a.unit.app (K.X n) ≫ R.map (eL.hom.app (K.X n)) at hh
  rw [Category.id_comp] at hh
  rw [← Category.assoc, ← hh, Iso.inv_hom_id_app]
  rfl

/-- The original exact identity comparisons retain their conjugacy under the
same native localized adjunction and the native derived identity comparison. -/
theorem mapDerivedCategory_conjugate_id (a : L ⊣ R)
    (eL : L ≅ 𝟭 A) (eR : R ≅ 𝟭 A)
    (h : conjugateEquiv Adjunction.id a eL.hom = eR.inv) :
    conjugateEquiv Adjunction.id a.mapDerivedCategoryAdjunction
      (mapDerivedCategoryOriginalIso L (𝟭 A) eL ≪≫ mapDerivedCategoryIdIso A).hom =
      (mapDerivedCategoryOriginalIso R (𝟭 A) eR ≪≫ mapDerivedCategoryIdIso A).inv := by
  let eLD := mapDerivedCategoryOriginalIso L (𝟭 A) eL ≪≫ mapDerivedCategoryIdIso A
  let eRD := mapDerivedCategoryOriginalIso R (𝟭 A) eR ≪≫ mapDerivedCategoryIdIso A
  change conjugateEquiv Adjunction.id a.mapDerivedCategoryAdjunction eLD.hom = eRD.inv
  apply conjugateEquiv_eq_of_unit
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  change (𝟙 _) ≫ eRD.inv.app (DerivedCategory.Q.obj K) =
    a.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Q.obj K) ≫
      R.mapDerivedCategory.map (eLD.hom.app (DerivedCategory.Q.obj K))
  rw [Category.id_comp]
  refine identity_unit_of_factors DerivedCategory.Q
    (R.mapHomologicalComplex (.up ℤ)) R.mapDerivedCategory
    ((a.mapHomologicalComplex (.up ℤ)).unit.app K)
    (a.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Q.obj K))
    (L.mapDerivedCategoryFactors.app K) (R.mapDerivedCategoryFactors.app K)
    (R.mapDerivedCategoryFactors.app ((L.mapHomologicalComplex (.up ℤ)).obj K))
    ((NatIso.mapHomologicalComplex eL (.up ℤ)).app K)
    ((NatIso.mapHomologicalComplex eR (.up ℤ)).app K)
    (eLD.app (DerivedCategory.Q.obj K)) (eRD.app (DerivedCategory.Q.obj K))
    ?_ ?_ (mapDerivedCategoryOriginalIdIso_fac L eL K)
    (mapDerivedCategoryOriginalIdIso_fac R eR K) (mapComplex_identity_unit a eL eR h K)
  · exact unit_of_specified_mate (a.mapHomologicalComplex (.up ℤ))
      a.mapDerivedCategoryAdjunction L.mapDerivedCategoryFactors.hom
      R.mapDerivedCategoryFactors.inv a.mapDerivedCategoryAdjunction_factor_mate K
  · exact R.mapDerivedCategoryFactors.hom.naturality
      ((NatIso.mapHomologicalComplex eL (.up ℤ)).hom.app K)

end CategoryTheory.Adjunction
