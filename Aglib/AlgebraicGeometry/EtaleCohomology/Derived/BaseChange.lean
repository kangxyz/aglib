/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.Composition
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.NatTrans
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Homology
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.UnitComparison

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.SingleSquare

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ZeroComparison


public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ActualZeroComparison

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.CoherenceNormalization
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.H1Normalization
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HomAction
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.SectionPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback

/-!
# Canonical bounded-below étale base change

The exchange map is the mate under the original derived adjunctions. Its maps
on higher direct images use the native homology and exact-single comparisons.
No cartesian hypothesis or invertibility claim is needed for these constructions.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u wX wS wX' wS'

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{wX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{wS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- The derived inverse-image square uses the native composition comparisons. -/
def derivedInverseImageSquareIso :
    derivedInverseImage g ⋙ derivedInverseImage f' ≅
      derivedInverseImage f ⋙ derivedInverseImage g' :=
  (derivedInverseImageCompIso g f').symm ≪≫
    eqToIso (congrArg (fun k : X' ⟶ S => derivedInverseImage k) h) ≪≫
      derivedInverseImageCompIso f g'

/-- The canonical derived exchange map for a commuting square of schemes. -/
def derivedBaseChangeMap :
    derivedDirectImage f ⋙ derivedInverseImage g ⟶
      derivedInverseImage g' ⋙ derivedDirectImage f' :=
  (mateEquiv (derivedImageAdjunction f) (derivedImageAdjunction f')
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom)).natTrans

/-- The exchange component retains the original derived unit and counit. -/
theorem derivedBaseChangeMap_app
    (K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X)) :
    MateComponentEquation (derivedImageAdjunction f) (derivedImageAdjunction f')
      (derivedInverseImageSquareIso f f' g g' h).hom K :=
  mateComponentEquation (derivedImageAdjunction f) (derivedImageAdjunction f')
    (derivedInverseImageSquareIso f f' g g' h).hom K

/-- The adjoint equation of the canonical derived exchange. -/
theorem derivedBaseChangeMap_counit
    (K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X)) :
    MateCounitEquation (derivedImageAdjunction f) (derivedImageAdjunction f')
      (derivedInverseImageSquareIso f f' g g' h).hom K :=
  mateCounitEquation (derivedImageAdjunction f) (derivedImageAdjunction f')
    (derivedInverseImageSquareIso f f' g g' h).hom K

/-- The adjoint equation characterizes the derived exchange, independently of resolutions. -/
theorem eq_derivedBaseChangeMap_iff
    (β : derivedDirectImage f ⋙ derivedInverseImage g ⟶
      derivedInverseImage g' ⋙ derivedDirectImage f') :
    β = derivedBaseChangeMap f f' g g' h ↔
      ∀ K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X),
        (derivedInverseImage f').map (β.app K) ≫
            (derivedImageAdjunction f').counit.app ((derivedInverseImage g').obj K) =
          (derivedInverseImageSquareIso f f' g g' h).hom.app
              ((derivedDirectImage f).obj K) ≫
            (derivedInverseImage g').map ((derivedImageAdjunction f).counit.app K) :=
  eq_mateEquiv_iff (derivedImageAdjunction f) (derivedImageAdjunction f') _ β

/-- Morphisms of derived coefficients commute with the canonical exchange. -/
@[reassoc]
theorem derivedBaseChangeMap_naturality
    {K L : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X)} (a : K ⟶ L) :
    (derivedInverseImage g).map ((derivedDirectImage f).map a) ≫
        (derivedBaseChangeMap f f' g g' h).app L =
      (derivedBaseChangeMap f f' g g' h).app K ≫
        (derivedDirectImage f').map ((derivedInverseImage g').map a) :=
  (derivedBaseChangeMap f f' g g' h).naturality a

/-- The native exact-homology comparison identifies the source of higher base change. -/
def higherBaseChangeSourceIso (q : ℕ) :
    higherDirectImage f q ⋙ inverseImage g ≅
      DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0 ⋙
        (derivedDirectImage f ⋙ derivedInverseImage g) ⋙
        DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ) :=
  Functor.isoWhiskerRight (higherDirectImageIso f q) (inverseImage g) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      ((inverseImage g).rightDerivedFunctorPlusHomologyIso (q : ℤ)).symm) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm

/-- The native exact-single comparison identifies the target of higher base change. -/
def higherBaseChangeTargetIso (q : ℕ) :
    DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0 ⋙
        (derivedInverseImage g' ⋙ derivedDirectImage f') ⋙
        DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ) ≅
      inverseImage g' ⋙ higherDirectImage f' q :=
  Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((inverseImage g').rightDerivedFunctorPlusSingleIso 0) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (higherDirectImageIso f' q).symm

/-- The source comparison evaluated on a coefficient sheaf. -/
theorem higherBaseChangeSourceIso_hom_app (q : ℕ)
    (F : AbelianSheaf.{u, u + 1} X) :
    (higherBaseChangeSourceIso f g q).hom.app F =
      (inverseImage g).map ((higherDirectImageIso f q).hom.app F) ≫
        ((inverseImage g).rightDerivedFunctorPlusHomologyIso (q : ℤ)).inv.app
          ((derivedDirectImage f).obj
            ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)) := by
  simp only [higherBaseChangeSourceIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp]
  change (inverseImage g).map ((higherDirectImageIso f q).hom.app F) ≫
      (𝟙 _ ≫ (((inverseImage g).rightDerivedFunctorPlusHomologyIso (q : ℤ)).inv.app
        ((derivedDirectImage f).obj
          ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)) ≫
        𝟙 _)) = _
  rw [Category.id_comp, Category.comp_id]

/-- The target comparison evaluated on a coefficient sheaf. -/
theorem higherBaseChangeTargetIso_hom_app (q : ℕ)
    (F : AbelianSheaf.{u, u + 1} X) :
    (higherBaseChangeTargetIso f' g' q).hom.app F =
      (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ)).map
          ((derivedDirectImage f').map
            (((inverseImage g').rightDerivedFunctorPlusSingleIso 0).hom.app F)) ≫
        (higherDirectImageIso f' q).inv.app ((inverseImage g').obj F) := by
  simp only [higherBaseChangeTargetIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_map, Category.id_comp]
  change (𝟙 _) ≫ ((DerivedCategory.Plus.homologyFunctor
      (AbelianSheaf.{u, u + 1} S') (q : ℤ)).map
        ((derivedDirectImage f').map
          (((inverseImage g').rightDerivedFunctorPlusSingleIso 0).hom.app F)) ≫
      (higherDirectImageIso f' q).inv.app ((inverseImage g').obj F)) = _
  exact Category.id_comp _

/-- Base change on every natural-degree higher direct image, induced by the actual derived map. -/
def higherBaseChangeMap (q : ℕ) :
    higherDirectImage f q ⋙ inverseImage g ⟶ inverseImage g' ⋙ higherDirectImage f' q :=
  (higherBaseChangeSourceIso f g q).hom ≫
    Functor.whiskerLeft
      (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0)
      (Functor.whiskerRight (derivedBaseChangeMap f f' g g' h)
        (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ))) ≫
    (higherBaseChangeTargetIso f' g' q).hom

/-- The all-degree exchange formula with its native higher-direct-image, homology,
and exact-single comparison maps. -/
theorem higherBaseChangeMap_app (q : ℕ) (F : AbelianSheaf.{u, u + 1} X) :
    WhiskeredTransportEquation (higherBaseChangeSourceIso f g q).hom
    (derivedBaseChangeMap f f' g g' h) (higherBaseChangeTargetIso f' g' q).hom F
    ((inverseImage g).map ((higherDirectImageIso f q).hom.app F))
    (((inverseImage g).rightDerivedFunctorPlusHomologyIso (q : ℤ)).inv.app
      ((derivedDirectImage f).obj
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)))
    ((DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ)).map
      ((derivedDirectImage f').map
        (((inverseImage g').rightDerivedFunctorPlusSingleIso 0).hom.app F)))
    ((higherDirectImageIso f' q).inv.app ((inverseImage g').obj F)) :=
  whiskeredTransportEquation (higherBaseChangeSourceIso f g q).hom
    (derivedBaseChangeMap f f' g g' h) (higherBaseChangeTargetIso f' g' q).hom F
    ((inverseImage g).map ((higherDirectImageIso f q).hom.app F))
    (((inverseImage g).rightDerivedFunctorPlusHomologyIso (q : ℤ)).inv.app
      ((derivedDirectImage f).obj
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)))
    ((DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ)).map
      ((derivedDirectImage f').map
        (((inverseImage g').rightDerivedFunctorPlusSingleIso 0).hom.app F)))
    ((higherDirectImageIso f' q).inv.app ((inverseImage g').obj F))
    (higherBaseChangeSourceIso_hom_app f g q F)
    (higherBaseChangeTargetIso_hom_app f' g' q F)

/-- Naturality of higher base change in the coefficient sheaf. -/
@[reassoc]
theorem higherBaseChangeMap_naturality (q : ℕ)
    {F G : AbelianSheaf.{u, u + 1} X} (a : F ⟶ G) :
    (inverseImage g).map ((higherDirectImage f q).map a) ≫
        (higherBaseChangeMap f f' g g' h q).app G =
      (higherBaseChangeMap f f' g g' h q).app F ≫
        (higherDirectImage f' q).map ((inverseImage g').map a) :=
  (higherBaseChangeMap f f' g g' h q).naturality a

/-- The actual inverse-image square over identity horizontal maps is normalized by the
original inverse-image identity comparisons. -/
theorem derivedInverseImageSquareIso_id (e : f ≫ 𝟙 S = 𝟙 X ≫ f) :
    derivedInverseImageSquareIso f f (𝟙 S) (𝟙 X) e ≪≫
        Functor.isoWhiskerLeft (derivedInverseImage f) (derivedInverseImageIdIso X) ≪≫
        Functor.rightUnitor (derivedInverseImage f) =
      Functor.isoWhiskerRight (derivedInverseImageIdIso S) (derivedInverseImage f) ≪≫
        Functor.leftUnitor (derivedInverseImage f) := by
  apply Iso.ext
  apply (cancel_epi (derivedInverseImageCompIso (𝟙 S) f).hom).1
  simp only [derivedInverseImageSquareIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  have hA := congrArg Iso.hom (derivedInverseImageCompIso_id_comp f)
  have hB := congrArg Iso.hom (derivedInverseImageCompIso_comp_id f)
  simp only [Iso.trans_hom] at hA hB
  rw [hB, hA]
  simp only [eqToIso.hom, eqToHom_trans]

/-- The canonical exchange for identity horizontal maps is the identity after the
original inverse-image identity comparisons, not a newly chosen exchange. -/
@[reassoc]
theorem derivedBaseChangeMap_id (e : f ≫ 𝟙 S = 𝟙 X ≫ f)
    (F : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X)) :
    (derivedBaseChangeMap f f (𝟙 S) (𝟙 X) e).app F ≫
        (derivedDirectImage f).map ((derivedInverseImageIdIso X).hom.app F) =
      (derivedInverseImageIdIso S).hom.app ((derivedDirectImage f).obj F) := by
  have hα : ∀ A : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} S),
      (derivedInverseImage f).map ((derivedInverseImageIdIso S).hom.app A) ≫
          (TwoSquare.hId (derivedInverseImage f)).app A =
        (derivedInverseImageSquareIso f f (𝟙 S) (𝟙 X) e).hom.app A ≫
          (derivedInverseImageIdIso X).hom.app ((derivedInverseImage f).obj A) := by
    intro A
    have he := congrArg (fun i => i.hom.app A) (derivedInverseImageSquareIso_id f e)
    simpa [TwoSquare.hId] using he.symm
  have he := mateEquiv_top_bottom_naturality (derivedImageAdjunction f)
    (derivedImageAdjunction f)
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f (𝟙 S) (𝟙 X) e).hom)
    (TwoSquare.hId (derivedInverseImage f)) (derivedInverseImageIdIso S).hom
    (derivedInverseImageIdIso X).hom hα F
  simpa [derivedBaseChangeMap, mateEquiv_hId, TwoSquare.vId] using he.symm


/-- The actual derived inverse-image square respects the original exact comparison on
arbitrary bounded-below complexes. The original termwise square is retained literally. -/
theorem derivedInverseImageSquareIso_exactComparison
    (K : CochainComplex.Plus (AbelianSheaf.{u, u + 1} S)) :
    ExactComparisonSquareEquation (inverseImage f) (inverseImage g')
      (inverseImage g) (inverseImage f')
      (TwoSquare.mk _ _ _ _ (inverseImageSquareIso f f' g g' h).hom)
      (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom) K := by
  have hc := exactComparisonSquareEquation
    (inverseImage f) (inverseImage g') (inverseImage g) (inverseImage f')
    (inverseImage (f' ≫ g)) (inverseImage (g' ≫ f))
    (inverseImageComp g f') (inverseImageComp f g')
    (eqToIso (congrArg (fun k : X' ⟶ S => inverseImage k) h)) K
  simp only [Functor.rightDerivedFunctorPlusIso_eqToIso] at hc
  simpa only [derivedInverseImageSquareIso, derivedInverseImageCompIso,
    inverseImageSquareIso] using hc

/-- The canonical derived exchange preserves the original right-derived units.
The shared formula retains the original degreewise underived exchange and both
exact inverse-image comparisons; no nonexact right-derived unit is cancelled. -/
theorem derivedBaseChangeMap_unit
    (K : CochainComplex.Plus (AbelianSheaf.{u, u + 1} X)) :
    DerivedMateUnitEquation (inverseImageAdjunction f) (inverseImageAdjunction f')
      (TwoSquare.mk _ _ _ _ (inverseImageSquareIso f f' g g' h).hom)
      (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom) K :=
  derivedMateUnitEquation_of_exactSquare (inverseImageAdjunction f) (inverseImageAdjunction f')
    (TwoSquare.mk _ _ _ _ (inverseImageSquareIso f f' g g' h).hom)
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom)
    (derivedInverseImageSquareIso_exactComparison f f' g g' h) K

/-- The scheme specialization keeps the shared single-square proposition intact. -/
theorem derivedInverseImageSquareIso_single
    (T : AbelianSheaf.{u, u + 1} S) :
    SingleComparisonSquareEquation (inverseImage f) (inverseImage g')
      (inverseImage g) (inverseImage f')
      (inverseImageSquareIso f f' g g' h).hom
      (derivedInverseImageSquareIso f f' g g' h).hom T :=
  singleComparisonSquareEquation (inverseImage f) (inverseImage g')
    (inverseImage g) (inverseImage f') _ _ T
    (derivedInverseImageSquareIso_exactComparison f f' g g' h
      ((CochainComplex.singleFunctorPlus (AbelianSheaf.{u, u + 1} S) 0).obj T))

omit [HasDerivedCategory.{wX} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{wS} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{wX'} (AbelianSheaf.{u, u + 1} X')]
    [HasDerivedCategory.{wS'} (AbelianSheaf.{u, u + 1} S')] in
/-- The original exchange is the literal ordinary adjunction mate. -/
theorem baseChangeMap_eq_mate :
    baseChangeMap f f' g g' h =
      (mateEquiv (inverseImageAdjunction f) (inverseImageAdjunction f')
        (TwoSquare.mk _ _ _ _ (inverseImageSquareIso f f' g g' h).hom)).natTrans := rfl

/-- The derived sheaf adjunction is the native right-derived adjunction. -/
theorem derivedImageAdjunction_eq_rightDerivedFunctorPlus :
    derivedImageAdjunction f = (inverseImageAdjunction f).rightDerivedFunctorPlus := rfl

/-- The derived exchange retains the native derived adjunctions explicitly. -/
theorem derivedBaseChangeMap_eq_nativeMate :
    derivedBaseChangeMap f f' g g' h =
      (mateEquiv (inverseImageAdjunction f).rightDerivedFunctorPlus
        (inverseImageAdjunction f').rightDerivedFunctorPlus
        (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom)).natTrans := by
  calc
    derivedBaseChangeMap f f' g g' h =
        (mateEquiv (derivedImageAdjunction f) (derivedImageAdjunction f')
          (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom)).natTrans := rfl
    _ = _ := congrArg₂ (fun a b =>
      (mateEquiv a b
        (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom)).natTrans)
      (derivedImageAdjunction_eq_rightDerivedFunctorPlus f)
      (derivedImageAdjunction_eq_rightDerivedFunctorPlus f')

/-- The higher-direct-image comparison is the original native comparison. -/
theorem higherDirectImageIso_eq_native (q : ℕ) :
    higherDirectImageIso f q = (directImage f).rightDerivedSingleHomologyIso q := rfl

/-- The actual higher exchange is its original source/mate/target transport. -/
theorem higherBaseChangeMap_eq_transport (q : ℕ) :
    higherBaseChangeMap f f' g g' h q =
      (higherBaseChangeSourceIso f g q).hom ≫
        Functor.whiskerLeft
          (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0)
          (Functor.whiskerRight (derivedBaseChangeMap f f' g g' h)
            (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ))) ≫
        (higherBaseChangeTargetIso f' g' q).hom := rfl

/-- The original unit equation written using the actual canonical exchange maps. -/
theorem derivedBaseChangeMap_actualUnit
    (K : CochainComplex.Plus (AbelianSheaf.{u, u + 1} X)) :
    Functor.ActualDerivedUnitEquation
      (directImage f) (directImage f') (inverseImage g) (inverseImage g')
      (baseChangeMap f f' g g' h) (derivedBaseChangeMap f f' g g' h) K :=
  actualDerivedUnitEquation_of_mate
    (inverseImageAdjunction f) (inverseImageAdjunction f')
    (TwoSquare.mk _ _ _ _ (inverseImageSquareIso f f' g g' h).hom)
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom)
    (baseChangeMap f f' g g' h) (derivedBaseChangeMap f f' g g' h)
    (baseChangeMap_eq_mate f f' g g' h) (derivedBaseChangeMap_eq_nativeMate f f' g g' h) K
    (derivedBaseChangeMap_unit f f' g g' h K)

/-- The original R0 normalization, with all actual maps kept opaque. -/
theorem higherBaseChangeMap_zero (F : AbelianSheaf.{u, u + 1} X) :
    Functor.HigherExchangeZeroEquation
      (directImage f) (directImage f') (inverseImage g) (inverseImage g')
      (baseChangeMap f f' g g' h) F ((higherBaseChangeMap f f' g g' h 0).app F) :=
  Functor.higherExchangeZero_normalization_actual
    (directImage f) (directImage f') (inverseImage g) (inverseImage g')
    (baseChangeMap f f' g g' h) (derivedBaseChangeMap f f' g g' h)
    (higherDirectImageIso f 0) (higherDirectImageIso f' 0)
    (higherDirectImageIso_eq_native f 0) (higherDirectImageIso_eq_native f' 0)
    (higherBaseChangeSourceIso f g 0).hom (higherBaseChangeTargetIso f' g' 0).hom
    (higherBaseChangeMap f f' g g' h 0) (higherBaseChangeMap_eq_transport f f' g g' h 0) F
    (derivedBaseChangeMap_actualUnit f f' g g' h) (higherBaseChangeMap_app f f' g g' h 0 F)

end AlgebraicGeometry.Scheme.EtaleCohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u eX eS eX' eS' dX dS dX' dS'

attribute [local instance] hasSheafifyLarge

private theorem inverseImageSquareIso_decomposition
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) :
    inverseImageSquareIso f f' g g' h =
      (inverseImageComp g f').symm ≪≫
        eqToIso (congrArg (fun k : X' ⟶ S => inverseImage k) h) ≪≫
        inverseImageComp f g' := rfl

private theorem inverseImageSquareIso_components
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (T : AbelianSheaf.{u, u + 1} S) :
    (inverseImageSquareIso f f' g g' h).app T =
      ((inverseImageComp g f').app T).symm ≪≫
        (eqToIso (congrArg (fun k : X' ⟶ S => inverseImage k) h)).app T ≪≫
        (inverseImageComp f g').app T :=
  exchangeCoherence_app_decomposition (inverseImageSquareIso f f' g g' h)
    (inverseImageComp g f')
    (eqToIso (congrArg (fun k : X' ⟶ S => inverseImage k) h))
    (inverseImageComp f g') (inverseImageSquareIso_decomposition f f' g g' h) T

private theorem inverseImageSquareIso_arrowSquare
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (T : AbelianSheaf.{u, u + 1} S) :
    (inverseImageComp g f').hom.app T ≫
        (inverseImageSquareIso f f' g g' h).hom.app T =
      (eqToIso (congrArg (fun k : X' ⟶ S => inverseImage k) h)).hom.app T ≫
        (inverseImageComp f g').hom.app T :=
  exchangeCoherence_square_app (inverseImageSquareIso f f' g g' h)
    (inverseImageComp g f')
    (eqToIso (congrArg (fun k : X' ⟶ S => inverseImage k) h))
    (inverseImageComp f g') (inverseImageSquareIso_decomposition f f' g g' h) T



section OriginalConstants
variable {X S X' S' : Scheme.{u}}
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- Constant transport across equality of morphisms keeps the original map. -/
theorem inverseImageConstantIso_eq_transport
    {Y V : Scheme.{u}} {k l : Y ⟶ V} (e : k = l) (A : AddCommGrpCat.{u + 1}) :
    (eqToIso (congrArg (fun m : Y ⟶ V => inverseImage m) e)).hom.app
        ((constantSheaf (Scheme.smallEtaleTopology V) AddCommGrpCat.{u + 1}).obj A) ≫
      (inverseImageConstantIso l).hom.app A =
    (inverseImageConstantIso k).hom.app A := by
  subst l
  change (𝟙 _) ≫ (inverseImageConstantIso k).hom.app A = _
  exact Category.id_comp _

/-- The original constant source comparisons obey the original square. -/
theorem inverseImageSquareIso_constant (A : AddCommGrpCat.{u + 1}) :
    (inverseImageSquareIso f f' g g' h).hom.app
        ((constantSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).obj A) ≫
      (inverseImage g').map ((inverseImageConstantIso f).hom.app A) ≫
        (inverseImageConstantIso g').hom.app A =
    (inverseImage f').map ((inverseImageConstantIso g).hom.app A) ≫
      (inverseImageConstantIso f').hom.app A := by
  exact arrowSquareCancel
    ((inverseImageComp g f').hom.app _)
    ((inverseImageSquareIso f f' g g' h).hom.app _)
    ((eqToIso (congrArg (fun k : X' ⟶ S => inverseImage k) h)).hom.app _)
    ((inverseImageComp f g').hom.app _)
    ((inverseImageComp g f').inv.app _)
    ((inverseImageComp g f').inv_hom_id_app _)
    (inverseImageSquareIso_arrowSquare f f' g g' h _)
    ((inverseImage f').map ((inverseImageConstantIso g).hom.app A) ≫
      (inverseImageConstantIso f').hom.app A)
    ((inverseImage g').map ((inverseImageConstantIso f).hom.app A) ≫
      (inverseImageConstantIso g').hom.app A)
    ((inverseImageConstantIso (f' ≫ g)).hom.app A)
    ((inverseImageConstantIso (g' ≫ f)).hom.app A)
    (inverseImageComp_constant g f' A) (inverseImageComp_constant f g' A)
    (inverseImageConstantIso_eq_transport h A)

end OriginalConstants

section DerivedAction
variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

/-- The actual canonical derived exchange acts on adjunction representatives
through the actual derived inverse-image square. This is not an exchange chosen
after an isomorphism theorem. Specialize K to single(F)[1] for H¹. -/
theorem derivedBaseChangeMap_homEquiv_action
    {A : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} S)}
    {K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X)}
    (a : (derivedInverseImage f).obj A ⟶ K) :
    (derivedInverseImage g).map ((derivedImageAdjunction f).homEquiv A K a) ≫
        (derivedBaseChangeMap f f' g g' h).app K =
      (derivedImageAdjunction f').homEquiv
        ((derivedInverseImage g).obj A) ((derivedInverseImage g').obj K)
        ((derivedInverseImageSquareIso f f' g g' h).hom.app A ≫
          (derivedInverseImage g').map a) :=
  CategoryTheory.mateEquiv_homEquiv_action_actual
    (derivedImageAdjunction f) (derivedImageAdjunction f')
    (inverseImageAdjunction f).rightDerivedFunctorPlus
    (inverseImageAdjunction f').rightDerivedFunctorPlus
    (derivedImageAdjunction_eq_rightDerivedFunctorPlus f)
    (derivedImageAdjunction_eq_rightDerivedFunctorPlus f')
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom)
    (derivedBaseChangeMap f f' g g' h)
    (derivedBaseChangeMap_eq_nativeMate f f' g g' h) a

/-- The fixed constant-integer comparison used to put an original H¹ class
into the source of the derived adjunction. Both factors are original maps. -/
def derivedConstantIntegerPullbackIso :
    (derivedInverseImage f).obj
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} S) 0).obj
          ((constantSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) ≅
      (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj
        ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) :=
  ((inverseImage f).rightDerivedFunctorPlusSingleIso 0).app _ ≪≫
    (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).mapIso
      ((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))

/-- The canonical representative of the original H¹ class in the left derived
adjunction. Its source and shifted-single target are fixed before taking mates. -/
def derivedH1Representative
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    (F : AbelianSheaf.{u, u + 1} X) (a : H1Etale.{u, u + 1, eX} X F) :
    (derivedInverseImage f).obj
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} S) 0).obj
          ((constantSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) ⟶
      ((DerivedCategory.Plus.singleFunctor
        (AbelianSheaf.{u, u + 1} X) 0).obj F)⟦(1 : ℤ)⟧ :=
  (derivedConstantIntegerPullbackIso f).hom ≫ a.homPlus

/-- The named representative is exactly the native constant comparison followed
by the original class, not a chosen replacement morphism. -/
theorem derivedH1Representative_eq
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    (F : AbelianSheaf.{u, u + 1} X) (a : H1Etale.{u, u + 1, eX} X F) :
    derivedH1Representative f F a = (derivedConstantIntegerPullbackIso f).hom ≫
      a.homPlus := rfl

/-- The actual canonical mate acts on the canonical representative of every
original H¹ class. The shared proposition retains the literal original maps. -/
theorem derivedBaseChangeMap_h1Representative
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    (F : AbelianSheaf.{u, u + 1} X) (a : H1Etale.{u, u + 1, eX} X F) :
    MateHomActionEquation (derivedImageAdjunction f) (derivedImageAdjunction f')
      (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom)
      (derivedBaseChangeMap f f' g g' h) (derivedH1Representative f F a) :=
  mateHomActionEquation_actual
    (derivedImageAdjunction f) (derivedImageAdjunction f')
    (inverseImageAdjunction f).rightDerivedFunctorPlus
    (inverseImageAdjunction f').rightDerivedFunctorPlus
    (derivedImageAdjunction_eq_rightDerivedFunctorPlus f)
    (derivedImageAdjunction_eq_rightDerivedFunctorPlus f')
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom)
    (derivedBaseChangeMap f f' g g' h)
    (derivedBaseChangeMap_eq_nativeMate f f' g g' h) (derivedH1Representative f F a)

/-- The canonical constant-single comparison retains its original two factors. -/
theorem derivedConstantIntegerPullbackIso_hom :
    (derivedConstantIntegerPullbackIso f).hom =
      ((inverseImage f).rightDerivedFunctorPlusSingleIso 0).hom.app
        ((constantSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫
      (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).map
        ((inverseImageConstantIso f).hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ))) := rfl

/-- The native single square and ordinary constant square determine the actual
constant-source derived square. All normalization is performed at abstract functors. -/
theorem derivedInverseImageSquareIso_constant :
    DerivedConstantSquareEquation
      (inverseImage f) (inverseImage g') (inverseImage g) (inverseImage f')
      (derivedInverseImageSquareIso f f' g g' h).hom
      (derivedConstantIntegerPullbackIso f) (derivedConstantIntegerPullbackIso g)
      (derivedConstantIntegerPullbackIso f') (derivedConstantIntegerPullbackIso g') :=
  derivedConstantSquareEquation_of_single
    (inverseImage f) (inverseImage g') (inverseImage g) (inverseImage f')
    (derivedInverseImageSquareIso f f' g g' h).hom
    (derivedConstantIntegerPullbackIso f) (derivedConstantIntegerPullbackIso g)
    (derivedConstantIntegerPullbackIso f') (derivedConstantIntegerPullbackIso g')
    (inverseImageSquareIso f f' g g' h).hom
    ((inverseImageConstantIso f).hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    ((inverseImageConstantIso g).hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    ((inverseImageConstantIso f').hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    ((inverseImageConstantIso g').hom.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (inverseImageSquareIso_constant f f' g g' h (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (derivedInverseImageSquareIso_single f f' g g' h
      ((constantSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))))
    (derivedConstantIntegerPullbackIso_hom f) (derivedConstantIntegerPullbackIso_hom g)
    (derivedConstantIntegerPullbackIso_hom f') (derivedConstantIntegerPullbackIso_hom g')

/-- The native shifted-single comparison at the target of an H¹ pullback. -/
def derivedH1TargetMap (F : AbelianSheaf.{u, u + 1} X) :
    (derivedInverseImage g').obj
        (((DerivedCategory.Plus.singleFunctor
          (AbelianSheaf.{u, u + 1} X) 0).obj F)⟦(1 : ℤ)⟧) ⟶
      ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X') 0).obj
        ((inverseImage g').obj F))⟦(1 : ℤ)⟧ :=
  ((derivedInverseImage g').commShiftIso (1 : ℤ)).hom.app
      ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F) ≫
    (((inverseImage g').rightDerivedFunctorPlusSingleIso 0).hom.app F)⟦(1 : ℤ)⟧'

/-- The target map is precisely the native shift and single comparison. -/
theorem derivedH1TargetMap_eq (F : AbelianSheaf.{u, u + 1} X) :
    derivedH1TargetMap g' F =
      ((derivedInverseImage g').commShiftIso (1 : ℤ)).hom.app
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F) ≫
      (((inverseImage g').rightDerivedFunctorPlusSingleIso 0).hom.app F)⟦(1 : ℤ)⟧' := rfl

/-- The original H¹ pullback has its native derived representative. -/
theorem h1Pullback_homPlus_native
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{eX'} (AbelianSheaf.{u, u + 1} X')]
    (F : AbelianSheaf.{u, u + 1} X) (a : H1Etale.{u, u + 1, eX} X F) :
    (h1Pullback g' F a).homPlus =
      (derivedConstantIntegerPullbackIso g').inv ≫
        (derivedInverseImage g').map a.homPlus ≫ derivedH1TargetMap g' F := by
  rw [show h1Pullback g' F a = cohomologyPullback g' F 1 a from rfl,
    cohomologyPullback_homPlus]
  simp only [derivedConstantIntegerPullbackIso, Iso.trans_inv, Functor.mapIso_inv,
    derivedH1TargetMap, ShiftedHom.map, Category.assoc, Iso.app_inv]
  rfl

/-- The actual canonical mate recovers original H¹ pullback after the native
constant, adjunction, shift and single comparisons, without any R¹ section claim. -/
theorem derivedBaseChangeMap_h1_normalized
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{eX'} (AbelianSheaf.{u, u + 1} X')]
    (F : AbelianSheaf.{u, u + 1} X) (a : H1Etale.{u, u + 1, eX} X F) :
    NormalizedMateHomActionEquation (derivedImageAdjunction f) (derivedImageAdjunction f')
      (derivedBaseChangeMap f f' g g' h)
      (derivedConstantIntegerPullbackIso g) (derivedConstantIntegerPullbackIso f')
      (derivedH1Representative f F a) (derivedH1TargetMap g' F)
      (h1Pullback g' F a).homPlus :=
  normalizedMateHomActionEquation_actual
    (derivedImageAdjunction f) (derivedImageAdjunction f')
    (inverseImageAdjunction f).rightDerivedFunctorPlus
    (inverseImageAdjunction f').rightDerivedFunctorPlus
    (derivedImageAdjunction_eq_rightDerivedFunctorPlus f)
    (derivedImageAdjunction_eq_rightDerivedFunctorPlus f')
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom)
    (derivedBaseChangeMap f f' g g' h) (derivedBaseChangeMap_eq_nativeMate f f' g g' h)
    (derivedConstantIntegerPullbackIso f) (derivedConstantIntegerPullbackIso g)
    (derivedConstantIntegerPullbackIso f') (derivedConstantIntegerPullbackIso g')
    (constantSourceSquareEquation_of_derivedConstant
      (inverseImage f) (inverseImage g') (inverseImage g) (inverseImage f')
      (derivedInverseImageSquareIso f f' g g' h).hom
      (derivedConstantIntegerPullbackIso f) (derivedConstantIntegerPullbackIso g)
      (derivedConstantIntegerPullbackIso f') (derivedConstantIntegerPullbackIso g')
      (derivedInverseImageSquareIso_constant f f' g g' h))
    a.homPlus (derivedH1Representative f F a) (derivedH1Representative_eq f F a)
    (derivedH1TargetMap g' F) (h1Pullback g' F a).homPlus
    (h1Pullback_homPlus_native g' F a).symm

end DerivedAction

end AlgebraicGeometry.Scheme.EtaleCohomology
