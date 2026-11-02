/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChange.Higher
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HigherWholePasting
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

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.WholeNormalization
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ActualPasting

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HigherHorizontalEdges
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HigherHorizontal
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HigherIdentity
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HigherVertical
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.SingleCoherence
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HomologyCoherence

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


omit [HasDerivedCategory.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{wX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{wS'} (AbelianSheaf.{u, u + 1} S')] in
/-- The original R0 normalization, with all actual maps kept opaque. -/
theorem higherBaseChangeMap_zero (F : AbelianSheaf.{u, u + 1} X) :
    Functor.HigherExchangeZeroEquation
      (directImage f) (directImage f') (inverseImage g) (inverseImage g')
      (baseChangeMap f f' g g' h) F ((higherBaseChangeMap f f' g g' h 0).app F) := by
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X')
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S')
  exact Functor.higherExchangeZero_normalization_actual
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

universe eY eV

section TargetAction
variable {Y : Scheme.{u}}
  [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]

/-- An ordinary coefficient square acts on the original H1 classes.
The original coefficient functoriality suffices, without a derived category. -/
private theorem h1CoefficientMap_square_homPlus
    {P Q R U : AbelianSheaf.{u, u + 1} Y}
    (a : P ⟶ Q) (s : Q ⟶ U) (t : P ⟶ R) (b : R ⟶ U)
    (hs : a ≫ s = t ≫ b)
    (x : H1Etale.{u, u + 1, eY} Y P)
    (y : H1Etale.{u, u + 1, eY} Y Q)
    (z : H1Etale.{u, u + 1, eY} Y R)
    (w : H1Etale.{u, u + 1, eY} Y U)
    (ha : coefficientMap a x = y) (ht : coefficientMap t x = z)
    (hb : coefficientMap b z = w) : coefficientMap s y = w := by
  calc
    coefficientMap s y = coefficientMap (a ≫ s) x := by
      rw [coefficientMap_comp, AddMonoidHom.comp_apply, ha]
    _ = coefficientMap (t ≫ b) x := by rw [hs]
    _ = w := by rw [coefficientMap_comp, AddMonoidHom.comp_apply, ht, hb]

end TargetAction

private theorem h1Pullback_eq_transport_homPlus_route
    {Y V : Scheme.{u}}
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{eV} (AbelianSheaf.{u, u + 1} V)]
    {k l : Y ⟶ V} (e : k = l) (T : AbelianSheaf.{u, u + 1} V)
    (a : H1Etale.{u, u + 1, eV} V T) :
    coefficientMap
        ((eqToIso (congrArg (fun m : Y ⟶ V => inverseImage m) e)).hom.app T)
        (h1Pullback k T a) = h1Pullback l T a := by
  subst l
  change coefficientMap (𝟙 _) (h1Pullback k T a) = h1Pullback k T a
  rw [coefficientMap_id]
  rfl

/-- The original H1 square, preserving its original universes and hypotheses. -/
theorem h1Pullback_square
    {X S X' S' : Scheme.{u}}
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{eS} (AbelianSheaf.{u, u + 1} S)]
    [HasExt.{eX'} (AbelianSheaf.{u, u + 1} X')]
    [HasExt.{eS'} (AbelianSheaf.{u, u + 1} S')]
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (T : AbelianSheaf.{u, u + 1} S)
    (a : H1Etale.{u, u + 1, eS} S T) :
    coefficientMap ((inverseImageSquareIso f f' g g' h).hom.app T)
        (h1Pullback f' ((inverseImage g).obj T) (h1Pullback g T a)) =
      h1Pullback g' ((inverseImage f).obj T) (h1Pullback f T a) := by
  exact h1CoefficientMap_square_homPlus
    ((inverseImageComp g f').hom.app T)
    ((inverseImageSquareIso f f' g g' h).hom.app T)
    ((eqToIso (congrArg (fun k : X' ⟶ S => inverseImage k) h)).hom.app T)
    ((inverseImageComp f g').hom.app T)
    (inverseImageSquareIso_arrowSquare f f' g g' h T)
    (h1Pullback (f' ≫ g) T a)
    (h1Pullback f' ((inverseImage g).obj T) (h1Pullback g T a))
    (h1Pullback (g' ≫ f) T a)
    (h1Pullback g' ((inverseImage f).obj T) (h1Pullback f T a))
    (h1Pullback_comp g f' T a)
    (h1Pullback_eq_transport_homPlus_route h T a)
    (h1Pullback_comp f g' T a)


section OriginalSquareCongruence
variable {X S X' S' : Scheme.{u}}
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{eS} (AbelianSheaf.{u, u + 1} S)]
  [HasExt.{eX'} (AbelianSheaf.{u, u + 1} X')]
  [HasExt.{eS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)

include f' h in
/-- This is the literal content of the existing generic H¹ pullback congruence,
obtained from the stronger square above without importing finite-etale rigidity.
The old theorem's variables are R=S, S=S', K=X, L=X', uS=g, gS=f',
gK=f, and k=g'. -/
theorem h1Pullback_square_congruence (T : AbelianSheaf.{u, u + 1} S)
    (a b : H1Etale.{u, u + 1, eS} S T)
    (hab : h1Pullback g T a = h1Pullback g T b) :
    h1Pullback g' ((inverseImage f).obj T) (h1Pullback f T a) =
      h1Pullback g' ((inverseImage f).obj T) (h1Pullback f T b) := by
  rw [← h1Pullback_square f f' g g' h T a,
    ← h1Pullback_square f f' g g' h T b, hab]

end OriginalSquareCongruence

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

/-- The actual normalized mate lands on the original coefficient-transported
opposite H¹ path. No sections-of-higher-direct-image identification is used. -/
theorem derivedBaseChangeMap_h1_square
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{eX'} (AbelianSheaf.{u, u + 1} X')]
    [HasExt.{eS} (AbelianSheaf.{u, u + 1} S)]
    [HasExt.{eS'} (AbelianSheaf.{u, u + 1} S')]
    (T : AbelianSheaf.{u, u + 1} S) (a : H1Etale.{u, u + 1, eS} S T) :
    NormalizedMateHomActionEquation (derivedImageAdjunction f) (derivedImageAdjunction f')
      (derivedBaseChangeMap f f' g g' h)
      (derivedConstantIntegerPullbackIso g) (derivedConstantIntegerPullbackIso f')
      (derivedH1Representative f ((inverseImage f).obj T) (h1Pullback f T a))
      (derivedH1TargetMap g' ((inverseImage f).obj T))
      (coefficientMap ((inverseImageSquareIso f f' g g' h).hom.app T)
        (h1Pullback f' ((inverseImage g).obj T) (h1Pullback g T a))).homPlus :=
  normalizedMateHomActionEquation_congr_target
    (derivedImageAdjunction f) (derivedImageAdjunction f')
    (derivedBaseChangeMap f f' g g' h)
    (derivedConstantIntegerPullbackIso g) (derivedConstantIntegerPullbackIso f')
    (derivedH1Representative f ((inverseImage f).obj T) (h1Pullback f T a))
    (derivedH1TargetMap g' ((inverseImage f).obj T)) _ _
    (congrArg (fun b : H1Etale.{u, u + 1, eX'} X'
      ((inverseImage g').obj ((inverseImage f).obj T)) => b.homPlus)
      (h1Pullback_square f f' g g' h T a).symm)
    (derivedBaseChangeMap_h1_normalized f f' g g' h
      ((inverseImage f).obj T) (h1Pullback f T a))

end DerivedAction

end AlgebraicGeometry.Scheme.EtaleCohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge

universe wb0 wb1 wb2 wb3 wb4 wb5


/-- The derived exchange remains the mate under its original sheaf adjunctions. -/
theorem derivedBaseChangeMap_eq_mate {X S X' S' : Scheme.{u}}
    [HasDerivedCategory.{wb0} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{wb1} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{wb2} (AbelianSheaf.{u, u + 1} X')]
    [HasDerivedCategory.{wb3} (AbelianSheaf.{u, u + 1} S')]
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) :
    derivedBaseChangeMap f f' g g' h =
      (mateEquiv (derivedImageAdjunction f) (derivedImageAdjunction f')
        (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom)).natTrans := rfl

section Horizontal
variable {X₀ S₀ X₁ S₁ X₂ S₂ : Scheme.{u}}
  [HasDerivedCategory.{wb0} (AbelianSheaf.{u, u + 1} X₀)]
  [HasDerivedCategory.{wb1} (AbelianSheaf.{u, u + 1} S₀)]
  [HasDerivedCategory.{wb2} (AbelianSheaf.{u, u + 1} X₁)]
  [HasDerivedCategory.{wb3} (AbelianSheaf.{u, u + 1} S₁)]
  [HasDerivedCategory.{wb4} (AbelianSheaf.{u, u + 1} X₂)]
  [HasDerivedCategory.{wb5} (AbelianSheaf.{u, u + 1} S₂)]
  (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂)
  (g₁ : S₁ ⟶ S₀) (g₂ : S₂ ⟶ S₁) (h₁ : X₁ ⟶ X₀) (h₂ : X₂ ⟶ X₁)
  (e₁ : f₁ ≫ g₁ = h₁ ≫ f₀) (e₂ : f₂ ≫ g₂ = h₂ ≫ f₁)
  (e : f₂ ≫ (g₂ ≫ g₁) = (h₂ ≫ h₁) ≫ f₀)

/-- Horizontal pasting for the actual derived exchange maps, with native comparisons. -/
theorem derivedBaseChangeMap_hComp
    (K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X₀)) :
    (derivedInverseImageCompIso g₁ g₂).hom.app ((derivedDirectImage f₀).obj K) ≫
        (derivedInverseImage g₂).map ((derivedBaseChangeMap f₀ f₁ g₁ h₁ e₁).app K) ≫
        (derivedBaseChangeMap f₁ f₂ g₂ h₂ e₂).app ((derivedInverseImage h₁).obj K) =
      (derivedBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).app K ≫
        (derivedDirectImage f₂).map ((derivedInverseImageCompIso h₁ h₂).hom.app K) := by
  apply actualHorizontalMateEquation_eq
    (derivedBaseChangeMap f₀ f₁ g₁ h₁ e₁) (derivedBaseChangeMap f₁ f₂ g₂ h₂ e₂)
    (derivedBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e)
    (derivedInverseImageCompIso g₁ g₂).hom
    (derivedInverseImageCompIso h₁ h₂).hom K
  exact actualHorizontalMateEquation_of_mates
    (derivedImageAdjunction f₀) (derivedImageAdjunction f₁)
    (derivedImageAdjunction f₂)
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f₀ f₁ g₁ h₁ e₁).hom)
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f₁ f₂ g₂ h₂ e₂).hom)
    (TwoSquare.mk _ _ _ _
      (derivedInverseImageSquareIso f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).hom)
    (derivedInverseImageCompIso g₁ g₂).hom
    (derivedInverseImageCompIso h₁ h₂).hom
    (derivedBaseChangeMap f₀ f₁ g₁ h₁ e₁) (derivedBaseChangeMap f₁ f₂ g₂ h₂ e₂)
    (derivedBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e)
    (derivedBaseChangeMap_eq_mate f₀ f₁ g₁ h₁ e₁)
    (derivedBaseChangeMap_eq_mate f₁ f₂ g₂ h₂ e₂)
    (derivedBaseChangeMap_eq_mate f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e) K
    (horizontalMateEquation _ _ _ _ _
      (derivedImageAdjunction f₀) (derivedImageAdjunction f₁)
    (derivedImageAdjunction f₂)
      (derivedInverseImageSquareIso_hComp f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e) K)

end Horizontal

section VerticalPasting
universe w₁ w₂ w₃ w₄ w₅ w₆
variable {S X Y S' X' Y' : Scheme.{u}}
  [HasDerivedCategory.{w₁} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{w₂} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{w₃} (AbelianSheaf.{u, u + 1} Y)]
  [HasDerivedCategory.{w₄} (AbelianSheaf.{u, u + 1} S')]
  [HasDerivedCategory.{w₅} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{w₆} (AbelianSheaf.{u, u + 1} Y')]
  (f : X ⟶ S) (k : Y ⟶ X) (f' : X' ⟶ S') (k' : Y' ⟶ X')
  (g : S' ⟶ S) (g' : X' ⟶ X) (g'' : Y' ⟶ Y)
  (h₁ : f' ≫ g = g' ≫ f) (h₂ : k' ≫ g' = g'' ≫ k)
  (h : (k' ≫ f') ≫ g = g'' ≫ (k ≫ f))

/-- Actual vertical derived exchange pasting, normalized by the native comparisons. -/
theorem derivedBaseChangeMap_vComp_mate
    (K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} Y)) :
    VerticalMateEquation
      (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h₁).hom)
      (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso k k' g' g'' h₂).hom)
      (TwoSquare.mk _ _ _ _
        (derivedInverseImageSquareIso (k ≫ f) (k' ≫ f') g g'' h).hom)
      (derivedDirectImageCompIso f k) (derivedDirectImageCompIso f' k')
      (derivedImageAdjunction f) (derivedImageAdjunction f')
      (derivedImageAdjunction k) (derivedImageAdjunction k')
      (derivedImageAdjunction (k ≫ f)) (derivedImageAdjunction (k' ≫ f')) K :=
  verticalMateEquation
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h₁).hom)
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso k k' g' g'' h₂).hom)
    (TwoSquare.mk _ _ _ _
      (derivedInverseImageSquareIso (k ≫ f) (k' ≫ f') g g'' h).hom)
    (derivedInverseImageCompIso f k) (derivedInverseImageCompIso f' k')
    (derivedDirectImageCompIso f k) (derivedDirectImageCompIso f' k')
    (derivedImageAdjunction f) (derivedImageAdjunction f')
    (derivedImageAdjunction k) (derivedImageAdjunction k')
    (derivedImageAdjunction (k ≫ f)) (derivedImageAdjunction (k' ≫ f'))
    (conjugateEquiv_derivedInverseImageCompIso_hom f k)
    (conjugateEquiv_derivedInverseImageCompIso_hom f' k')
    (derivedInverseImageSquareIso_vComp f k f' k' g g' g'' h₁ h₂ h) K

/-- Vertical pasting of the actual exchange maps under the native direct-image comparisons. -/
theorem derivedBaseChangeMap_vComp
    (K : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} Y)) :
    (derivedInverseImage g).map ((derivedDirectImageCompIso f k).hom.app K) ≫
        (derivedBaseChangeMap f f' g g' h₁).app ((derivedDirectImage k).obj K) ≫
        (derivedDirectImage f').map ((derivedBaseChangeMap k k' g' g'' h₂).app K) =
      (derivedBaseChangeMap (k ≫ f) (k' ≫ f') g g'' h).app K ≫
        (derivedDirectImageCompIso f' k').hom.app ((derivedInverseImage g'').obj K) := by
  apply actualVerticalMateEquation_eq
    (derivedBaseChangeMap f f' g g' h₁) (derivedBaseChangeMap k k' g' g'' h₂)
    (derivedBaseChangeMap (k ≫ f) (k' ≫ f') g g'' h)
    (derivedDirectImageCompIso f k).hom (derivedDirectImageCompIso f' k').hom K
  exact actualVerticalMateEquation_of_mates
    (derivedImageAdjunction f) (derivedImageAdjunction f')
    (derivedImageAdjunction k) (derivedImageAdjunction k')
    (derivedImageAdjunction (k ≫ f)) (derivedImageAdjunction (k' ≫ f'))
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h₁).hom)
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso k k' g' g'' h₂).hom)
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso (k ≫ f) (k' ≫ f') g g'' h).hom)
    (derivedDirectImageCompIso f k) (derivedDirectImageCompIso f' k')
    (derivedBaseChangeMap f f' g g' h₁) (derivedBaseChangeMap k k' g' g'' h₂)
    (derivedBaseChangeMap (k ≫ f) (k' ≫ f') g g'' h)
    (derivedBaseChangeMap_eq_mate f f' g g' h₁) (derivedBaseChangeMap_eq_mate k k' g' g'' h₂)
    (derivedBaseChangeMap_eq_mate (k ≫ f) (k' ≫ f') g g'' h) K
    (derivedBaseChangeMap_vComp_mate f k f' k' g g' g'' h₁ h₂ h K)

end VerticalPasting

universe wIdS wIdS'


/-- The actual derived exchange over vertical identities uses the native identity maps. -/
theorem derivedBaseChangeMap_vId_mate {S S' : Scheme.{u}}
    [HasDerivedCategory.{wIdS} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{wIdS'} (AbelianSheaf.{u, u + 1} S')] (g : S' ⟶ S)
    (e : 𝟙 S' ≫ g = g ≫ 𝟙 S) (A : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} S)) :
    IdentityMateEquation
      (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso (𝟙 S) (𝟙 S') g g e).hom)
      (derivedDirectImageIdIso S) (derivedDirectImageIdIso S')
      (derivedImageAdjunction (𝟙 S)) (derivedImageAdjunction (𝟙 S')) A :=
  identityMateEquation
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso (𝟙 S) (𝟙 S') g g e).hom)
    (derivedInverseImageIdIso S) (derivedInverseImageIdIso S')
    (derivedDirectImageIdIso S) (derivedDirectImageIdIso S')
    (derivedImageAdjunction (𝟙 S)) (derivedImageAdjunction (𝟙 S'))
    (conjugateEquiv_derivedInverseImageIdIso_hom S) (conjugateEquiv_derivedInverseImageIdIso_hom S')
    (derivedInverseImageSquareIso_vId g e) A

/-- The actual exchange over vertical identities uses the original direct-image units. -/
theorem derivedBaseChangeMap_vId {S S' : Scheme.{u}}
    [HasDerivedCategory.{wIdS} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{wIdS'} (AbelianSheaf.{u, u + 1} S')] (g : S' ⟶ S)
    (e : 𝟙 S' ≫ g = g ≫ 𝟙 S) (A : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} S)) :
    (derivedInverseImage g).map ((derivedDirectImageIdIso S).hom.app A) =
      (derivedBaseChangeMap (𝟙 S) (𝟙 S') g g e).app A ≫
        (derivedDirectImageIdIso S').hom.app ((derivedInverseImage g).obj A) := by
  apply actualIdentityMateEquation_eq
    (derivedBaseChangeMap (𝟙 S) (𝟙 S') g g e)
    (derivedDirectImageIdIso S).hom (derivedDirectImageIdIso S').hom A
  exact actualIdentityMateEquation_of_mate
    (derivedImageAdjunction (𝟙 S)) (derivedImageAdjunction (𝟙 S'))
    (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso (𝟙 S) (𝟙 S') g g e).hom)
    (derivedDirectImageIdIso S) (derivedDirectImageIdIso S')
    (derivedBaseChangeMap (𝟙 S) (𝟙 S') g g e)
    (derivedBaseChangeMap_eq_mate (𝟙 S) (𝟙 S') g g e) A (derivedBaseChangeMap_vId_mate g e A)

section HigherActualMapFactor
universe wBC0 wBC1 wBC2 wBC3

/-- The actual higher exchange has the original derived map as its middle factor. -/
theorem higherBaseChangeMap_target_inv_app
    {X S X' S' : Scheme.{u}}
    [HasDerivedCategory.{wBC0} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{wBC1} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{wBC2} (AbelianSheaf.{u, u + 1} X')]
    [HasDerivedCategory.{wBC3} (AbelianSheaf.{u, u + 1} S')]
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (q : ℕ) (F : AbelianSheaf.{u, u + 1} X) :
    ActualWhiskeredTargetInverseEquation
      (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0)
      (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ))
      (derivedBaseChangeMap f f' g g' h)
      (higherBaseChangeSourceIso f g q) (higherBaseChangeTargetIso f' g' q)
      (higherBaseChangeMap f f' g g' h q) F :=
  actualWhiskeredTargetInverseEquation_of_transport
    (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0)
    (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ))
    (derivedBaseChangeMap f f' g g' h)
    (higherBaseChangeSourceIso f g q) (higherBaseChangeTargetIso f' g' q)
    (higherBaseChangeMap f f' g g' h q) (higherBaseChangeMap_eq_transport f f' g g' h q) F

/-- The shared component predicate for the original higher exchange. -/
theorem higherBaseChangeMap_target_inv_component
    {X S X' S' : Scheme.{u}}
    [HasDerivedCategory.{wBC0} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{wBC1} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{wBC2} (AbelianSheaf.{u, u + 1} X')]
    [HasDerivedCategory.{wBC3} (AbelianSheaf.{u, u + 1} S')]
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (q : ℕ) (F : AbelianSheaf.{u, u + 1} X) :
    MappedTargetInverseEquation
      (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ))
      ((derivedBaseChangeMap f f' g g' h).app
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F))
      ((higherBaseChangeSourceIso f g q).app F)
      ((higherBaseChangeTargetIso f' g' q).app F).symm
      ((higherBaseChangeMap f f' g g' h q).app F) :=
  mappedTargetInverseEquation_of_whiskered
    (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0)
    (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ))
    (derivedBaseChangeMap f f' g g' h)
    (higherBaseChangeSourceIso f g q) (higherBaseChangeTargetIso f' g' q)
    (higherBaseChangeMap f f' g g' h q) F
    (higherBaseChangeMap_target_inv_app f f' g g' h q F)

end HigherActualMapFactor



section HigherHorizontal
universe wHC0 wHC1 wHC2 wHC3 wHC4 wHC5
variable {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}}
  [HasDerivedCategory.{wHC0} (AbelianSheaf.{u, u + 1} X₀)]
  [HasDerivedCategory.{wHC1} (AbelianSheaf.{u, u + 1} X₁)]
  [HasDerivedCategory.{wHC2} (AbelianSheaf.{u, u + 1} X₂)]
  [HasDerivedCategory.{wHC3} (AbelianSheaf.{u, u + 1} S₀)]
  [HasDerivedCategory.{wHC4} (AbelianSheaf.{u, u + 1} S₁)]
  [HasDerivedCategory.{wHC5} (AbelianSheaf.{u, u + 1} S₂)]
  (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂)
  (g₁ : S₁ ⟶ S₀) (g₂ : S₂ ⟶ S₁) (h₁ : X₁ ⟶ X₀) (h₂ : X₂ ⟶ X₁)
  (e₁ : f₁ ≫ g₁ = h₁ ≫ f₀) (e₂ : f₂ ≫ g₂ = h₂ ≫ f₁)
  (e : f₂ ≫ (g₂ ≫ g₁) = (h₂ ≫ h₁) ≫ f₀)
  (q : ℕ) (F : AbelianSheaf.{u, u + 1} X₀)

end HigherHorizontal





section HigherIdentityAppend

universe wHigherIdX wHigherIdS
section HigherIdentity
variable {X S : Scheme.{u}}
  [HasDerivedCategory.{wHigherIdX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wHigherIdS} (AbelianSheaf.{u, u + 1} S)]
  (f : X ⟶ S) (e : f ≫ 𝟙 S = 𝟙 X ≫ f) (q : ℕ)
  (F : AbelianSheaf.{u, u + 1} X)

/-- Original source comparison for the actual R^q identity square. -/
theorem higherBaseChangeMap_id_source :
    (inverseImageId S).hom.app ((higherDirectImage f q).obj F) ≫
        (higherDirectImageIso f q).hom.app F =
      (higherBaseChangeSourceIso f (𝟙 S) q).hom.app F ≫
        (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) (q : ℤ)).map
          ((derivedInverseImageIdIso S).hom.app ((derivedDirectImage f).obj
            ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F))) := by
  exact mapped_identity_source_edge
    (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) (q : ℤ))
    (inverseImage (𝟙 S)) (derivedInverseImage (𝟙 S))
    ((inverseImage (𝟙 S)).rightDerivedFunctorPlusHomologyIso (q : ℤ))
    (inverseImageId S) (derivedInverseImageIdIso S)
    ((derivedDirectImage f).obj
      ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F))
    (Functor.rightDerivedFunctorPlusHomologyIso_id
      (inverseImage (𝟙 S)) (inverseImageId S) (q : ℤ) _)
    ((higherDirectImageIso f q).app F)
    ((higherBaseChangeSourceIso f (𝟙 S) q).app F)
    (higherBaseChangeSourceIso_hom_app f (𝟙 S) q F)

/-- Original target comparison for the actual R^q identity square. -/
theorem higherBaseChangeMap_id_target :
    (higherDirectImage f q).map ((inverseImageId X).hom.app F) ≫
        (higherDirectImageIso f q).hom.app F =
      (higherBaseChangeTargetIso f (𝟙 X) q).inv.app F ≫
        (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) (q : ℤ)).map
          ((derivedDirectImage f).map ((derivedInverseImageIdIso X).hom.app
            ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F))) := by
  exact mapped_identity_target_edge
    (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0)
    (derivedDirectImage f)
    (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) (q : ℤ))
    (higherDirectImage f q) (higherDirectImageIso f q)
    (inverseImage (𝟙 X)) (derivedInverseImage (𝟙 X))
    ((inverseImage (𝟙 X)).rightDerivedFunctorPlusSingleIso 0)
    (inverseImageId X) (derivedInverseImageIdIso X) F
    (Functor.rightDerivedFunctorPlusSingleIso_id
      (inverseImage (𝟙 X)) (inverseImageId X) F)
    ((higherBaseChangeTargetIso f (𝟙 X) q).app F)
    (higherBaseChangeTargetIso_hom_app f (𝟙 X) q F)

omit [HasDerivedCategory.{wHigherIdX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wHigherIdS} (AbelianSheaf.{u, u + 1} S)] in
/-- The actual higher exchange over identity horizontal maps uses the native identity maps. -/
theorem higherBaseChangeMap_id :
    (inverseImageId S).hom.app ((higherDirectImage f q).obj F) =
      (higherBaseChangeMap f f (𝟙 S) (𝟙 X) e q).app F ≫
        (higherDirectImage f q).map ((inverseImageId X).hom.app F) := by
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S)
  let J := (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F
  let Hq := DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) (q : ℤ)
  have hb : (higherBaseChangeMap f f (𝟙 S) (𝟙 X) e q).app F ≫
      (higherBaseChangeTargetIso f (𝟙 X) q).inv.app F =
    (higherBaseChangeSourceIso f (𝟙 S) q).hom.app F ≫
      Hq.map ((derivedBaseChangeMap f f (𝟙 S) (𝟙 X) e).app J) := by
    exact higherBaseChangeMap_target_inv_component f f (𝟙 S) (𝟙 X) e q F
  exact mapped_identity_transport Hq
    ((derivedBaseChangeMap f f (𝟙 S) (𝟙 X) e).app J)
    ((derivedInverseImageIdIso S).hom.app ((derivedDirectImage f).obj J))
    ((derivedDirectImage f).map ((derivedInverseImageIdIso X).hom.app J))
    (derivedBaseChangeMap_id f e J).symm
    ((higherBaseChangeSourceIso f (𝟙 S) q).app F)
    ((higherBaseChangeTargetIso f (𝟙 X) q).app F).symm
    ((higherDirectImageIso f q).app F)
    ((higherBaseChangeMap f f (𝟙 S) (𝟙 X) e q).app F)
    ((inverseImageId S).hom.app ((higherDirectImage f q).obj F))
    ((higherDirectImage f q).map ((inverseImageId X).hom.app F))
    hb (higherBaseChangeMap_id_source f q F) (higherBaseChangeMap_id_target f q F)

end HigherIdentity

end HigherIdentityAppend

section HigherVerticalAppend


universe wV1 wV2 wV3 wV4 wV5 wV6

section HigherVerticalPasting
variable {S X Y S' X' Y' : Scheme.{u}}
  [HasDerivedCategory.{wV1} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{wV2} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wV3} (AbelianSheaf.{u, u + 1} Y)]
  [HasDerivedCategory.{wV4} (AbelianSheaf.{u, u + 1} S')]
  [HasDerivedCategory.{wV5} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{wV6} (AbelianSheaf.{u, u + 1} Y')]
  (f : X ⟶ S) (k : Y ⟶ X) (f' : X' ⟶ S') (k' : Y' ⟶ X')
  (g : S' ⟶ S) (g' : X' ⟶ X) (g'' : Y' ⟶ Y)
  (h₁ : f' ≫ g = g' ≫ f) (h₂ : k' ≫ g' = g'' ≫ k)
  (h : (k' ≫ f') ≫ g = g'' ≫ (k ≫ f))
  (q : ℕ) (F : AbelianSheaf.{u, u + 1} Y)

/-- The actual source comparison to H^q of the composed derived direct images. -/
def higherVerticalSourceIsoApp :
    (inverseImage g).obj ((higherDirectImage (k ≫ f) q).obj F) ≅
      (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ)).obj
        ((derivedInverseImage g).obj ((derivedDirectImage f).obj
          ((derivedDirectImage k).obj
            ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj F)))) :=
  (higherBaseChangeSourceIso (k ≫ f) g q).app F ≪≫
    (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ)).mapIso
      ((derivedInverseImage g).mapIso ((derivedDirectImageCompIso f k).app
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj F)))

/-- The actual target exact-single comparison for the composed derived images. -/
def higherVerticalTargetIsoApp :
    (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ)).obj
        ((derivedDirectImage f').obj ((derivedDirectImage k').obj
          ((derivedInverseImage g'').obj
            ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj F)))) ≅
      (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ)).obj
        ((derivedDirectImage f').obj ((derivedDirectImage k').obj
          ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y') 0).obj
            ((inverseImage g'').obj F)))) :=
  (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ)).mapIso
    ((derivedDirectImage k' ⋙ derivedDirectImage f').mapIso
      (((inverseImage g'').rightDerivedFunctorPlusSingleIso 0).app F))


/-- The actual vertical source comparison has its defining forward arrow. -/
theorem higherVerticalSourceIsoApp_hom :
    (higherVerticalSourceIsoApp f k g q F).hom =
      (higherBaseChangeSourceIso (k ≫ f) g q).hom.app F ≫
        (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ)).map
          ((derivedInverseImage g).map ((derivedDirectImageCompIso f k).hom.app
            ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj F))) := rfl

/-- The actual target comparison retains the original exact-single arrow. -/
theorem higherVerticalTargetIsoApp_hom :
    (higherVerticalTargetIsoApp f' k' g'' q F).hom =
      (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ)).map
        ((derivedDirectImage k' ⋙ derivedDirectImage f').map
          (((inverseImage g'').rightDerivedFunctorPlusSingleIso 0).hom.app F)) := rfl

/-- The native composite higher-image comparison retains its original forward arrow. -/
theorem higherDirectImageCompHomologyIsoApp_hom :
    (higherDirectImageCompHomologyIsoApp f k q F).hom =
      (higherDirectImageIso (k ≫ f) q).hom.app F ≫
        (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) (q : ℤ)).map
          ((derivedDirectImageCompIso f k).hom.app
            ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj F)) := rfl


/-- R^q vertical pasting through homology of the actual composite derived image. -/
theorem higherBaseChangeMap_vComp :
    MappedVerticalPastingEquation
      (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ))
      ((derivedBaseChangeMap f f' g g' h₁).app
          ((derivedDirectImage k).obj
            ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj F)) ≫
        (derivedDirectImage f').map ((derivedBaseChangeMap k k' g' g'' h₂).app
          ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj F)))
      (higherVerticalSourceIsoApp f k g q F)
      (higherVerticalTargetIsoApp f' k' g'' q F)
      (higherDirectImageCompHomologyIsoApp f' k' q ((inverseImage g'').obj F))
      ((higherBaseChangeMap (k ≫ f) (k' ≫ f') g g'' h q).app F) := by
  exact mapped_vertical_pasting_actual_equation
    (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ))
    (derivedDirectImageCompIso f' k')
    (((inverseImage g'').rightDerivedFunctorPlusSingleIso 0).hom.app F)
    ((derivedInverseImage g).map ((derivedDirectImageCompIso f k).hom.app
      ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj F)))
    ((derivedBaseChangeMap f f' g g' h₁).app ((derivedDirectImage k).obj
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj F)) ≫
      (derivedDirectImage f').map ((derivedBaseChangeMap k k' g' g'' h₂).app
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj F)))
    ((derivedBaseChangeMap (k ≫ f) (k' ≫ f') g g'' h).app
      ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj F))
    (derivedBaseChangeMap_vComp f k f' k' g g' g'' h₁ h₂ h
      ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj F))
    ((higherBaseChangeSourceIso (k ≫ f) g q).app F)
    ((higherDirectImageIso (k' ≫ f') q).app ((inverseImage g'').obj F))
    ((higherBaseChangeTargetIso (k' ≫ f') g'' q).app F)
    ((higherBaseChangeMap (k ≫ f) (k' ≫ f') g g'' h q).app F)
    (higherBaseChangeMap_target_inv_component (k ≫ f) (k' ≫ f') g g'' h q F)
    (higherBaseChangeTargetIso_hom_app (k' ≫ f') g'' q F)
    (higherVerticalSourceIsoApp f k g q F)
    (higherVerticalTargetIsoApp f' k' g'' q F)
    (higherDirectImageCompHomologyIsoApp f' k' q ((inverseImage g'').obj F))
    (higherVerticalSourceIsoApp_hom f k g q F)
    (higherVerticalTargetIsoApp_hom f' k' g'' q F)
    (higherDirectImageCompHomologyIsoApp_hom f' k' q ((inverseImage g'').obj F))

end HigherVerticalPasting

end HigherVerticalAppend

section HigherVerticalIdentityAppend

universe wVIdS wVIdS'

/-- Vertical identity exchange in every degree, under the actual homology comparisons. -/
theorem higherBaseChangeMap_vId_homology {S S' : Scheme.{u}}
    [HasDerivedCategory.{wVIdS} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{wVIdS'} (AbelianSheaf.{u, u + 1} S')]
    (g : S' ⟶ S) (e : 𝟙 S' ≫ g = g ≫ 𝟙 S) (q : ℕ)
    (F : AbelianSheaf.{u, u + 1} S) :
    (higherBaseChangeSourceIso (𝟙 S) g q).hom.app F ≫
        (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ)).map
          ((derivedInverseImage g).map ((derivedDirectImageIdIso S).hom.app
            ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} S) 0).obj F))) =
      (higherBaseChangeMap (𝟙 S) (𝟙 S') g g e q).app F ≫
        (higherBaseChangeTargetIso (𝟙 S') g q).inv.app F ≫
        (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ)).map
          ((derivedDirectImageIdIso S').hom.app ((derivedInverseImage g).obj
            ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} S) 0).obj F))) := by
  let J := (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} S) 0).obj F
  let Hq := DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ)
  have hb : (higherBaseChangeMap (𝟙 S) (𝟙 S') g g e q).app F ≫
      (higherBaseChangeTargetIso (𝟙 S') g q).inv.app F =
    (higherBaseChangeSourceIso (𝟙 S) g q).hom.app F ≫
      Hq.map ((derivedBaseChangeMap (𝟙 S) (𝟙 S') g g e).app J) := by
    exact higherBaseChangeMap_target_inv_component (𝟙 S) (𝟙 S') g g e q F
  have hm := congrArg Hq.map (derivedBaseChangeMap_vId g e J)
  simp only [Functor.map_comp] at hm
  change (higherBaseChangeSourceIso (𝟙 S) g q).hom.app F ≫
      Hq.map ((derivedInverseImage g).map ((derivedDirectImageIdIso S).hom.app J)) =
    (higherBaseChangeMap (𝟙 S) (𝟙 S') g g e q).app F ≫
      (higherBaseChangeTargetIso (𝟙 S') g q).inv.app F ≫
      Hq.map ((derivedDirectImageIdIso S').hom.app ((derivedInverseImage g).obj J))
  rw [hm, ← Category.assoc, ← hb, Category.assoc]

/-- The vertical identity equation ends in homology of the original single object,
using the native exact-single comparison. The higher identity direct image is
not identified with the identity functor in positive degree. -/
theorem higherBaseChangeMap_vId {S S' : Scheme.{u}}
    [HasDerivedCategory.{wVIdS} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{wVIdS'} (AbelianSheaf.{u, u + 1} S')]
    (g : S' ⟶ S) (e : 𝟙 S' ≫ g = g ≫ 𝟙 S) (q : ℕ)
    (F : AbelianSheaf.{u, u + 1} S) :
    (higherBaseChangeSourceIso (𝟙 S) g q).hom.app F ≫
        (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ)).map
          ((derivedInverseImage g).map ((derivedDirectImageIdIso S).hom.app
            ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} S) 0).obj F))) ≫
        (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ)).map
          (((inverseImage g).rightDerivedFunctorPlusSingleIso 0).hom.app F) =
      (higherBaseChangeMap (𝟙 S) (𝟙 S') g g e q).app F ≫
        (higherBaseChangeTargetIso (𝟙 S') g q).inv.app F ≫
        (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ)).map
          ((derivedDirectImageIdIso S').hom.app ((derivedInverseImage g).obj
            ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} S) 0).obj F))) ≫
        (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ)).map
          (((inverseImage g).rightDerivedFunctorPlusSingleIso 0).hom.app F) := by
  have h := congrArg (fun k => k ≫
    (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ)).map
      (((inverseImage g).rightDerivedFunctorPlusSingleIso 0).hom.app F))
    (higherBaseChangeMap_vId_homology g e q F)
  simpa only [Category.assoc] using h


end HigherVerticalIdentityAppend

end AlgebraicGeometry.Scheme.EtaleCohomology

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
attribute [local instance] hasSheafifyLarge
universe u wHC0 wHC1 wHC2 wHC3 wHC4 wHC5

/-- Whole factorization of the actual higher map with its original target removed. -/
theorem higherBaseChangeMap_target_inv_whole
    {X S X' S' : Scheme.{u}}
    [HasDerivedCategory.{wHC0} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{wHC1} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{wHC2} (AbelianSheaf.{u, u + 1} X')]
    [HasDerivedCategory.{wHC3} (AbelianSheaf.{u, u + 1} S')]
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) (q : ℕ) :
    higherBaseChangeMap f f' g g' h q ≫ (higherBaseChangeTargetIso f' g' q).inv =
      (higherBaseChangeSourceIso f g q).hom ≫
        Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0)
          (Functor.whiskerRight (derivedBaseChangeMap f f' g g' h)
            (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ))) :=
  nativeTransport_target_inverse (higherBaseChangeSourceIso f g q)
    (higherBaseChangeTargetIso f' g' q) _ (higherBaseChangeMap f f' g g' h q)
    (higherBaseChangeMap_eq_transport f f' g g' h q)

/-- Whole native target comparison factorization before a coefficient is chosen. -/
theorem higherBaseChangeTargetIso_inv_whole_factor
    {S X X' : Scheme.{u}}
    [HasDerivedCategory.{wHC0} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{wHC1} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{wHC2} (AbelianSheaf.{u, u + 1} X')]
    (f : X' ⟶ S) (g : X' ⟶ X) (q : ℕ) :
    (higherBaseChangeTargetIso f g q).inv =
      Functor.whiskerLeft (inverseImage g) (higherDirectImageIso f q).hom ≫
        Functor.whiskerRight ((inverseImage g).rightDerivedFunctorPlusSingleIso 0).inv
          (derivedDirectImage f ⋙
            DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) (q : ℤ)) := by
  apply NatTrans.ext
  funext F
  exact higherBaseChangeTargetIso_inv_app f g q F

/-- Whole native source comparison factorization before a coefficient is chosen. -/
theorem higherBaseChangeSourceIso_hom_whole_factor
    {X S S' : Scheme.{u}}
    [HasDerivedCategory.{wHC0} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{wHC1} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{wHC2} (AbelianSheaf.{u, u + 1} S')]
    (f : X ⟶ S) (g : S' ⟶ S) (q : ℕ) :
    (higherBaseChangeSourceIso f g q).hom =
      Functor.whiskerRight (higherDirectImageIso f q).hom (inverseImage g) ≫
        Functor.whiskerLeft
          (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0 ⋙ derivedDirectImage f)
          ((inverseImage g).rightDerivedFunctorPlusHomologyIso (q : ℤ)).inv := by
  apply NatTrans.ext
  funext F
  exact higherBaseChangeSourceIso_hom_app f g q F

/-- The native single functor with the fixed large sheaf universe. -/
abbrev higherHorizontalSingle (X : Scheme.{u})
    [HasDerivedCategory.{wHC0} (AbelianSheaf.{u, u + 1} X)] :
    AbelianSheaf.{u, u + 1} X ⥤ DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X) :=
  DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0

/-- Native homology with the same fixed large sheaf universe. -/
abbrev higherHorizontalHomology (S : Scheme.{u})
    [HasDerivedCategory.{wHC0} (AbelianSheaf.{u, u + 1} S)] (q : ℕ) :
    DerivedCategory.Plus (AbelianSheaf.{u, u + 1} S) ⥤ AbelianSheaf.{u, u + 1} S :=
  DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) (q : ℤ)

variable {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}}
  [HasDerivedCategory.{wHC0} (AbelianSheaf.{u, u + 1} X₀)]
  [HasDerivedCategory.{wHC1} (AbelianSheaf.{u, u + 1} X₁)]
  [HasDerivedCategory.{wHC2} (AbelianSheaf.{u, u + 1} X₂)]
  [HasDerivedCategory.{wHC3} (AbelianSheaf.{u, u + 1} S₀)]
  [HasDerivedCategory.{wHC4} (AbelianSheaf.{u, u + 1} S₁)]
  [HasDerivedCategory.{wHC5} (AbelianSheaf.{u, u + 1} S₂)]
  (f₀ : X₀ ⟶ S₀) (f₁ : X₁ ⟶ S₁) (f₂ : X₂ ⟶ S₂)
  (g₁ : S₁ ⟶ S₀) (g₂ : S₂ ⟶ S₁) (h₁ : X₁ ⟶ X₀) (h₂ : X₂ ⟶ X₁)
  (e₁ : f₁ ≫ g₁ = h₁ ≫ f₀) (e₂ : f₂ ≫ g₂ = h₂ ≫ f₁)
  (e : f₂ ≫ (g₂ ≫ g₁) = (h₂ ≫ h₁) ≫ f₀) (q : ℕ)

local notation "J₀" => higherHorizontalSingle X₀
local notation "H₁" => higherHorizontalHomology S₁ q
local notation "H₂" => higherHorizontalHomology S₂ q
local notation "R₀" => derivedDirectImage f₀
local notation "R₁" => derivedDirectImage f₁
local notation "R₂" => derivedDirectImage f₂
local notation "D₁" => derivedInverseImage g₁
local notation "D₂" => derivedInverseImage g₂
local notation "E₁" => derivedInverseImage h₁
local notation "E₂" => derivedInverseImage h₂
local notation "G₁" => inverseImage g₁
local notation "G₂" => inverseImage g₂
local notation "L₁" => inverseImage h₁
local notation "L₂" => inverseImage h₂
local notation "V₀" => higherDirectImage f₀ q
local notation "V₁" => higherDirectImage f₁ q
local notation "V₂" => higherDirectImage f₂ q

/-- Canonical whole functor data. All comparison isomorphisms are the original
native NatIsos, not isomorphisms reconstructed from coefficient components. -/
def higherHorizontalWholeLadder :
    HigherPastingLadder (AbelianSheaf.{u, u + 1} X₀ ⥤ AbelianSheaf.{u, u + 1} S₂) :=
  HigherPastingLadder.ofHigherExchange
    (inverseImageComp g₁ g₂)
    (derivedInverseImageCompIso g₁ g₂)
    (inverseImageComp h₁ h₂)
    (derivedInverseImageCompIso h₁ h₂)
    (derivedBaseChangeMap f₀ f₁ g₁ h₁ e₁)
    (derivedBaseChangeMap f₁ f₂ g₂ h₂ e₂)
    (derivedBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e)
    (higherBaseChangeMap f₀ f₁ g₁ h₁ e₁ q)
    (higherBaseChangeMap f₁ f₂ g₂ h₂ e₂ q)
    (higherBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e q)
    (higherBaseChangeSourceIso f₀ g₁ q)
    (higherBaseChangeTargetIso f₁ h₁ q)
    (higherBaseChangeTargetIso f₂ h₂ q)
    (higherBaseChangeSourceIso f₀ (g₂ ≫ g₁) q)
    (higherBaseChangeTargetIso f₂ (h₂ ≫ h₁) q)
    ((inverseImage g₂).rightDerivedFunctorPlusHomologyIso (q : ℤ))
    ((inverseImage h₁).rightDerivedFunctorPlusSingleIso 0)

local notation "Δ" => higherHorizontalWholeLadder f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e q

/-- The original source composition law, now a whole natural transformation equation. -/
theorem higherHorizontalWholeLadder_source : (Δ).SourceEquation :=
  HigherPastingLadder.ofHigherExchange_source
    (inverseImageComp g₁ g₂)
    (derivedInverseImageCompIso g₁ g₂)
    (inverseImageComp h₁ h₂)
    (derivedInverseImageCompIso h₁ h₂)
    (derivedBaseChangeMap f₀ f₁ g₁ h₁ e₁)
    (derivedBaseChangeMap f₁ f₂ g₂ h₂ e₂)
    (derivedBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e)
    (higherBaseChangeMap f₀ f₁ g₁ h₁ e₁ q)
    (higherBaseChangeMap f₁ f₂ g₂ h₂ e₂ q)
    (higherBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e q)
    (higherBaseChangeSourceIso f₀ g₁ q)
    (higherBaseChangeTargetIso f₁ h₁ q)
    (higherBaseChangeTargetIso f₂ h₂ q)
    (higherBaseChangeSourceIso f₀ (g₂ ≫ g₁) q)
    (higherBaseChangeTargetIso f₂ (h₂ ≫ h₁) q)
    ((inverseImage g₂).rightDerivedFunctorPlusHomologyIso (q : ℤ))
    ((inverseImage h₁).rightDerivedFunctorPlusSingleIso 0)
    (higherBaseChangeSourceIso_comp f₀ g₁ g₂ q)

/-- The outer edge is the actual higher exchange, not a substituted map. -/
theorem higherHorizontalWholeLadder_outer : (Δ).OuterEquation :=
  HigherPastingLadder.ofHigherExchange_outer
    (inverseImageComp g₁ g₂)
    (derivedInverseImageCompIso g₁ g₂)
    (inverseImageComp h₁ h₂)
    (derivedInverseImageCompIso h₁ h₂)
    (derivedBaseChangeMap f₀ f₁ g₁ h₁ e₁)
    (derivedBaseChangeMap f₁ f₂ g₂ h₂ e₂)
    (derivedBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e)
    (higherBaseChangeMap f₀ f₁ g₁ h₁ e₁ q)
    (higherBaseChangeMap f₁ f₂ g₂ h₂ e₂ q)
    (higherBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e q)
    (higherBaseChangeSourceIso f₀ g₁ q)
    (higherBaseChangeTargetIso f₁ h₁ q)
    (higherBaseChangeTargetIso f₂ h₂ q)
    (higherBaseChangeSourceIso f₀ (g₂ ≫ g₁) q)
    (higherBaseChangeTargetIso f₂ (h₂ ≫ h₁) q)
    ((inverseImage g₂).rightDerivedFunctorPlusHomologyIso (q : ℤ))
    ((inverseImage h₁).rightDerivedFunctorPlusSingleIso 0)
    (higherBaseChangeMap_target_inv_whole f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e q)

/-- The final edge is the original exact-single composition law. -/
theorem higherHorizontalWholeLadder_target : (Δ).TargetEquation :=
  HigherPastingLadder.ofHigherExchange_target
    (inverseImageComp g₁ g₂)
    (derivedInverseImageCompIso g₁ g₂)
    (inverseImageComp h₁ h₂)
    (derivedInverseImageCompIso h₁ h₂)
    (derivedBaseChangeMap f₀ f₁ g₁ h₁ e₁)
    (derivedBaseChangeMap f₁ f₂ g₂ h₂ e₂)
    (derivedBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e)
    (higherBaseChangeMap f₀ f₁ g₁ h₁ e₁ q)
    (higherBaseChangeMap f₁ f₂ g₂ h₂ e₂ q)
    (higherBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e q)
    (higherBaseChangeSourceIso f₀ g₁ q)
    (higherBaseChangeTargetIso f₁ h₁ q)
    (higherBaseChangeTargetIso f₂ h₂ q)
    (higherBaseChangeSourceIso f₀ (g₂ ≫ g₁) q)
    (higherBaseChangeTargetIso f₂ (h₂ ≫ h₁) q)
    ((inverseImage g₂).rightDerivedFunctorPlusHomologyIso (q : ℤ))
    ((inverseImage h₁).rightDerivedFunctorPlusSingleIso 0)
    (higherBaseChangeTargetIso_comp f₂ h₁ h₂ q)

/-- Native first whole edge in the canonical coefficient convention, independently of the ladder. -/
theorem higherHorizontalFirst_whole :
    Functor.whiskerRight (higherBaseChangeMap f₀ f₁ g₁ h₁ e₁ q) G₂ ≫
        (Functor.whiskerRight (higherBaseChangeTargetIso f₁ h₁ q).inv G₂ ≫
          Functor.whiskerLeft (J₀ ⋙ E₁ ⋙ R₁)
            ((inverseImage g₂).rightDerivedFunctorPlusHomologyIso (q : ℤ)).inv) =
      (Functor.whiskerRight (higherBaseChangeSourceIso f₀ g₁ q).hom G₂ ≫
        Functor.whiskerLeft (J₀ ⋙ R₀ ⋙ D₁)
          ((inverseImage g₂).rightDerivedFunctorPlusHomologyIso (q : ℤ)).inv) ≫
        Functor.whiskerLeft J₀ (Functor.whiskerRight
          (Functor.whiskerRight (derivedBaseChangeMap f₀ f₁ g₁ h₁ e₁) D₂) H₂) :=
  mapped_horizontal_first_canonical J₀ H₁ H₂ G₂ D₂
    ((inverseImage g₂).rightDerivedFunctorPlusHomologyIso (q : ℤ))
    (derivedBaseChangeMap f₀ f₁ g₁ h₁ e₁)
    (higherBaseChangeSourceIso f₀ g₁ q) (higherBaseChangeTargetIso f₁ h₁ q).symm
    (higherBaseChangeMap f₀ f₁ g₁ h₁ e₁ q)
    (higherBaseChangeMap_target_inv_whole f₀ f₁ g₁ h₁ e₁ q)

/-- Native second whole edge retains the original nested coefficient whisker. -/
theorem higherHorizontalSecond_whole :
    Functor.whiskerLeft L₁ (higherBaseChangeMap f₁ f₂ g₂ h₂ e₂ q) ≫
        (Functor.whiskerLeft L₁ (higherBaseChangeTargetIso f₂ h₂ q).inv ≫
          Functor.whiskerRight ((inverseImage h₁).rightDerivedFunctorPlusSingleIso 0).inv
            (E₂ ⋙ R₂ ⋙ H₂)) =
      (Functor.whiskerRight (higherBaseChangeTargetIso f₁ h₁ q).inv G₂ ≫
        Functor.whiskerLeft ((J₀ ⋙ E₁) ⋙ R₁)
          ((inverseImage g₂).rightDerivedFunctorPlusHomologyIso (q : ℤ)).inv) ≫
        Functor.whiskerLeft J₀ (Functor.whiskerRight
          (Functor.whiskerLeft E₁ (derivedBaseChangeMap f₁ f₂ g₂ h₂ e₂)) H₂) :=
  mapped_horizontal_second_native J₀ E₁ L₁ (higherHorizontalSingle X₁) H₁ H₂ G₂ D₂
    ((inverseImage g₂).rightDerivedFunctorPlusHomologyIso (q : ℤ))
    R₁ (E₂ ⋙ R₂) (derivedBaseChangeMap f₁ f₂ g₂ h₂ e₂)
    ((inverseImage h₁).rightDerivedFunctorPlusSingleIso 0).inv
    (higherBaseChangeTargetIso f₁ h₁ q).symm
    (higherDirectImageIso f₁ q) (higherBaseChangeSourceIso f₁ g₂ q)
    (higherBaseChangeTargetIso_inv_whole_factor f₁ h₁ q)
    (higherBaseChangeSourceIso_hom_whole_factor f₁ g₂ q)
    (higherBaseChangeTargetIso f₂ h₂ q).symm
    (higherBaseChangeMap f₁ f₂ g₂ h₂ e₂ q)
    (higherBaseChangeMap_target_inv_whole f₁ f₂ g₂ h₂ e₂ q)

/-- Homology of the accepted native derived path in the original coefficient convention. -/
theorem derivedHorizontalHomology_whole :
    Functor.whiskerLeft J₀ (Functor.whiskerRight
        (Functor.whiskerLeft R₀ (derivedInverseImageCompIso g₁ g₂).hom) H₂) ≫
      Functor.whiskerLeft J₀ (Functor.whiskerRight
        (Functor.whiskerRight (derivedBaseChangeMap f₀ f₁ g₁ h₁ e₁) D₂) H₂) ≫
      Functor.whiskerLeft J₀ (Functor.whiskerRight
        (Functor.whiskerLeft E₁ (derivedBaseChangeMap f₁ f₂ g₂ h₂ e₂)) H₂) =
    Functor.whiskerLeft J₀ (Functor.whiskerRight
        (derivedBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e) H₂) ≫
      Functor.whiskerLeft J₀ (Functor.whiskerRight
        (Functor.whiskerRight (derivedInverseImageCompIso h₁ h₂).hom R₂) H₂) :=
  whole_mapped_pasting_single J₀ H₂
    (Functor.whiskerLeft R₀ (derivedInverseImageCompIso g₁ g₂).hom)
    (Functor.whiskerRight (derivedBaseChangeMap f₀ f₁ g₁ h₁ e₁) D₂)
    (Functor.whiskerLeft E₁ (derivedBaseChangeMap f₁ f₂ g₂ h₂ e₂))
    (derivedBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e)
    (Functor.whiskerRight (derivedInverseImageCompIso h₁ h₂).hom R₂)
    (derivedBaseChangeMap_hComp f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e)

/-- The accepted native first edge supplies the ladder's first compatibility. -/
theorem higherHorizontalWholeLadder_first : (Δ).FirstEquation :=
  HigherPastingLadder.ofHigherExchange_first
    (inverseImageComp g₁ g₂)
    (derivedInverseImageCompIso g₁ g₂)
    (inverseImageComp h₁ h₂)
    (derivedInverseImageCompIso h₁ h₂)
    (derivedBaseChangeMap f₀ f₁ g₁ h₁ e₁)
    (derivedBaseChangeMap f₁ f₂ g₂ h₂ e₂)
    (derivedBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e)
    (higherBaseChangeMap f₀ f₁ g₁ h₁ e₁ q)
    (higherBaseChangeMap f₁ f₂ g₂ h₂ e₂ q)
    (higherBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e q)
    (higherBaseChangeSourceIso f₀ g₁ q)
    (higherBaseChangeTargetIso f₁ h₁ q)
    (higherBaseChangeTargetIso f₂ h₂ q)
    (higherBaseChangeSourceIso f₀ (g₂ ≫ g₁) q)
    (higherBaseChangeTargetIso f₂ (h₂ ≫ h₁) q)
    ((inverseImage g₂).rightDerivedFunctorPlusHomologyIso (q : ℤ))
    ((inverseImage h₁).rightDerivedFunctorPlusSingleIso 0)
    (higherBaseChangeMap_target_inv_whole f₀ f₁ g₁ h₁ e₁ q)

/-- The accepted native second edge supplies the ladder's second compatibility. -/
theorem higherHorizontalWholeLadder_second : (Δ).SecondEquation :=
  HigherPastingLadder.ofHigherExchange_second
    (inverseImageComp g₁ g₂)
    (derivedInverseImageCompIso g₁ g₂)
    (inverseImageComp h₁ h₂)
    (derivedInverseImageCompIso h₁ h₂)
    (derivedBaseChangeMap f₀ f₁ g₁ h₁ e₁)
    (derivedBaseChangeMap f₁ f₂ g₂ h₂ e₂)
    (derivedBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e)
    (higherBaseChangeMap f₀ f₁ g₁ h₁ e₁ q)
    (higherBaseChangeMap f₁ f₂ g₂ h₂ e₂ q)
    (higherBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e q)
    (higherBaseChangeSourceIso f₀ g₁ q)
    (higherBaseChangeTargetIso f₁ h₁ q)
    (higherBaseChangeTargetIso f₂ h₂ q)
    (higherBaseChangeSourceIso f₀ (g₂ ≫ g₁) q)
    (higherBaseChangeTargetIso f₂ (h₂ ≫ h₁) q)
    ((inverseImage g₂).rightDerivedFunctorPlusHomologyIso (q : ℤ))
    ((inverseImage h₁).rightDerivedFunctorPlusSingleIso 0)
    (higherDirectImageIso f₁ q)
    (higherBaseChangeSourceIso f₁ g₂ q)
    (higherBaseChangeTargetIso_inv_whole_factor f₁ h₁ q)
    (higherBaseChangeSourceIso_hom_whole_factor f₁ g₂ q)
    (higherBaseChangeMap_target_inv_whole f₁ f₂ g₂ h₂ e₂ q)

/-- The accepted mapped derived path supplies the ladder's upper equation. -/
theorem higherHorizontalWholeLadder_derived : (Δ).DerivedEquation :=
  HigherPastingLadder.ofHigherExchange_derived
    (inverseImageComp g₁ g₂)
    (derivedInverseImageCompIso g₁ g₂)
    (inverseImageComp h₁ h₂)
    (derivedInverseImageCompIso h₁ h₂)
    (derivedBaseChangeMap f₀ f₁ g₁ h₁ e₁)
    (derivedBaseChangeMap f₁ f₂ g₂ h₂ e₂)
    (derivedBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e)
    (higherBaseChangeMap f₀ f₁ g₁ h₁ e₁ q)
    (higherBaseChangeMap f₁ f₂ g₂ h₂ e₂ q)
    (higherBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e q)
    (higherBaseChangeSourceIso f₀ g₁ q)
    (higherBaseChangeTargetIso f₁ h₁ q)
    (higherBaseChangeTargetIso f₂ h₂ q)
    (higherBaseChangeSourceIso f₀ (g₂ ≫ g₁) q)
    (higherBaseChangeTargetIso f₂ (h₂ ≫ h₁) q)
    ((inverseImage g₂).rightDerivedFunctorPlusHomologyIso (q : ℤ))
    ((inverseImage h₁).rightDerivedFunctorPlusSingleIso 0)
    (derivedBaseChangeMap_hComp f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e)

/-- Whole all-degree pasting before any coefficient specialization. -/
theorem higherHorizontalWholeLadder_pasting : (Δ).HigherEquation :=
  HigherPastingLadder.ofHigherExchange_pasting
    (inverseImageComp g₁ g₂)
    (derivedInverseImageCompIso g₁ g₂)
    (inverseImageComp h₁ h₂)
    (derivedInverseImageCompIso h₁ h₂)
    (derivedBaseChangeMap f₀ f₁ g₁ h₁ e₁)
    (derivedBaseChangeMap f₁ f₂ g₂ h₂ e₂)
    (derivedBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e)
    (higherBaseChangeMap f₀ f₁ g₁ h₁ e₁ q)
    (higherBaseChangeMap f₁ f₂ g₂ h₂ e₂ q)
    (higherBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e q)
    (higherBaseChangeSourceIso f₀ g₁ q)
    (higherBaseChangeTargetIso f₁ h₁ q)
    (higherBaseChangeTargetIso f₂ h₂ q)
    (higherBaseChangeSourceIso f₀ (g₂ ≫ g₁) q)
    (higherBaseChangeTargetIso f₂ (h₂ ≫ h₁) q)
    ((inverseImage g₂).rightDerivedFunctorPlusHomologyIso (q : ℤ))
    ((inverseImage h₁).rightDerivedFunctorPlusSingleIso 0)
    (higherBaseChangeSourceIso_comp f₀ g₁ g₂ q)
    (higherBaseChangeTargetIso_comp f₂ h₁ h₂ q)
    (higherDirectImageIso f₁ q)
    (higherBaseChangeSourceIso f₁ g₂ q)
    (higherBaseChangeTargetIso_inv_whole_factor f₁ h₁ q)
    (higherBaseChangeSourceIso_hom_whole_factor f₁ g₂ q)
    (higherBaseChangeMap_target_inv_whole f₀ f₁ g₁ h₁ e₁ q)
    (higherBaseChangeMap_target_inv_whole f₁ f₂ g₂ h₂ e₂ q)
    (higherBaseChangeMap_target_inv_whole f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e q)
    (derivedBaseChangeMap_hComp f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e)

omit [HasDerivedCategory.{wHC0} (AbelianSheaf.{u, u + 1} X₀)]
  [HasDerivedCategory.{wHC1} (AbelianSheaf.{u, u + 1} X₁)]
  [HasDerivedCategory.{wHC2} (AbelianSheaf.{u, u + 1} X₂)]
  [HasDerivedCategory.{wHC3} (AbelianSheaf.{u, u + 1} S₀)]
  [HasDerivedCategory.{wHC4} (AbelianSheaf.{u, u + 1} S₁)]
  [HasDerivedCategory.{wHC5} (AbelianSheaf.{u, u + 1} S₂)] in
/-- Horizontal pasting of the actual higher exchange with native comparisons. -/
theorem higherBaseChangeMap_hComp (F : AbelianSheaf.{u, u + 1} X₀) :
    MappedHorizontalPastingEquation G₂
      ((inverseImageComp g₁ g₂).hom.app ((V₀).obj F))
      ((higherBaseChangeMap f₀ f₁ g₁ h₁ e₁ q).app F)
      ((higherBaseChangeMap f₁ f₂ g₂ h₂ e₂ q).app ((L₁).obj F))
      ((higherBaseChangeMap f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e q).app F)
      ((V₂).map ((inverseImageComp h₁ h₂).hom.app F)) := by
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X₀)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X₁)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X₂)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S₀)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S₁)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S₂)
  exact HigherPastingLadder.pasting_app (Δ)
    (higherHorizontalWholeLadder_pasting f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e q) F

/-- Horizontal pasting of the original transports in the six independently selected models. -/
theorem higherBaseChangeMapFromDerived_hComp (F : AbelianSheaf.{u, u + 1} X₀) :
    MappedHorizontalPastingEquation G₂
      ((inverseImageComp g₁ g₂).hom.app ((V₀).obj F))
      ((higherBaseChangeMapFromDerived f₀ f₁ g₁ h₁ e₁ q).app F)
      ((higherBaseChangeMapFromDerived f₁ f₂ g₂ h₂ e₂ q).app ((L₁).obj F))
      ((higherBaseChangeMapFromDerived f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e q).app F)
      ((V₂).map ((inverseImageComp h₁ h₂).hom.app F)) := by
  simpa only [higherBaseChangeMapFromDerived_eq] using
    higherBaseChangeMap_hComp f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e q F

end AlgebraicGeometry.Scheme.EtaleCohomology
