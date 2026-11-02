/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ThreeFactorSquare

public import Aglib.CategoryTheory.Adjunction.Mates.SourceCoherence

public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.Adjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Identity

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.TransportedComposition
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Transport
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.TransportedIdentity
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.DerivedConjugacy
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.IdentityConjugacy

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.SingleSquare
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.WholeNormalization
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.IdentityNormalization
public import
Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.CoherenceRawNormalization

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HigherComparisons
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.SingleCoherence
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HomologyCoherence

/-!
# Original identity and composition comparisons for derived étale images

The comparisons use the native sheaf comparisons and the installed
right-derived identity/composition comparisons. Direct-image composition
uses preservation of injectives, not an assertion that direct image is exact.
The source inverse-image squares, their exact/single comparisons, and their
identity and pasting coherence are proved here before taking adjunction mates.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w w' w''

attribute [local instance] hasSheafifyLarge

section Identity

variable (X : Scheme.{u}) [HasDerivedCategory.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The installed inverse image of the identity is canonically the identity. -/
def derivedInverseImageIdIso :
    derivedInverseImage (𝟙 X) ≅ 𝟭 (DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X)) :=
  (inverseImage (𝟙 X)).rightDerivedFunctorPlusIso (inverseImageId X) ≪≫
    Functor.rightDerivedFunctorPlusIdIso (AbelianSheaf.{u, u + 1} X)

/-- The installed direct image of the identity is canonically the identity. -/
def derivedDirectImageIdIso :
    derivedDirectImage (𝟙 X) ≅ 𝟭 (DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X)) :=
  (directImage (𝟙 X)).rightDerivedFunctorPlusIso (directImageIdIso X) ≪≫
    Functor.rightDerivedFunctorPlusIdIso (AbelianSheaf.{u, u + 1} X)

/-- The inverse-image identity comparison retains the original localization unit. -/
@[reassoc]
theorem derivedInverseImageIdIso_unit
    (K : CochainComplex.Plus (AbelianSheaf.{u, u + 1} X)) :
    (inverseImage (𝟙 X)).rightDerivedFunctorPlusUnit.app K ≫
        (derivedInverseImageIdIso X).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (inverseImageId X)).hom.app K ≫
          (Functor.mapCochainComplexPlusIdIso (AbelianSheaf.{u, u + 1} X)).hom.app K) := by
  have h := (inverseImage (𝟙 X)).rightDerivedFunctorPlusIso_hom_app (inverseImageId X) K
  change _ ≫ (_ ≫ _) = _
  rw [← Category.assoc, h, Category.assoc, Functor.rightDerivedFunctorPlusIdIso_unit,
    ← Functor.map_comp]

/-- The direct-image identity comparison retains the original localization unit. -/
@[reassoc]
theorem derivedDirectImageIdIso_unit
    (K : CochainComplex.Plus (AbelianSheaf.{u, u + 1} X)) :
    (directImage (𝟙 X)).rightDerivedFunctorPlusUnit.app K ≫
        (derivedDirectImageIdIso X).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
        ((NatIso.mapCochainComplexPlus (directImageIdIso X)).hom.app K ≫
          (Functor.mapCochainComplexPlusIdIso (AbelianSheaf.{u, u + 1} X)).hom.app K) := by
  have h := (directImage (𝟙 X)).rightDerivedFunctorPlusIso_hom_app (directImageIdIso X) K
  change _ ≫ (_ ≫ _) = _
  rw [← Category.assoc, h, Category.assoc, Functor.rightDerivedFunctorPlusIdIso_unit,
    ← Functor.map_comp]

end Identity

section Composition

variable {X S T : Scheme.{u}}
  [HasDerivedCategory.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{w'} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{w''} (AbelianSheaf.{u, u + 1} T)]
  (f : S ⟶ X) (g : T ⟶ S)

/-- Derived inverse images compose through the original exact inverse-image comparison. -/
def derivedInverseImageCompIso :
    derivedInverseImage (g ≫ f) ≅ derivedInverseImage f ⋙ derivedInverseImage g :=
  (inverseImage (g ≫ f)).rightDerivedFunctorPlusIso (inverseImageComp f g) ≪≫
    Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology (inverseImage f) (inverseImage g)

/-- Derived direct-image composition, oriented from the image of the composite morphism. -/
def derivedDirectImageCompIso :
    derivedDirectImage (g ≫ f) ≅ derivedDirectImage g ⋙ derivedDirectImage f :=
  (directImage (g ≫ f)).rightDerivedFunctorPlusIso (directImageCompIso f g).symm ≪≫
    Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives (directImage g) (directImage f)

/-- The direct-image comparison retains the original sheaf comparison and both original
right-derived units. -/
@[reassoc]
theorem derivedDirectImageCompIso_unit
    (K : CochainComplex.Plus (AbelianSheaf.{u, u + 1} T)) :
    (directImage (g ≫ f)).rightDerivedFunctorPlusUnit.app K ≫
        (derivedDirectImageCompIso f g).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
          ((NatIso.mapCochainComplexPlus (directImageCompIso f g).symm).hom.app K) ≫
        (directImage f).rightDerivedFunctorPlusUnit.app
          ((directImage g).mapCochainComplexPlus.obj K) ≫
        (derivedDirectImage f).map ((directImage g).rightDerivedFunctorPlusUnit.app K) := by
  dsimp only [derivedDirectImageCompIso, Iso.trans_hom, NatTrans.comp_app]
  rw [← Category.assoc, Functor.rightDerivedFunctorPlusIso_hom_app,
    Category.assoc, Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app]

/-- The inverse-image comparison retains the original sheaf comparison and both original
right-derived units of the exact inverse images. -/
@[reassoc]
theorem derivedInverseImageCompIso_unit
    (K : CochainComplex.Plus (AbelianSheaf.{u, u + 1} X)) :
    (inverseImage (g ≫ f)).rightDerivedFunctorPlusUnit.app K ≫
        (derivedInverseImageCompIso f g).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
          ((NatIso.mapCochainComplexPlus (inverseImageComp f g)).hom.app K) ≫
        (inverseImage g).rightDerivedFunctorPlusUnit.app
          ((inverseImage f).mapCochainComplexPlus.obj K) ≫
        (derivedInverseImage g).map ((inverseImage f).rightDerivedFunctorPlusUnit.app K) := by
  dsimp only [derivedInverseImageCompIso, Iso.trans_hom, NatTrans.comp_app]
  rw [← Category.assoc, Functor.rightDerivedFunctorPlusIso_hom_app,
    Category.assoc, Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology_hom_app]

end Composition

section Coherence

universe w₁ w₂ w₃ w₄

variable {X S T V : Scheme.{u}}
  [HasDerivedCategory.{w₁} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{w₂} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{w₃} (AbelianSheaf.{u, u + 1} T)]
  [HasDerivedCategory.{w₄} (AbelianSheaf.{u, u + 1} V)]
  (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T)

/-- Derived inverse images retain the actual original associativity comparison,
including equality transport for the two parenthesizations of the scheme morphism. -/
theorem derivedInverseImageCompIso_assoc :
    derivedInverseImageCompIso f (h ≫ g) ≪≫
        Functor.isoWhiskerLeft (derivedInverseImage f) (derivedInverseImageCompIso g h) =
      eqToIso (congrArg (fun k : V ⟶ X => derivedInverseImage k) (Category.assoc h g f)) ≪≫
        derivedInverseImageCompIso (g ≫ f) h ≪≫
        Functor.isoWhiskerRight (derivedInverseImageCompIso f g) (derivedInverseImage h) ≪≫
        Functor.associator (derivedInverseImage f) (derivedInverseImage g)
          (derivedInverseImage h) := by
  let e : inverseImage ((h ≫ g) ≫ f) ≅ inverseImage (h ≫ (g ≫ f)) :=
    eqToIso (congrArg (fun k : V ⟶ X => inverseImage k) (Category.assoc h g f))
  have hc := Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology_transportAssoc
    (inverseImage f) (inverseImage g) (inverseImage h)
    (inverseImage (g ≫ f)) (inverseImage (h ≫ g)) (inverseImage ((h ≫ g) ≫ f))
    (inverseImageComp f (h ≫ g)) (inverseImageComp g h)
    (e ≪≫ inverseImageComp (g ≫ f) h) (inverseImageComp f g)
    (by simpa only [e, Iso.trans_assoc] using inverseImageComp_assoc f g h)
  simpa only [derivedInverseImageCompIso, derivedInverseImage, e,
    Functor.rightDerivedFunctorPlusIso_trans, Functor.rightDerivedFunctorPlusIso_eqToIso,
    Iso.trans_assoc] using hc

/-- Inverse-oriented ordinary coherence, used only to lift the native direct-image comparison. -/
private theorem directImageCompIso_assoc_inv_forDerived {X S T V : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T) :
    (directImageCompIso (g ≫ f) h).symm ≪≫
        Functor.isoWhiskerLeft (directImage h) (directImageCompIso f g).symm =
      eqToIso (congrArg (fun k : V ⟶ X => directImage k) (Category.assoc h g f).symm) ≪≫
        (directImageCompIso f (h ≫ g)).symm ≪≫
        Functor.isoWhiskerRight (directImageCompIso g h).symm (directImage f) ≪≫
        Functor.associator (directImage h) (directImage g) (directImage f) := by
  apply Iso.symm_bijective.injective
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simpa only [Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp, eqToIso.inv, eqToIso.hom, eqToHom_app,
    Category.assoc, Functor.comp_obj] using (directImageCompIso_assoc_app f g h K).symm

/-- The actual derived direct-image comparisons associate, including the scheme transport. -/
theorem derivedDirectImageCompIso_assoc :
    derivedDirectImageCompIso (g ≫ f) h ≪≫
        Functor.isoWhiskerLeft (derivedDirectImage h) (derivedDirectImageCompIso f g) =
      eqToIso (congrArg (fun k : V ⟶ X => derivedDirectImage k)
        (Category.assoc h g f).symm) ≪≫
        derivedDirectImageCompIso f (h ≫ g) ≪≫
        Functor.isoWhiskerRight (derivedDirectImageCompIso g h) (derivedDirectImage f) ≪≫
        Functor.associator (derivedDirectImage h) (derivedDirectImage g)
          (derivedDirectImage f) := by
  let e : directImage (h ≫ (g ≫ f)) ≅ directImage ((h ≫ g) ≫ f) :=
    eqToIso (congrArg (fun k : V ⟶ X => directImage k) (Category.assoc h g f).symm)
  have hc := Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives_transportAssoc
    (directImage h) (directImage g) (directImage f)
    (directImage (h ≫ g)) (directImage (g ≫ f)) (directImage (h ≫ (g ≫ f)))
    (directImageCompIso (g ≫ f) h).symm (directImageCompIso f g).symm
    (e ≪≫ (directImageCompIso f (h ≫ g)).symm) (directImageCompIso g h).symm
    (by simpa only [e, Iso.trans_assoc] using directImageCompIso_assoc_inv_forDerived f g h)
  simpa only [derivedDirectImageCompIso, derivedDirectImage, e,
    Functor.rightDerivedFunctorPlusIso_trans, Functor.rightDerivedFunctorPlusIso_eqToIso,
    Iso.trans_assoc] using hc

end Coherence

section UnitCoherence

variable {X S : Scheme.{u}}
  [HasDerivedCategory.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{w'} (AbelianSheaf.{u, u + 1} S)] (f : S ⟶ X)

/-- The derived inverse image comparison satisfies its original comp_id unit law. -/
theorem derivedInverseImageCompIso_comp_id :
    derivedInverseImageCompIso f (𝟙 S) ≪≫
        Functor.isoWhiskerLeft (derivedInverseImage f) (derivedInverseImageIdIso S) ≪≫
        Functor.rightUnitor (derivedInverseImage f) =
      eqToIso (congrArg (fun k : S ⟶ X => derivedInverseImage k) (Category.id_comp f)) := by
  have hc := Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology_transportRightUnit
    (inverseImage f) (inverseImage ((𝟙 S) ≫ f)) (inverseImage (𝟙 S))
    (inverseImageComp f (𝟙 S)) (inverseImageId S)
  rw [inverseImageComp_comp_id] at hc
  simpa only [derivedInverseImageCompIso, derivedInverseImageIdIso, derivedInverseImage,
    Functor.rightDerivedFunctorPlusIso_eqToIso] using hc

/-- The derived inverse image comparison satisfies its original id_comp unit law. -/
theorem derivedInverseImageCompIso_id_comp :
    derivedInverseImageCompIso (𝟙 X) f ≪≫
        Functor.isoWhiskerRight (derivedInverseImageIdIso X) (derivedInverseImage f) ≪≫
        Functor.leftUnitor (derivedInverseImage f) =
      eqToIso (congrArg (fun k : S ⟶ X => derivedInverseImage k) (Category.comp_id f)) := by
  have hc := Functor.rightDerivedFunctorPlusCompIsoOfPreservesHomology_transportLeftUnit
    (inverseImage f) (inverseImage (f ≫ 𝟙 X)) (inverseImage (𝟙 X))
    (inverseImageComp (𝟙 X) f) (inverseImageId X)
  rw [inverseImageComp_id_comp] at hc
  simpa only [derivedInverseImageCompIso, derivedInverseImageIdIso, derivedInverseImage,
    Functor.rightDerivedFunctorPlusIso_eqToIso] using hc

/-- The derived direct image comparison satisfies its original comp_id unit law. -/
theorem derivedDirectImageCompIso_comp_id :
    derivedDirectImageCompIso f (𝟙 S) ≪≫
        Functor.isoWhiskerRight (derivedDirectImageIdIso S) (derivedDirectImage f) ≪≫
        Functor.leftUnitor (derivedDirectImage f) =
      eqToIso (congrArg (fun k : S ⟶ X => derivedDirectImage k) (Category.id_comp f)) := by
  have hc := Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives_transportLeftUnit
    (directImage f) (directImage ((𝟙 S) ≫ f)) (directImage (𝟙 S))
    (directImageCompIso f (𝟙 S)).symm (directImageIdIso S)
  rw [directImageCompIso_comp_id] at hc
  simpa only [derivedDirectImageCompIso, derivedDirectImageIdIso, derivedDirectImage,
    Functor.rightDerivedFunctorPlusIso_eqToIso] using hc

/-- The derived direct image comparison satisfies its original id_comp unit law. -/
theorem derivedDirectImageCompIso_id_comp :
    derivedDirectImageCompIso (𝟙 X) f ≪≫
        Functor.isoWhiskerLeft (derivedDirectImage f) (derivedDirectImageIdIso X) ≪≫
        Functor.rightUnitor (derivedDirectImage f) =
      eqToIso (congrArg (fun k : S ⟶ X => derivedDirectImage k) (Category.comp_id f)) := by
  have hc := Functor.rightDerivedFunctorPlusCompIsoOfPreservesInjectives_transportRightUnit
    (directImage f) (directImage (f ≫ 𝟙 X)) (directImage (𝟙 X))
    (directImageCompIso (𝟙 X) f).symm (directImageIdIso X)
  rw [directImageCompIso_id_comp] at hc
  simpa only [derivedDirectImageCompIso, derivedDirectImageIdIso, derivedDirectImage,
    Functor.rightDerivedFunctorPlusIso_eqToIso] using hc

end UnitCoherence

section AdjunctionCoherence

variable {X S T : Scheme.{u}}
  [HasDerivedCategory.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{w'} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{w''} (AbelianSheaf.{u, u + 1} T)]
  (f : S ⟶ X) (g : T ⟶ S)

/-- The actual installed composition comparisons are conjugate for the actual derived adjunctions.
This is the compatibility needed to transport base-change pasting, not merely an abstract
existence of a derived adjunction. -/
theorem conjugateEquiv_derivedInverseImageCompIso_hom :
    conjugateEquiv ((derivedImageAdjunction f).comp (derivedImageAdjunction g))
        (derivedImageAdjunction (g ≫ f)) (derivedInverseImageCompIso f g).hom =
      (derivedDirectImageCompIso f g).inv := by
  exact Adjunction.rightDerivedFunctorPlus_conjugate_comp
    (inverseImageAdjunction f) (inverseImageAdjunction g) (inverseImageAdjunction (g ≫ f))
    (inverseImageComp f g) (directImageCompIso f g) (conjugateEquiv_inverseImageComp_hom f g)

end AdjunctionCoherence

section IdentityAdjunctionCoherence

variable (X : Scheme.{u}) [HasDerivedCategory.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The installed derived identity comparisons are conjugate for the actual derived adjunction. -/
theorem conjugateEquiv_derivedInverseImageIdIso_hom :
    conjugateEquiv Adjunction.id (derivedImageAdjunction (𝟙 X))
        (derivedInverseImageIdIso X).hom = (derivedDirectImageIdIso X).inv := by
  exact Adjunction.rightDerivedFunctorPlus_conjugate_id
    (inverseImageAdjunction (𝟙 X)) (inverseImageId X) (directImageIdIso X)
    (conjugateEquiv_inverseImageId_hom X)

end IdentityAdjunctionCoherence

section CompositionHomology

variable {S X Y : Scheme.{u}}
  [HasDerivedCategory.{w} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{w'} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{w''} (AbelianSheaf.{u, u + 1} Y)]
  (f : X ⟶ S) (k : Y ⟶ X) (q : ℕ)

/-- The native R^q of a composite is the homology of the composed derived images,
not the composite of the two separate R^q functors. -/
def higherDirectImageCompHomologyIso :
    higherDirectImage (k ≫ f) q ≅
      DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0 ⋙
        (derivedDirectImage k ⋙ derivedDirectImage f) ⋙
          DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) (q : ℤ) :=
  higherDirectImageIso (k ≫ f) q ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (derivedDirectImageCompIso f k) _)

/-- Objectwise native composition/homology comparison, with the original component maps. -/
def higherDirectImageCompHomologyIsoApp (F : AbelianSheaf.{u, u + 1} Y) :
    (higherDirectImage (k ≫ f) q).obj F ≅
      (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) (q : ℤ)).obj
        ((derivedDirectImage f).obj ((derivedDirectImage k).obj
          ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj F))) :=
  (higherDirectImageIso (k ≫ f) q).app F ≪≫
    (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) (q : ℤ)).mapIso
      ((derivedDirectImageCompIso f k).app
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} Y) 0).obj F))

/-- The objectwise comparison is the component of the native natural isomorphism. -/
theorem higherDirectImageCompHomologyIso_app (F : AbelianSheaf.{u, u + 1} Y) :
    (higherDirectImageCompHomologyIso f k q).app F =
      higherDirectImageCompHomologyIsoApp f k q F := rfl

end CompositionHomology

end AlgebraicGeometry.Scheme.EtaleCohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u wX wS wX' wS'

attribute [local instance] hasSheafifyLarge

section SourceSquare

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
  sourceSquareIso (derivedInverseImageCompIso g f') (derivedInverseImageCompIso f g')
    (eqToIso (congrArg (fun k : X' ⟶ S => derivedInverseImage k) h))

local instance sourceSquareSourceComparisonIsIso :
    IsIso (Functor.rightDerivedFunctorPlusCompComparison (inverseImage g) (inverseImage f')) :=
  Functor.isIso_rightDerivedFunctorPlusCompComparison_of_preservesHomology _ _

local instance sourceSquareTargetComparisonIsIso :
    IsIso (Functor.rightDerivedFunctorPlusCompComparison (inverseImage f) (inverseImage g')) :=
  Functor.isIso_rightDerivedFunctorPlusCompComparison_of_preservesHomology _ _

/-- The original source square equals the installed three-factor comparison. -/
theorem derivedInverseImageSquareIso_eq_threeFactor :
    derivedInverseImageSquareIso f f' g g' h =
      Functor.rightDerivedFunctorPlusThreeFactorIso (inverseImage g) (inverseImage f')
        (inverseImage f) (inverseImage g') (inverseImageSquareIso f f' g g' h) := by
  symm
  have hv := rightDerivedFunctorPlusThreeFactorIso_eq_factored (inverseImage f) (inverseImage g')
    (inverseImage g) (inverseImage f')
    (inverseImage (f' ≫ g)) (inverseImage (g' ≫ f))
    (inverseImageComp g f') (inverseImageComp f g')
    (eqToIso (congrArg (fun k : X' ⟶ S => inverseImage k) h))
  simpa only [derivedInverseImageSquareIso, sourceSquareIso,
    inverseImageSquareIso, derivedInverseImageCompIso,
    Functor.rightDerivedFunctorPlusIso_eqToIso] using hv

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
  simp only [derivedInverseImageSquareIso, sourceSquareIso,
    Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc]
  have hA := congrArg Iso.hom (derivedInverseImageCompIso_id_comp f)
  have hB := congrArg Iso.hom (derivedInverseImageCompIso_comp_id f)
  simp only [Iso.trans_hom] at hA hB
  rw [hB, hA]
  simp only [eqToIso.hom, eqToHom_trans]

/-- The actual derived inverse-image square respects the original exact comparison on
arbitrary bounded-below complexes. The original termwise square is retained literally. -/
theorem derivedInverseImageSquareIso_exactComparison
    (K : CochainComplex.Plus (AbelianSheaf.{u, u + 1} S)) :
    ExactComparisonSquareEquation (inverseImage f) (inverseImage g')
      (inverseImage g) (inverseImage f')
      (TwoSquare.mk _ _ _ _ (inverseImageSquareIso f f' g g' h).hom)
      (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' h).hom) K := by
  rw [derivedInverseImageSquareIso_eq_threeFactor]
  exact rightDerivedFunctorPlusThreeFactorIso_exactComparison (inverseImage f) (inverseImage g')
    (inverseImage g) (inverseImage f') (inverseImageSquareIso f f' g g' h) K

/-- The scheme specialization keeps the shared single-square proposition intact. -/
theorem derivedInverseImageSquareIso_single
    (T : AbelianSheaf.{u, u + 1} S) :
    SingleComparisonSquareEquation (inverseImage f) (inverseImage g')
      (inverseImage g) (inverseImage f')
      (inverseImageSquareIso f f' g g' h).hom
      (derivedInverseImageSquareIso f f' g g' h).hom T := by
  rw [derivedInverseImageSquareIso_eq_threeFactor]
  exact rightDerivedFunctorPlusThreeFactorIso_single (inverseImage f) (inverseImage g')
    (inverseImage g) (inverseImage f') (inverseImageSquareIso f f' g g' h) T

end SourceSquare

universe wb0 wb1 wb2 wb3 wb4 wb5

/-- The original associativity comparison, without evaluating on any sheaf. -/
theorem derivedInverseImageCompIso_assoc_hom {X S T V : Scheme.{u}}
    [HasDerivedCategory.{wb0} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{wb1} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{wb2} (AbelianSheaf.{u, u + 1} T)]
    [HasDerivedCategory.{wb3} (AbelianSheaf.{u, u + 1} V)]
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T) :
    (derivedInverseImageCompIso f (h ≫ g)).hom ≫
        Functor.whiskerLeft (derivedInverseImage f) (derivedInverseImageCompIso g h).hom =
      (eqToIso (congrArg (fun k : V ⟶ X => derivedInverseImage k)
        (Category.assoc h g f))).hom ≫
        (derivedInverseImageCompIso (g ≫ f) h).hom ≫
        Functor.whiskerRight (derivedInverseImageCompIso f g).hom (derivedInverseImage h) ≫
        (Functor.associator (derivedInverseImage f) (derivedInverseImage g)
          (derivedInverseImage h)).hom := by
  have hc := congrArg Iso.hom (derivedInverseImageCompIso_assoc f g h)
  simpa only [Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom] using hc

/-- Equality transport in the second whole inverse-image composition comparison. -/
theorem derivedInverseImageCompIso_eqToHom_right_whole {X S T : Scheme.{u}}
    [HasDerivedCategory.{wb0} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{wb1} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{wb2} (AbelianSheaf.{u, u + 1} T)]
    (f : S ⟶ X) {g g' : T ⟶ S} (e : g = g') :
    (derivedInverseImageCompIso f g).hom ≫
        Functor.whiskerLeft (derivedInverseImage f)
          (eqToHom (congrArg (fun k : T ⟶ S => derivedInverseImage k) e)) =
      eqToHom (congrArg (fun k : T ⟶ X => derivedInverseImage k)
        (congrArg (fun k => k ≫ f) e)) ≫ (derivedInverseImageCompIso f g').hom := by
  subst g'
  simp

/-- Equality transport in the first whole inverse-image composition comparison. -/
theorem derivedInverseImageCompIso_eqToHom_left_whole {X S T : Scheme.{u}}
    [HasDerivedCategory.{wb0} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{wb1} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{wb2} (AbelianSheaf.{u, u + 1} T)]
    {f f' : S ⟶ X} (e : f = f') (g : T ⟶ S) :
    (derivedInverseImageCompIso f g).hom ≫
        Functor.whiskerRight
          (eqToHom (congrArg (fun k : S ⟶ X => derivedInverseImage k) e)) (derivedInverseImage g) =
      eqToHom (congrArg (fun k : T ⟶ X => derivedInverseImage k)
        (congrArg (fun k => g ≫ k) e)) ≫ (derivedInverseImageCompIso f' g).hom := by
  subst f'
  simp

/-- Initial rotation of the actual whole associativity comparison. -/
theorem derivedInverseImageCompIso_assoc_start_whole {X S T V : Scheme.{u}}
    [HasDerivedCategory.{wb0} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{wb1} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{wb2} (AbelianSheaf.{u, u + 1} T)]
    [HasDerivedCategory.{wb3} (AbelianSheaf.{u, u + 1} V)]
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T) :
    (derivedInverseImageCompIso (g ≫ f) h).hom ≫
        (Functor.whiskerRight (derivedInverseImageCompIso f g).hom (derivedInverseImage h) ≫
          (Functor.associator (derivedInverseImage f) (derivedInverseImage g)
          (derivedInverseImage h)).hom) ≫
        Functor.whiskerLeft (derivedInverseImage f) (derivedInverseImageCompIso g h).inv =
      (eqToIso (congrArg (fun k : V ⟶ X => derivedInverseImage k)
        (Category.assoc h g f))).inv ≫ (derivedInverseImageCompIso f (h ≫ g)).hom :=
  exchangeCoherence_rotate_start _ _ _ _ _ _ _
    (Iso.inv_hom_id _) (Iso.hom_inv_id (Functor.isoWhiskerLeft
      (derivedInverseImage f) (derivedInverseImageCompIso g h)))
    (derivedInverseImageCompIso_assoc_hom f g h).symm

/-- Terminal rotation of the actual whole associativity comparison. -/
theorem derivedInverseImageCompIso_assoc_finish_whole {X S T V : Scheme.{u}}
    [HasDerivedCategory.{wb0} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{wb1} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{wb2} (AbelianSheaf.{u, u + 1} T)]
    [HasDerivedCategory.{wb3} (AbelianSheaf.{u, u + 1} V)]
    (f : S ⟶ X) (g : T ⟶ S) (h : V ⟶ T) :
    (derivedInverseImageCompIso (g ≫ f) h).hom ≫
        Functor.whiskerRight (derivedInverseImageCompIso f g).hom (derivedInverseImage h) ≫
        (Functor.associator (derivedInverseImage f) (derivedInverseImage g)
          (derivedInverseImage h)).hom =
      (eqToIso (congrArg (fun k : V ⟶ X => derivedInverseImage k)
        (Category.assoc h g f))).inv ≫
        (derivedInverseImageCompIso f (h ≫ g)).hom ≫
        Functor.whiskerLeft (derivedInverseImage f) (derivedInverseImageCompIso g h).hom :=
  exchangeCoherence_rotate_finish _ _ _ _ (Iso.inv_hom_id _)
    (derivedInverseImageCompIso_assoc_hom f g h).symm

section WholeHorizontal
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

/-- The original functors, source equalities and comparison families. -/
def derivedInverseImageHorizontalSourceData :
    SourceCoherenceData
      (DerivedCategory.Plus (AbelianSheaf.{u, u + 1} S₀))
      (DerivedCategory.Plus (AbelianSheaf.{u, u + 1} S₁))
      (DerivedCategory.Plus (AbelianSheaf.{u, u + 1} S₂))
      (DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X₀))
      (DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X₁))
      (DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X₂))
      (X₂ ⟶ S₀) (X₁ ⟶ S₀) (X₂ ⟶ S₁) where
  F₀ := (derivedInverseImage f₀)
  F₁ := (derivedInverseImage f₁)
  F₂ := (derivedInverseImage f₂)
  G₁ := (derivedInverseImage g₁)
  G₂ := (derivedInverseImage g₂)
  H₁ := (derivedInverseImage h₁)
  H₂ := (derivedInverseImage h₂)
  G₁₂ := (derivedInverseImage (g₂ ≫ g₁))
  H₁₂ := (derivedInverseImage (h₂ ≫ h₁))
  T := fun k => (derivedInverseImage k)
  P := fun k => (derivedInverseImage k)
  Q := fun k => (derivedInverseImage k)
  post := fun k => k ≫ g₁
  pre := fun k => h₂ ≫ k
  a₀ := f₂ ≫ (g₂ ≫ g₁)
  a₅ := (h₂ ≫ h₁) ≫ f₀
  p₀ := f₁ ≫ g₁
  p₁ := h₁ ≫ f₀
  q₀ := f₂ ≫ g₂
  q₁ := h₂ ≫ f₁
  first_eq := e₁
  second_eq := e₂
  start_eq := Category.assoc f₂ g₂ g₁
  middle_eq := Category.assoc h₂ f₁ g₁
  finish_eq := Category.assoc h₂ h₁ f₀
  outer_eq := e
  cG := derivedInverseImageCompIso g₁ g₂
  cH := derivedInverseImageCompIso h₁ h₂
  cOuter := derivedInverseImageCompIso (g₂ ≫ g₁) f₂
  cQ₀ := derivedInverseImageCompIso g₂ f₂
  cQ₁ := derivedInverseImageCompIso f₁ h₂
  cP₀ := derivedInverseImageCompIso g₁ f₁
  cP₁ := derivedInverseImageCompIso f₀ h₁
  cQ := fun k => derivedInverseImageCompIso g₁ k
  cP := fun k => derivedInverseImageCompIso k h₂
  cFinish := derivedInverseImageCompIso f₀ (h₂ ≫ h₁)

/-- The actual whole comparison diagram; no coherence proof is part of its data. -/
def derivedInverseImageHorizontalDiagram :
    ExchangeCoherenceDiagram
      (DerivedCategory.Plus (AbelianSheaf.{u, u + 1} S₀) ⥤
        DerivedCategory.Plus (AbelianSheaf.{u, u + 1} X₂)) :=
  (derivedInverseImageHorizontalSourceData f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).diagram

/-- The first actual whole comparison is the original associativity rotation. -/
theorem derivedInverseImageHorizontalDiagram_start :
    (derivedInverseImageHorizontalDiagram f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).StartEquation :=
  (derivedInverseImageHorizontalSourceData f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).start
    (derivedInverseImageCompIso_assoc_hom g₁ g₂ f₂)

/-- The second actual whole comparison is native equality transport. -/
theorem derivedInverseImageHorizontalDiagram_firstTransport :
    (derivedInverseImageHorizontalDiagram f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).FirstTransportEquation :=
  (derivedInverseImageHorizontalSourceData f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).firstTransport

/-- The middle actual whole comparison is the original associativity equation. -/
theorem derivedInverseImageHorizontalDiagram_middle :
    (derivedInverseImageHorizontalDiagram f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).MiddleEquation :=
  (derivedInverseImageHorizontalSourceData f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).middle
    (derivedInverseImageCompIso_assoc_hom g₁ f₁ h₂)

/-- The fourth actual whole comparison is native equality transport. -/
theorem derivedInverseImageHorizontalDiagram_secondTransport :
    (derivedInverseImageHorizontalDiagram f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).SecondTransportEquation :=
  (derivedInverseImageHorizontalSourceData f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).secondTransport

/-- The final actual whole comparison is the original associativity rotation. -/
theorem derivedInverseImageHorizontalDiagram_finish :
    (derivedInverseImageHorizontalDiagram f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).FinishEquation :=
  (derivedInverseImageHorizontalSourceData f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).finish
    (derivedInverseImageCompIso_assoc_hom f₀ h₁ h₂)

/-- Source equalities close the actual whole transport pentagon. -/
theorem derivedInverseImageHorizontalDiagram_transport :
    (derivedInverseImageHorizontalDiagram f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).TransportEquation :=
  (derivedInverseImageHorizontalSourceData f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).transport

/-- The whole actual comparison chase consumes only its named native witnesses. -/
theorem derivedInverseImageHorizontalDiagram_chain :
    (derivedInverseImageHorizontalDiagram f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).ChainEquation :=
  (derivedInverseImageHorizontalSourceData f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).chain
    (derivedInverseImageCompIso_assoc_hom g₁ g₂ f₂)
    (derivedInverseImageCompIso_assoc_hom g₁ f₁ h₂)
    (derivedInverseImageCompIso_assoc_hom f₀ h₁ h₂)

/-- Evaluate the proved whole diagram; no concrete comparison proof is repeated. -/
theorem derivedInverseImageHorizontalDiagram_chain_app
    (A : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} S₀)) :
    ((derivedInverseImageHorizontalDiagram f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).app A).ChainEquation :=
  ExchangeCoherenceDiagram.chain_app _
    (derivedInverseImageHorizontalDiagram_chain f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e) A

/-- The proved whole diagram has the shared whiskering recipe used by extraction. -/
theorem derivedInverseImageHorizontalDiagram_whiskered :
    WhiskeredComparisonChainEquation
    (derivedInverseImageCompIso g₁ g₂) (derivedInverseImageCompIso g₁ f₁)
    (derivedInverseImageCompIso f₀ h₁)
    (derivedInverseImageCompIso (g₂ ≫ g₁) f₂).hom
    (Functor.whiskerLeft (derivedInverseImage g₁) (derivedInverseImageCompIso g₂ f₂).inv)
    (Functor.whiskerLeft (derivedInverseImage g₁)
      (eqToIso (congrArg (fun k : X₂ ⟶ S₁ => derivedInverseImage k) e₂)).hom)
    (Functor.whiskerLeft (derivedInverseImage g₁) (derivedInverseImageCompIso f₁ h₂).hom)
    (Functor.whiskerRight
      (eqToIso (congrArg (fun k : X₁ ⟶ S₀ => derivedInverseImage k) e₁)).hom
      (derivedInverseImage h₂))
    (eqToIso (congrArg (fun k : X₂ ⟶ S₀ => derivedInverseImage k) e)).hom
    (derivedInverseImageCompIso f₀ (h₂ ≫ h₁)).hom
    (Functor.whiskerLeft (derivedInverseImage f₀) (derivedInverseImageCompIso h₁ h₂).hom) :=
  derivedInverseImageHorizontalDiagram_chain f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e

end WholeHorizontal

/-- The canonical whole natural-iso factorization of the actual inverse-image square. -/
theorem derivedInverseImageSquareIso_eq_comp {X S X' S' : Scheme.{u}}
    [HasDerivedCategory.{wb0} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{wb1} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{wb2} (AbelianSheaf.{u, u + 1} X')]
    [HasDerivedCategory.{wb3} (AbelianSheaf.{u, u + 1} S')]
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : f' ≫ g = g' ≫ f) :
    derivedInverseImageSquareIso f f' g g' h =
      (derivedInverseImageCompIso g f').symm ≪≫
        eqToIso (congrArg (fun k : X' ⟶ S => derivedInverseImage k) h) ≪≫
        derivedInverseImageCompIso f g' := rfl

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

/-- Actual horizontal square coherence is proved in the whole functor category. -/
theorem derivedInverseImageSquareIso_hComp_whole :
    WholeHorizontalSquareEquation
      (derivedInverseImageSquareIso f₀ f₁ g₁ h₁ e₁).hom
      (derivedInverseImageSquareIso f₁ f₂ g₂ h₂ e₂).hom
      (derivedInverseImageSquareIso f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).hom
      (derivedInverseImageCompIso g₁ g₂).hom
    (derivedInverseImageCompIso h₁ h₂).hom :=
  (derivedInverseImageHorizontalSourceData f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e).whole
    (derivedInverseImageCompIso_assoc_hom g₁ g₂ f₂)
    (derivedInverseImageCompIso_assoc_hom g₁ f₁ h₂)
    (derivedInverseImageCompIso_assoc_hom f₀ h₁ h₂)

/-- Evaluate only the final actual horizontal square, not its internal long chase. -/
theorem derivedInverseImageSquareIso_hComp (A : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} S₀)) :
    HorizontalSquareEquation
      (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f₀ f₁ g₁ h₁ e₁).hom)
      (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f₁ f₂ g₂ h₂ e₂).hom)
      (TwoSquare.mk _ _ _ _
      (derivedInverseImageSquareIso f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).hom)
      (derivedInverseImageCompIso g₁ g₂).hom
    (derivedInverseImageCompIso h₁ h₂).hom A :=
  wholeHorizontalSquare_app
    (derivedInverseImageSquareIso f₀ f₁ g₁ h₁ e₁).hom
    (derivedInverseImageSquareIso f₁ f₂ g₂ h₂ e₂).hom
    (derivedInverseImageSquareIso f₀ f₂ (g₂ ≫ g₁) (h₂ ≫ h₁) e).hom
    (derivedInverseImageCompIso g₁ g₂).hom
    (derivedInverseImageCompIso h₁ h₂).hom
    (derivedInverseImageSquareIso_hComp_whole f₀ f₁ f₂ g₁ g₂ h₁ h₂ e₁ e₂ e) A

end Horizontal

/-- Transposing the commuting square inverts its canonical inverse-image comparison. -/
theorem derivedInverseImageSquareIso_transpose {X S X' S' : Scheme.{u}}
    [HasDerivedCategory.{wb0} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{wb1} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{wb2} (AbelianSheaf.{u, u + 1} X')]
    [HasDerivedCategory.{wb3} (AbelianSheaf.{u, u + 1} S')]
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (e : f' ≫ g = g' ≫ f) :
    derivedInverseImageSquareIso g g' f f' e.symm =
      (derivedInverseImageSquareIso f f' g g' e).symm := by
  simp only [derivedInverseImageSquareIso, sourceSquareIso,
    Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
  rfl

/-- The vertical square-coherence law follows from transposed horizontal coherence. -/
theorem derivedInverseImageSquareIso_vComp {S X Y S' X' Y' : Scheme.{u}}
    [HasDerivedCategory.{wb0} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{wb1} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{wb2} (AbelianSheaf.{u, u + 1} Y)]
    [HasDerivedCategory.{wb3} (AbelianSheaf.{u, u + 1} S')]
    [HasDerivedCategory.{wb4} (AbelianSheaf.{u, u + 1} X')]
    [HasDerivedCategory.{wb5} (AbelianSheaf.{u, u + 1} Y')]
    (f : X ⟶ S) (k : Y ⟶ X) (f' : X' ⟶ S') (k' : Y' ⟶ X')
    (g : S' ⟶ S) (g' : X' ⟶ X) (g'' : Y' ⟶ Y)
    (ef : f' ≫ g = g' ≫ f) (ek : k' ≫ g' = g'' ≫ k)
    (e : (k' ≫ f') ≫ g = g'' ≫ (k ≫ f)) (A : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} S)) :
    VerticalSquareEquation
      (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso f f' g g' ef).hom)
      (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso k k' g' g'' ek).hom)
      (TwoSquare.mk _ _ _ _
        (derivedInverseImageSquareIso (k ≫ f) (k' ≫ f') g g'' e).hom)
      (derivedInverseImageCompIso f k) (derivedInverseImageCompIso f' k') A := by
  change (derivedInverseImageCompIso f' k').hom.app ((derivedInverseImage g).obj A) ≫
        (derivedInverseImage k').map ((derivedInverseImageSquareIso f f' g g' ef).hom.app A) ≫
        (derivedInverseImageSquareIso k k' g' g'' ek).hom.app ((derivedInverseImage f).obj A) =
      (derivedInverseImageSquareIso (k ≫ f) (k' ≫ f') g g'' e).hom.app A ≫
        (derivedInverseImage g'').map ((derivedInverseImageCompIso f k).hom.app A)
  have hp := derivedInverseImageSquareIso_hComp g g' g'' f k f' k' ef.symm ek.symm e.symm A
  dsimp only [HorizontalSquareEquation, TwoSquare.mk, TwoSquare.natTrans] at hp
  rw [derivedInverseImageSquareIso_transpose f f' g g' ef,
    derivedInverseImageSquareIso_transpose k k' g' g'' ek,
    derivedInverseImageSquareIso_transpose (k ≫ f) (k' ≫ f') g g'' e] at hp
  have hr := congrArg (fun z =>
    (derivedInverseImageSquareIso (k ≫ f) (k' ≫ f') g g'' e).hom.app A ≫ z ≫
      (derivedInverseImage k').map ((derivedInverseImageSquareIso f f' g g' ef).hom.app A) ≫
      (derivedInverseImageSquareIso k k' g' g'' ek).hom.app ((derivedInverseImage f).obj A)) hp
  simp only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id_app_assoc,
    ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app] at hr
  rw [(derivedInverseImage k').map_id
    ((derivedInverseImage f ⋙ derivedInverseImage g').obj A)] at hr
  simpa only [CategoryTheory.Functor.comp_obj, CategoryTheory.Category.id_comp,
    Iso.inv_hom_id_app, CategoryTheory.Category.comp_id] using hr.symm


universe wIdS wIdS'

/-- The inverse-image square over vertical identities has its original normalization. -/
theorem derivedInverseImageSquareIso_vId {S S' : Scheme.{u}}
    [HasDerivedCategory.{wIdS} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{wIdS'} (AbelianSheaf.{u, u + 1} S')] (g : S' ⟶ S)
    (e : 𝟙 S' ≫ g = g ≫ 𝟙 S) (A : DerivedCategory.Plus (AbelianSheaf.{u, u + 1} S)) :
    IdentitySquareEquation
      (TwoSquare.mk _ _ _ _ (derivedInverseImageSquareIso (𝟙 S) (𝟙 S') g g e).hom)
      (derivedInverseImageIdIso S) (derivedInverseImageIdIso S') A := by
  have hi := congrArg (fun i => i.hom.app A) (derivedInverseImageSquareIso_id g e.symm)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app] at hi
  change (derivedInverseImageSquareIso g g (𝟙 S) (𝟙 S') e.symm).hom.app A ≫
      ((derivedInverseImageIdIso S').hom.app ((derivedInverseImage g).obj A) ≫
        𝟙 ((derivedInverseImage g).obj A)) =
    (derivedInverseImage g).map ((derivedInverseImageIdIso S).hom.app A) ≫
      𝟙 ((derivedInverseImage g).obj A) at hi
  have hi := exchangeCoherence_remove_right_id
    ((derivedInverseImageSquareIso g g (𝟙 S) (𝟙 S') e.symm).hom.app A)
    ((derivedInverseImageIdIso S').hom.app ((derivedInverseImage g).obj A))
    ((derivedInverseImage g).map ((derivedInverseImageIdIso S).hom.app A)) hi
  change (derivedInverseImageIdIso S').hom.app ((derivedInverseImage g).obj A) =
    (derivedInverseImageSquareIso (𝟙 S) (𝟙 S') g g e).hom.app A ≫
      (derivedInverseImage g).map ((derivedInverseImageIdIso S).hom.app A)
  rw [derivedInverseImageSquareIso_transpose g g (𝟙 S) (𝟙 S') e.symm,
    Iso.symm_hom, ← hi, Iso.inv_hom_id_app_assoc]

section HigherBaseChangeComparisons

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{wX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{wS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)

/-- The native exact-homology comparison identifies the source of higher base change. -/
def higherBaseChangeSourceIso (q : ℕ) :
    higherDirectImage f q ⋙ inverseImage g ≅
      DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0 ⋙
        (derivedDirectImage f ⋙ derivedInverseImage g) ⋙
        DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ) :=
  Functor.higherExchangeSourceIso (directImage f) (inverseImage g) q

/-- The native exact-single comparison identifies the target of higher base change. -/
def higherBaseChangeTargetIso (q : ℕ) :
    DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0 ⋙
        (derivedInverseImage g' ⋙ derivedDirectImage f') ⋙
        DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ) ≅
      inverseImage g' ⋙ higherDirectImage f' q :=
  Functor.higherExchangeTargetIso (inverseImage g') (directImage f') q

/-- The source comparison evaluated on a coefficient sheaf. -/
theorem higherBaseChangeSourceIso_hom_app (q : ℕ)
    (F : AbelianSheaf.{u, u + 1} X) :
    (higherBaseChangeSourceIso f g q).hom.app F =
      (inverseImage g).map ((higherDirectImageIso f q).hom.app F) ≫
        ((inverseImage g).rightDerivedFunctorPlusHomologyIso (q : ℤ)).inv.app
          ((derivedDirectImage f).obj
            ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)) :=
  Functor.higherExchangeSourceIso_hom_app (directImage f) (inverseImage g) q F

/-- The target comparison evaluated on a coefficient sheaf. -/
theorem higherBaseChangeTargetIso_hom_app (q : ℕ)
    (F : AbelianSheaf.{u, u + 1} X) :
    (higherBaseChangeTargetIso f' g' q).hom.app F =
      (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S') (q : ℤ)).map
          ((derivedDirectImage f').map
            (((inverseImage g').rightDerivedFunctorPlusSingleIso 0).hom.app F)) ≫
        (higherDirectImageIso f' q).inv.app ((inverseImage g').obj F) :=
  Functor.higherExchangeTargetIso_hom_app (inverseImage g') (directImage f') q F

end HigherBaseChangeComparisons

section HigherEdgesAppend

universe wEdgeS wEdgeX wEdgeXPrime

/-- The inverse target comparison retains its actual exact-single component. -/
theorem higherBaseChangeTargetIso_inv_app
    {S X X' : Scheme.{u}}
    [HasDerivedCategory.{wEdgeS} (AbelianSheaf.{u, u + 1} S)]
    [HasDerivedCategory.{wEdgeX} (AbelianSheaf.{u, u + 1} X)]
    [HasDerivedCategory.{wEdgeXPrime} (AbelianSheaf.{u, u + 1} X')]
    (f : X' ⟶ S) (g : X' ⟶ X) (q : ℕ) (F : AbelianSheaf.{u, u + 1} X) :
    (higherBaseChangeTargetIso f g q).inv.app F =
      (higherDirectImageIso f q).hom.app ((inverseImage g).obj F) ≫
        (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) (q : ℤ)).map
          ((derivedDirectImage f).map
            (((inverseImage g).rightDerivedFunctorPlusSingleIso 0).inv.app F)) :=
  Functor.higherExchangeTargetIso_inv_app (inverseImage g) (directImage f) q F

section HorizontalSource
universe wEdge0 wEdge1 wEdge2 wEdge3
variable {X S₀ S₁ S₂ : Scheme.{u}}
  [HasDerivedCategory.{wEdge0} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wEdge1} (AbelianSheaf.{u, u + 1} S₀)]
  [HasDerivedCategory.{wEdge2} (AbelianSheaf.{u, u + 1} S₁)]
  [HasDerivedCategory.{wEdge3} (AbelianSheaf.{u, u + 1} S₂)]
  (f : X ⟶ S₀) (g₁ : S₁ ⟶ S₀) (g₂ : S₂ ⟶ S₁)
  (q : ℕ) (F : AbelianSheaf.{u, u + 1} X)

/-- The actual source comparison respects horizontal composition. -/
theorem higherBaseChangeSourceIso_comp :
    (inverseImageComp g₁ g₂).hom.app ((higherDirectImage f q).obj F) ≫
        (inverseImage g₂).map ((higherBaseChangeSourceIso f g₁ q).hom.app F) ≫
        (((inverseImage g₂).rightDerivedFunctorPlusHomologyIso (q : ℤ)).inv.app
          ((derivedInverseImage g₁).obj ((derivedDirectImage f).obj
            ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F)))) =
      (higherBaseChangeSourceIso f (g₂ ≫ g₁) q).hom.app F ≫
        (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S₂) (q : ℤ)).map
          ((derivedInverseImageCompIso g₁ g₂).hom.app ((derivedDirectImage f).obj
            ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F))) := by
  rw [higherBaseChangeSourceIso_hom_app, higherBaseChangeSourceIso_hom_app]
  simpa only [Category.assoc, Iso.app_hom] using mapped_horizontal_source_edge
    (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S₀) (q : ℤ))
    (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S₁) (q : ℤ))
    (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S₂) (q : ℤ))
    (inverseImage g₁) (inverseImage g₂) (inverseImage (g₂ ≫ g₁))
    (derivedInverseImage g₁) (derivedInverseImage g₂) (derivedInverseImage (g₂ ≫ g₁))
    ((inverseImage g₁).rightDerivedFunctorPlusHomologyIso (q : ℤ))
    ((inverseImage g₂).rightDerivedFunctorPlusHomologyIso (q : ℤ))
    ((inverseImage (g₂ ≫ g₁)).rightDerivedFunctorPlusHomologyIso (q : ℤ))
    (inverseImageComp g₁ g₂) (derivedInverseImageCompIso g₁ g₂)
    ((derivedDirectImage f).obj
      ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).obj F))
    (Functor.rightDerivedFunctorPlusHomologyIso_comp (inverseImage g₁) (inverseImage g₂)
      (inverseImage (g₂ ≫ g₁)) (inverseImageComp g₁ g₂) (q : ℤ) _)
    ((higherDirectImageIso f q).app F)

end HorizontalSource

section HorizontalTarget
universe wEdge0 wEdge1 wEdge2 wEdge3
variable {S X₀ X₁ X₂ : Scheme.{u}}
  [HasDerivedCategory.{wEdge0} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{wEdge1} (AbelianSheaf.{u, u + 1} X₀)]
  [HasDerivedCategory.{wEdge2} (AbelianSheaf.{u, u + 1} X₁)]
  [HasDerivedCategory.{wEdge3} (AbelianSheaf.{u, u + 1} X₂)]
  (f : X₂ ⟶ S) (h₁ : X₁ ⟶ X₀) (h₂ : X₂ ⟶ X₁)
  (q : ℕ) (F : AbelianSheaf.{u, u + 1} X₀)

/-- The actual target comparison respects horizontal composition. -/
theorem higherBaseChangeTargetIso_comp :
    (higherDirectImage f q).map ((inverseImageComp h₁ h₂).hom.app F) ≫
        (higherBaseChangeTargetIso f h₂ q).inv.app ((inverseImage h₁).obj F) ≫
        (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) (q : ℤ)).map
          ((derivedDirectImage f).map ((derivedInverseImage h₂).map
            (((inverseImage h₁).rightDerivedFunctorPlusSingleIso 0).inv.app F))) =
      (higherBaseChangeTargetIso f (h₂ ≫ h₁) q).inv.app F ≫
        (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) (q : ℤ)).map
          ((derivedDirectImage f).map ((derivedInverseImageCompIso h₁ h₂).hom.app
            ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X₀) 0).obj F))) := by
  rw [higherBaseChangeTargetIso_inv_app, higherBaseChangeTargetIso_inv_app]
  simpa only [Category.assoc] using mapped_horizontal_target_edge
    (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X₀) 0)
    (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X₁) 0)
    (DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X₂) 0)
    (inverseImage h₁) (inverseImage h₂) (inverseImage (h₂ ≫ h₁))
    (derivedInverseImage h₁) (derivedInverseImage h₂) (derivedInverseImage (h₂ ≫ h₁))
    ((inverseImage h₁).rightDerivedFunctorPlusSingleIso 0)
    ((inverseImage h₂).rightDerivedFunctorPlusSingleIso 0)
    ((inverseImage (h₂ ≫ h₁)).rightDerivedFunctorPlusSingleIso 0)
    (inverseImageComp h₁ h₂) (derivedInverseImageCompIso h₁ h₂) F
    (Functor.rightDerivedFunctorPlusSingleIso_comp (inverseImage h₁) (inverseImage h₂)
      (inverseImage (h₂ ≫ h₁)) (inverseImageComp h₁ h₂) F)
    (derivedDirectImage f)
    (DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) (q : ℤ))
    (higherDirectImage f q) (higherDirectImageIso f q)

end HorizontalTarget

end HigherEdgesAppend

end AlgebraicGeometry.Scheme.EtaleCohomology
