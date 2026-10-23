/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.Adjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.BaseChangeMap
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Identity

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.TransportedComposition
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.Transport
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.TransportedIdentity
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.DerivedConjugacy
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.IdentityConjugacy

/-!
# Original identity and composition comparisons for derived étale images

The comparisons use the native sheaf comparisons and the installed
right-derived identity/composition comparisons. Direct-image composition
uses preservation of injectives, not an assertion that direct image is exact.
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
