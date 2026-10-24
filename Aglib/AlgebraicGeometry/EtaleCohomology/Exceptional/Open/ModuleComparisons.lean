/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleAdjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackCoherence

/-! # Original identity and composition comparisons for native module lower shriek -/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

variable (Λ : Type (u + 1)) [Ring Λ]

/-- Module-valued direct-image identity from the original chart identity. -/
def moduleValuedDirectImageIdIso (X : Scheme.{u}) :
    moduleValuedDirectImage (𝟙 X) Λ ≅ 𝟭 (ModuleValuedSheaf X Λ) :=
  Functor.sheafPushforwardContinuousId' (siteBaseChangeId X)
    (ModuleCat.{u + 1} Λ) (Scheme.smallEtaleTopology X)

/-- Native direct-image identity after the actual inverse coefficient equivalence. -/
def moduleDirectImageIdValuedIso (X : Scheme.{u}) :
    moduleDirectImage (𝟙 X) Λ ⋙ (moduleSheafEquivalence X Λ).inverse ≅
      (𝟭 (ModuleSheaf X Λ)) ⋙ (moduleSheafEquivalence X Λ).inverse :=
  moduleDirectImageComparison (𝟙 X) Λ ≪≫
    Functor.isoWhiskerLeft _ (moduleValuedDirectImageIdIso Λ X) ≪≫
    Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm

/-- Native direct-image identity induced by the original chart identity. -/
def moduleDirectImageIdIso (X : Scheme.{u}) :
    moduleDirectImage (𝟙 X) Λ ≅ 𝟭 (ModuleSheaf X Λ) :=
  ((Functor.whiskeringRight (ModuleSheaf X Λ) (ModuleSheaf X Λ)
    (ModuleValuedSheaf X Λ)).obj (moduleSheafEquivalence X Λ).inverse).preimageIso
      (moduleDirectImageIdValuedIso Λ X)

/-- Native inverse-image identity with its actual adjunction normalization. -/
def moduleInverseImageIdIso (X : Scheme.{u}) :
    moduleInverseImage (𝟙 X) Λ ≅ 𝟭 (ModuleSheaf X Λ) :=
  ((moduleInverseImageAdjunction (𝟙 X) Λ).ofNatIsoRight
    (moduleDirectImageIdIso Λ X)).leftAdjointUniq Adjunction.id

variable {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S)

/-- Module-valued direct-image composition from the actual chart comparison. -/
def moduleValuedDirectImageCompIso :
    moduleValuedDirectImage (g ≫ f) Λ ≅
      moduleValuedDirectImage g Λ ⋙ moduleValuedDirectImage f Λ :=
  (Functor.sheafPushforwardContinuousComp' (siteBaseChangeComp f g).symm
    (ModuleCat.{u + 1} Λ) (Scheme.smallEtaleTopology X)
      (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology T)).symm

/-- Native direct-image composition after the actual inverse coefficient equivalence. -/
def moduleDirectImageCompRightIso :
    (moduleDirectImage g Λ ⋙ moduleDirectImage f Λ) ⋙
        (moduleSheafEquivalence X Λ).inverse ≅
      (moduleSheafEquivalence T Λ).inverse ⋙
        moduleValuedDirectImage g Λ ⋙ moduleValuedDirectImage f Λ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (moduleDirectImageComparison f Λ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleDirectImageComparison g Λ) _ ≪≫
    Functor.associator _ _ _

/-- Native direct-image composition induced by actual chart pullback composition. -/
def moduleDirectImageCompIso :
    moduleDirectImage (g ≫ f) Λ ≅ moduleDirectImage g Λ ⋙ moduleDirectImage f Λ :=
  ((Functor.whiskeringRight (ModuleSheaf T Λ) (ModuleSheaf X Λ)
    (ModuleValuedSheaf X Λ)).obj (moduleSheafEquivalence X Λ).inverse).preimageIso
      (moduleDirectImageComparison (g ≫ f) Λ ≪≫
        Functor.isoWhiskerLeft _ (moduleValuedDirectImageCompIso Λ f g) ≪≫
        (moduleDirectImageCompRightIso Λ f g).symm)

/-- Native inverse-image composition retains the original specified adjunctions. -/
def moduleInverseImageCompIso :
    moduleInverseImage (g ≫ f) Λ ≅ moduleInverseImage f Λ ⋙ moduleInverseImage g Λ :=
  ((moduleInverseImageAdjunction (g ≫ f) Λ).ofNatIsoRight
    (moduleDirectImageCompIso Λ f g)).leftAdjointUniq
      ((moduleInverseImageAdjunction f Λ).comp (moduleInverseImageAdjunction g Λ))

/-- Module lower shriek of the identity, normalized by the actual inverse image. -/
def moduleLowerShriekIdIso (X : Scheme.{u}) :
    moduleLowerShriek (𝟙 X) Λ ≅ 𝟭 (ModuleSheaf X Λ) :=
  ((moduleLowerShriekAdjunction (𝟙 X) Λ).ofNatIsoRight
    (moduleInverseImageIdIso Λ X)).leftAdjointUniq Adjunction.id

/-- The lower-shriek identity comparison has the original adjunction normalization. -/
@[reassoc]
theorem moduleLowerShriekIdIso_homEquiv (X : Scheme.{u}) (M : ModuleSheaf X Λ) :
    (moduleLowerShriekAdjunction (𝟙 X) Λ).homEquiv _ _
        ((moduleLowerShriekIdIso Λ X).hom.app M) ≫
      (moduleInverseImageIdIso Λ X).hom.app M = 𝟙 M := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((moduleLowerShriekAdjunction (𝟙 X) Λ).ofNatIsoRight (moduleInverseImageIdIso Λ X))
    (Adjunction.id (C := ModuleSheaf X Λ)) M
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  simpa only [moduleLowerShriekIdIso, Functor.id_obj, Adjunction.id, NatTrans.id_app] using h

variable [Etale f] [Etale g]

/-- Composition of native module lower shriek, as the mate of actual inverse-image composition. -/
def moduleLowerShriekCompIso :
    moduleLowerShriek (g ≫ f) Λ ≅ moduleLowerShriek g Λ ⋙ moduleLowerShriek f Λ :=
  ((moduleLowerShriekAdjunction (g ≫ f) Λ).ofNatIsoRight
    (moduleInverseImageCompIso Λ f g)).leftAdjointUniq
      ((moduleLowerShriekAdjunction g Λ).comp (moduleLowerShriekAdjunction f Λ))

/-- The composition comparison retains the original composite adjunction unit. -/
@[reassoc]
theorem moduleLowerShriekCompIso_unit (M : ModuleSheaf T Λ) :
    (moduleLowerShriekAdjunction (g ≫ f) Λ).homEquiv _ _
        ((moduleLowerShriekCompIso Λ f g).hom.app M) ≫
      (moduleInverseImageCompIso Λ f g).hom.app
        ((moduleLowerShriek f Λ).obj ((moduleLowerShriek g Λ).obj M)) =
    (moduleLowerShriekAdjunction g Λ).unit.app M ≫
      (moduleInverseImage g Λ).map
        ((moduleLowerShriekAdjunction f Λ).unit.app ((moduleLowerShriek g Λ).obj M)) := by
  simpa only [Adjunction.homEquiv_ofNatIsoRight_apply, moduleLowerShriekCompIso,
    Functor.comp_obj, Adjunction.comp_unit_app] using
    Adjunction.homEquiv_leftAdjointUniq_hom_app
      (((moduleLowerShriekAdjunction (g ≫ f) Λ).ofNatIsoRight
        (moduleInverseImageCompIso Λ f g)))
      ((moduleLowerShriekAdjunction g Λ).comp (moduleLowerShriekAdjunction f Λ)) M

end AlgebraicGeometry.Scheme.EtaleCohomology
