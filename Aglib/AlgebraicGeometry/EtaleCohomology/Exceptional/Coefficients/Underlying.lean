/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Pullback
public import Aglib.CategoryTheory.Sites.Pullback.Coefficients
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# The original abelian inverse image underlying constant-ring pullback

This comparison is between the native ringed pullback and the original étale
abelian inverse image. Coefficient forgetting is the existing `forget₂`, and
its comparison is the preserved-Kan/sheafification comparison. No duplicate
scalar-forgetting construction or changed site is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

attribute [local instance] hasSheafifyLarge hasSheafifyModules

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]

/-- Additive forgetting preserves the actual sheafification class, detected on underlying types. -/
theorem moduleForget_preservesSheafification :
    (Scheme.smallEtaleTopology X).PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) where
  le := by
    intro P Q α hα
    let J := Scheme.smallEtaleTopology X
    let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
    let : J.WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
      CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard.{u + 1, u} J
    have ht : J.W (Functor.whiskerRight α (CategoryTheory.forget (ModuleCat.{u + 1} Λ))) :=
      J.W_of_preservesSheafification (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) α hα
    have hi : Presheaf.IsLocallyInjective J (Functor.whiskerRight α U) :=
      (Presheaf.isLocallyInjective_forget_iff J _).mp ht.isLocallyInjective
    have hs : Presheaf.IsLocallySurjective J (Functor.whiskerRight α U) :=
      (Presheaf.isLocallySurjective_iff_whisker_forget J _).mpr ht.isLocallySurjective
    exact (J.W_iff_isLocallyBijective (Functor.whiskerRight α U)).mpr ⟨hi, hs⟩

attribute [local instance] moduleForget_preservesSheafification

/-- The inverse equivalence retains the same original abelian sheaf. -/
def moduleSheafInverseUnderlyingIso :
    (moduleSheafEquivalence X Λ).inverse ⋙
      sheafCompose (Scheme.smallEtaleTopology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≅
      SheafOfModules.toSheaf (constantRing X Λ) :=
  Functor.isoWhiskerLeft (moduleSheafEquivalence X Λ).inverse
    (moduleSheafUnderlyingIso X Λ).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleSheafEquivalence X Λ).counitIso
      (SheafOfModules.toSheaf (constantRing X Λ)) ≪≫
    Functor.leftUnitor _

variable {X} {S : Scheme.{u}} (f : S ⟶ X)

/-- The original module-valued inverse image commutes with additive forgetting. -/
def moduleValuedInverseImageUnderlyingIso :
    moduleValuedInverseImage f Λ ⋙
      sheafCompose (Scheme.smallEtaleTopology S)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ≅
    sheafCompose (Scheme.smallEtaleTopology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙ inverseImage f := by
  letI : (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).PreservesLeftKanExtensions
      (siteBaseChange f).op := by
    intro P
    infer_instance
  exact (Functor.sheafPullbackCoefficientIso (siteBaseChange f)
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).symm

/-- The native constant-ring inverse image has the original abelian inverse image underneath. -/
def moduleInverseImageUnderlyingIso :
    moduleInverseImage f Λ ⋙ SheafOfModules.toSheaf (constantRing S Λ) ≅
      SheafOfModules.toSheaf (constantRing X Λ) ⋙ inverseImage f :=
  Functor.isoWhiskerRight (moduleInverseImageTransportIso f Λ)
    (SheafOfModules.toSheaf (constantRing S Λ)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      ((moduleSheafEquivalence X Λ).inverse ⋙ moduleValuedInverseImage f Λ)
      (moduleSheafUnderlyingIso S Λ) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleSheafEquivalence X Λ).inverse
      (moduleValuedInverseImageUnderlyingIso Λ f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (moduleSheafInverseUnderlyingIso X Λ) (inverseImage f)

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
