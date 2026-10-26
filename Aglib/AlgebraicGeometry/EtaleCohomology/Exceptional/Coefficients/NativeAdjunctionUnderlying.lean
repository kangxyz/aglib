/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.AdjunctionUnderlying
public import Aglib.CategoryTheory.Adjunction.UnderlyingEquivalence
public import Aglib.CategoryTheory.Adjunction.UnderlyingMate

/-!
# The original native adjunction under additive coefficient forgetting

The existing native pullback comparison preserves the original adjunction unit.
The proof uses the native module-sheafification counit and the triangle identities
of the existing coefficient equivalence. In particular, it does not replace the
specified pullback comparison by a newly chosen mate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.TorsionZMod.Ringed

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  moduleForget_preservesSheafification moduleForget_preservesLeftKanExtensions
  hasSheafifyRingStandard hasSheafifyAbStandard
  ringWEqualsLocallyBijectiveStandard abWEqualsLocallyBijectiveStandard

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]

/-- The counit of the original coefficient equivalence has its prescribed
abelian-sheafification comparison underneath. -/
@[reassoc]
theorem moduleSheafEquivalence_counit_underlying (M : ModuleSheaf X Λ) :
    (SheafOfModules.toSheaf (constantRing X Λ)).map
        ((moduleSheafEquivalence X Λ).counitIso.hom.app M) =
      (moduleSheafUnderlyingIso X Λ).hom.app
        ((moduleSheafEquivalence X Λ).inverse.obj M) :=
  ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_counit_underlying.{
    u + 1, u, u + 1, u + 1}
    (Scheme.smallEtaleTopology X) Λ M

/-- The inverse counit retains the inverse of the specified underlying comparison. -/
theorem moduleSheafEquivalence_counit_inv_underlying (M : ModuleSheaf X Λ) :
    (SheafOfModules.toSheaf (constantRing X Λ)).map
        ((moduleSheafEquivalence X Λ).counitIso.inv.app M) =
      (moduleSheafUnderlyingIso X Λ).inv.app
        ((moduleSheafEquivalence X Λ).inverse.obj M) :=
  ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_counit_inv_underlying.{
    u + 1, u, u + 1, u + 1}
    (Scheme.smallEtaleTopology X) Λ M

/-- The already specified inverse-equivalence comparison is the identity on the
original abelian sheaf. -/
theorem moduleSheafInverseUnderlyingIso_hom_app (M : ModuleSheaf X Λ) :
    (moduleSheafInverseUnderlyingIso X Λ).hom.app M =
      𝟙 ((SheafOfModules.toSheaf (constantRing X Λ)).obj M) :=
  ModuleCat.Sheaf.ConstantRing.moduleSheafInverseUnderlyingIso_hom_app.{
    u + 1, u, u + 1, u + 1}
    (Scheme.smallEtaleTopology X) Λ M

/-- The fixed inverse-equivalence comparison is the identity natural isomorphism. -/
theorem moduleSheafInverseUnderlyingIso_eq_refl :
    moduleSheafInverseUnderlyingIso X Λ =
      Iso.refl (SheafOfModules.toSheaf (constantRing X Λ)) :=
  ModuleCat.Sheaf.ConstantRing.moduleSheafInverseUnderlyingIso_eq_refl.{
    u + 1, u, u + 1, u + 1}
    (Scheme.smallEtaleTopology X) Λ

/-- The equivalence unit becomes the inverse of the existing underlying comparison. -/
theorem moduleSheafEquivalence_unit_underlying (M : ModuleValuedSheaf X Λ) :
    (sheafCompose (Scheme.smallEtaleTopology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
          ((moduleSheafEquivalence X Λ).unitIso.hom.app M) =
      (moduleSheafUnderlyingIso X Λ).inv.app M :=
  ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence_unit_underlying.{
    u + 1, u, u + 1, u + 1}
    (Scheme.smallEtaleTopology X) Λ M

variable {X} {S : Scheme.{u}} (f : S ⟶ X)

/-- The inverse direct-image transport has exactly the existing coefficient
comparison underneath; restriction of scalars retains every additive map. -/
theorem moduleDirectImageTransportIso_inv_underlying (M : ModuleSheaf S Λ) :
    (SheafOfModules.toSheaf (constantRing X Λ)).map
        ((moduleDirectImageTransportIso f Λ).inv.app M) =
      (moduleSheafUnderlyingIso X Λ).hom.app
        ((moduleValuedDirectImage f Λ).obj
          ((moduleSheafEquivalence S Λ).inverse.obj M)) :=
  ModuleCat.Sheaf.ConstantRing.moduleDirectImageTransportIso_inv_underlying.{
    u + 1, u, u + 1, u, u + 1, u + 1}
    (siteBaseChange f) (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ M

/-- The unit transported through the existing equivalences becomes the original
module-valued unit, after its specified underlying comparison. -/
@[reassoc]
theorem moduleTransportAdjunction_unit_underlying (M : ModuleSheaf X Λ) :
    (SheafOfModules.toSheaf (constantRing X Λ)).map
        ((moduleTransportAdjunction f Λ).unit.app M) ≫
      (directImage f).map ((moduleSheafUnderlyingIso S Λ).hom.app
        ((moduleValuedInverseImage f Λ).obj
          ((moduleSheafEquivalence X Λ).inverse.obj M))) =
      (sheafCompose (Scheme.smallEtaleTopology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
          ((moduleValuedInverseImageAdjunction f Λ).unit.app
            ((moduleSheafEquivalence X Λ).inverse.obj M)) :=
  ModuleCat.Sheaf.ConstantRing.moduleTransportAdjunction_unit_underlying.{
    u + 1, u, u + 1, u, u + 1, u + 1}
    (siteBaseChange f) (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ M

/-- The fixed native inverse-image comparison preserves the original native
unit and the original abelian unit. -/
@[reassoc]
theorem moduleInverseImageUnderlyingIso_unit (M : ModuleSheaf X Λ) :
    (SheafOfModules.toSheaf (constantRing X Λ)).map
        ((moduleInverseImageAdjunction f Λ).unit.app M) ≫
      (directImage f).map ((moduleInverseImageUnderlyingIso Λ f).hom.app M) =
    (inverseImageAdjunction f).unit.app
      ((SheafOfModules.toSheaf (constantRing X Λ)).obj M) :=
  ModuleCat.Sheaf.ConstantRing.moduleInverseImageUnderlyingIso_unit_app.{
    u + 1, u, u + 1, u, u + 1, u + 1}
    (siteBaseChange f) (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ M

/-- The inverse of the fixed native pullback comparison has the original
direct-image comparison as its mate. -/
theorem mate_moduleInverseImageUnderlyingIso_inv :
    (mateEquiv (moduleInverseImageAdjunction f Λ) (inverseImageAdjunction f)
      (TwoSquare.mk _ _ _ _ (moduleInverseImageUnderlyingIso Λ f).inv)).natTrans =
        (moduleDirectImageUnderlyingIso f Λ).hom :=
  ModuleCat.Sheaf.ConstantRing.mate_moduleInverseImageUnderlyingIso_inv.{
    u + 1, u, u + 1, u, u + 1, u + 1}
    (siteBaseChange f) (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
