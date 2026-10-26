/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Underlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackComposition

/-!
# Original adjunction maps under additive coefficient comparison

These equations use the original continuous-site adjunction and its proved
coefficient comparison. They do not infer compatibility merely from an
isomorphism of the underlying functors.
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

variable {X S : Scheme.{u}} (f : S ⟶ X) (Λ : Type (u + 1)) [Ring Λ]

/-- The original module-valued unit becomes the original abelian unit. -/
theorem moduleValuedInverseImageUnderlyingIso_unit (M : ModuleValuedSheaf X Λ) :
    (sheafCompose (Scheme.smallEtaleTopology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
          ((moduleValuedInverseImageAdjunction f Λ).unit.app M) ≫
      (directImage f).map ((moduleValuedInverseImageUnderlyingIso Λ f).hom.app M) =
    (inverseImageAdjunction f).unit.app
      ((sheafCompose (Scheme.smallEtaleTopology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj M) :=
  ModuleCat.Sheaf.ConstantRing.moduleValuedInverseImageUnderlyingIso_unit.{
    u + 1, u, u + 1, u, u + 1, u + 1}
    (siteBaseChange f) (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S) Λ M

/-- Isomorphism of the native unit can be detected before transport by equivalences. -/
theorem moduleInverseImage_unit_map_isIso_iff
    {A : Type*} [Category A] (H : ModuleSheaf X Λ ⥤ A) (M : ModuleSheaf X Λ) :
    IsIso (H.map ((moduleInverseImageAdjunction f Λ).unit.app M)) ↔
      IsIso (((moduleSheafEquivalence X Λ).functor ⋙ H).map
        ((moduleValuedInverseImageAdjunction f Λ).unit.app
          ((moduleSheafEquivalence X Λ).inverse.obj M))) := by
  have hn : IsIso (H.map ((moduleInverseImageAdjunction f Λ).unit.app M)) ↔
      IsIso (H.map ((moduleTransportAdjunction f Λ).unit.app M)) := by
    rw [← moduleInverseImageTransportIso_unit f Λ M, CategoryTheory.Functor.map_comp,
      isIso_comp_right_iff]
  rw [hn]
  let EX := moduleSheafEquivalence X Λ
  let ES := moduleSheafEquivalence S Λ
  let adj := EX.symm.toAdjunction.comp (moduleValuedInverseImageAdjunction f Λ)
  change IsIso (H.map ((adj.comp ES.toAdjunction).unit.app M ≫
    (moduleDirectImageTransportIso f Λ).inv.app
      (((EX.inverse ⋙ moduleValuedInverseImage f Λ) ⋙ ES.functor).obj M))) ↔ _
  rw [CategoryTheory.Functor.map_comp, isIso_comp_right_iff,
    Adjunction.comp_unit_app, CategoryTheory.Functor.map_comp]
  let : IsIso (ES.toAdjunction.unit.app
      ((EX.inverse ⋙ moduleValuedInverseImage f Λ).obj M)) := by
    change IsIso (ES.unitIso.hom.app _)
    infer_instance
  rw [isIso_comp_right_iff]
  change IsIso (H.map ((EX.symm.toAdjunction.comp
    (moduleValuedInverseImageAdjunction f Λ)).unit.app M)) ↔ _
  rw [Adjunction.comp_unit_app, CategoryTheory.Functor.map_comp]
  let : IsIso (EX.symm.toAdjunction.unit.app M) := by
    change IsIso (EX.counitIso.inv.app M)
    infer_instance
  exact isIso_comp_left_iff _ _

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
