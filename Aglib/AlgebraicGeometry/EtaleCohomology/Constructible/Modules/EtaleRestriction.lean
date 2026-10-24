/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Images
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.EtaleRestriction

/-! # Actual etale restriction of constant-ring module sheaves

Native module inverse image along an etale morphism agrees with original
precomposition restriction by uniqueness of the original image adjunction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R]

/-- The original precomposition restriction of module sheaves to an etale chart. -/
abbrev moduleEtaleRestriction {X S : Scheme.{u}} (f : S ⟶ X) [Etale f] :
    ModuleSheaf R X ⥤ ModuleSheaf R S :=
  (siteEtalePostcompose f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
    S.smallEtaleTopology X.smallEtaleTopology

/-- Native module inverse image agrees with actual etale chart restriction. -/
def moduleInverseImageEtaleIso {X S : Scheme.{u}} (f : S ⟶ X) [Etale f] :
    moduleInverseImage R f ≅ moduleEtaleRestriction R f :=
  (moduleImageAdjunction R f).leftAdjointUniq
    ((siteEtalePostcomposeAdj f).sheafPushforwardContinuous (E := ModuleCat.{u + 1} R)
      S.smallEtaleTopology X.smallEtaleTopology)

/-- The chart comparison retains the original inverse-image adjunction unit. -/
@[reassoc]
theorem moduleInverseImageEtaleIso_unit {X S : Scheme.{u}} (f : S ⟶ X) [Etale f]
    (F : ModuleSheaf R X) :
    (moduleImageAdjunction R f).unit.app F ≫
      (moduleDirectImage R f).map ((moduleInverseImageEtaleIso R f).hom.app F) =
    ((siteEtalePostcomposeAdj f).sheafPushforwardContinuous (E := ModuleCat.{u + 1} R)
      S.smallEtaleTopology X.smallEtaleTopology).unit.app F :=
  Adjunction.unit_leftAdjointUniq_hom_app (moduleImageAdjunction R f)
    ((siteEtalePostcomposeAdj f).sheafPushforwardContinuous (E := ModuleCat.{u + 1} R)
      S.smallEtaleTopology X.smallEtaleTopology) F

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
