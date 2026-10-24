/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantImages
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteCoefficientPullback

/-! # Actual constant-ring module coefficients on the small etale site

The coefficient category and image functors are the native ModuleCat-valued
site constructions. Their underlying comparisons use the original abelian
image functors; identity, composition and constant transports use the native
adjunctions and actual base changes of etale test schemes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R]

/-- Genuine constant-ring module-valued sheaves in the original coefficient universe. -/
abbrev ModuleSheaf (X : Scheme.{u}) := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)

/-- The original underlying abelian coefficient functor. -/
abbrev moduleUnderlying (X : Scheme.{u}) : ModuleSheaf R X ⥤ AbelianSheaf.{u, u + 1} X :=
  ModuleCat.Sheaf.underlying R X.smallEtaleTopology

/-- The actual native inverse image of constant-ring module coefficients. -/
abbrev moduleInverseImage {X S : Scheme.{u}} (f : S ⟶ X) :
    ModuleSheaf R X ⥤ ModuleSheaf R S :=
  (siteBaseChange f).sheafPullback (ModuleCat.{u + 1} R)
    X.smallEtaleTopology S.smallEtaleTopology

/-- The actual native direct image of constant-ring module coefficients. -/
abbrev moduleDirectImage {X S : Scheme.{u}} (f : S ⟶ X) :
    ModuleSheaf R S ⥤ ModuleSheaf R X :=
  (siteBaseChange f).sheafPushforwardContinuous (ModuleCat.{u + 1} R)
    X.smallEtaleTopology S.smallEtaleTopology

/-- The native image adjunction, with no replacement of either image functor. -/
abbrev moduleImageAdjunction {X S : Scheme.{u}} (f : S ⟶ X) :
    moduleInverseImage R f ⊣ moduleDirectImage R f :=
  (siteBaseChange f).sheafAdjunctionContinuous (ModuleCat.{u + 1} R)
    X.smallEtaleTopology S.smallEtaleTopology

/-- The original abelian inverse image of the original underlying coefficient. -/
def moduleInverseImageUnderlyingIso {X S : Scheme.{u}} (f : S ⟶ X) :
    moduleInverseImage R f ⋙ moduleUnderlying R S ≅
      moduleUnderlying R X ⋙ inverseImage f :=
  ModuleCat.Sheaf.pullbackUnderlyingIso R (siteBaseChange f)
    X.smallEtaleTopology S.smallEtaleTopology

/-- Direct image retains the literal original underlying abelian sheaf. -/
def moduleDirectImageUnderlyingIso {X S : Scheme.{u}} (f : S ⟶ X) :
    moduleDirectImage R f ⋙ moduleUnderlying R X ≅
      moduleUnderlying R S ⋙ directImage f :=
  ModuleCat.Sheaf.pushforwardUnderlyingIso R (siteBaseChange f)
    X.smallEtaleTopology S.smallEtaleTopology

/-- The original constant module sheaf and the original constant abelian sheaf. -/
def moduleConstantUnderlyingIso (X : Scheme.{u}) :
    constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⋙ moduleUnderlying R X ≅
      forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1} ⋙
        constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ModuleCat.Sheaf.constantUnderlyingIso R X.smallEtaleTopology

/-- Module inverse image is exact along every scheme morphism. -/
instance moduleInverseImage_preservesFiniteLimits {X S : Scheme.{u}} (f : S ⟶ X) :
    PreservesFiniteLimits (moduleInverseImage R f) := by
  have := flat_of_preservesFiniteLimits (siteBaseChange f)
  exact ModuleCat.Sheaf.pullback_preservesFiniteLimits R (siteBaseChange f)
    X.smallEtaleTopology S.smallEtaleTopology

/-- Constant module coefficients commute with native inverse image. -/
def moduleInverseImageConstantIso {X S : Scheme.{u}} (f : S ⟶ X) :
    constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⋙ moduleInverseImage R f ≅
      constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} R) :=
  ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} R)
    (etaleTerminalIsTerminal X)).comp (moduleImageAdjunction R f)).leftAdjointUniq
      (constantSheafAdj S.smallEtaleTopology (ModuleCat.{u + 1} R)
        ((etaleTerminalIsTerminal X).isTerminalObj (siteBaseChange f)))

/-- Native module inverse images compose with the original scheme base changes. -/
def moduleInverseImageComp {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) :
    moduleInverseImage R (g ≫ f) ≅ moduleInverseImage R f ⋙ moduleInverseImage R g := by
  let e := Functor.sheafPushforwardContinuousComp' (siteBaseChangeComp f g).symm
    (ModuleCat.{u + 1} R) X.smallEtaleTopology S.smallEtaleTopology T.smallEtaleTopology
  exact (Adjunction.leftAdjointCompIso (moduleImageAdjunction R f)
    (moduleImageAdjunction R g) (moduleImageAdjunction R (g ≫ f)) e).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
