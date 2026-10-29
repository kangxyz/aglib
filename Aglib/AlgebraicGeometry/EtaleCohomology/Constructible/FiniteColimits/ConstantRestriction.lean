/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.EtaleRestriction
public import Aglib.CategoryTheory.Sites.ConstantRestriction

/-! # Unit-compatible constant sheaves on actual etale restrictions

Postcomposition with an etale chart is cocontinuous by its native site
adjunction. Restricting the original constant-presheaf unit therefore
remains locally bijective. Its actual sheafification gives a constant
restriction isomorphism with a literal original-unit normalization.
This normalization lets an original coefficient map be identified from
its values on one original etale chart.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteColimits

universe u

attribute [local instance] hasSheafifyLarge

/-- The original constant-presheaf unit, with its original coefficient values. -/
abbrev constantPresheafUnit (X : Scheme.{u}) (A : AddCommGrpCat.{u + 1}) :
    (Functor.const X.Etaleᵒᵖ).obj A ⟶
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A).obj :=
  toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)

/-- Naturality is recorded at the original complete presheaf-map boundary. -/
theorem constantPresheafUnit_naturality (X : Scheme.{u})
    {A B : AddCommGrpCat.{u + 1}} (g : A ⟶ B) :
    constantPresheafUnit X A ≫
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map g).hom =
      (Functor.const X.Etaleᵒᵖ).map g ≫ constantPresheafUnit X B :=
  (toSheafify_naturality X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).map g)).symm

/-- The original constant unit preserves the literal additive value map. -/
theorem constantPresheafUnit_map (X : Scheme.{u}) {A B : AddCommGrpCat.{u + 1}}
    (g : A ⟶ B) (U : X.Etale) (a : A) :
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map g).hom.app (op U)
        ((constantPresheafUnit X A).app (op U) a) =
      (constantPresheafUnit X B).app (op U) (g a) :=
  (ConcreteCategory.congr_hom (congr_app
    (toSheafify_naturality X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).map g))
      (op U)) a).symm

/-- A point of the original test scheme detects equality of constant labels. -/
theorem constantPresheafUnit_injective_at_point (X : Scheme.{u})
    (A : AddCommGrpCat.{u + 1}) (U : X.Etale) (x : U.left) :
    Function.Injective ((constantPresheafUnit X A).app (op U)) := by
  intro a b hab
  have hS := Presheaf.equalizerSieve_mem X.smallEtaleTopology
    (constantPresheafUnit X A) (X := op U) a b hab
  change _ ∈ X.smallGrothendieckTopology @Etale U at hS
  rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
    Scheme.mem_toGrothendieck_smallPretopology] at hS
  obtain ⟨V, g, y, hg, _, _⟩ := hS x
  exact hg

/-- The original constant functor is faithful whenever a base point exists. -/
theorem constant_map_injective_at_point (X : Scheme.{u})
    (A B : AddCommGrpCat.{u + 1}) (x : X) :
    Function.Injective ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map :
      (A ⟶ B) → _) := by
  intro f g hfg
  ext a
  apply constantPresheafUnit_injective_at_point X B (etaleTerminal X) x
  have h := congrArg (fun q => q.hom.app (op (etaleTerminal X))
    ((constantPresheafUnit X A).app (op (etaleTerminal X)) a)) hfg
  simpa only [constantPresheafUnit_map] using h

/-- The actual etale postcomposition functor lifts covering sieves, by its
native adjunction and the proved cover preservation of base change. -/
instance etalePostcompose_isCocontinuous {X S : Scheme.{u}} (p : S ⟶ X) [Etale p] :
    (siteEtalePostcompose p).IsCocontinuous S.smallEtaleTopology X.smallEtaleTopology :=
  (Adjunction.isCocontinuous_iff_coverPreserving
    (J := S.smallEtaleTopology) (K := X.smallEtaleTopology)
      (siteEtalePostcomposeAdj p)).mpr (siteBaseChange_coverPreserving p)

/-- Restrict the original constant-presheaf unit by actual postcomposition. -/
def restrictionConstantMap {X S : Scheme.{u}} (p : S ⟶ X) [Etale p]
    (A : AddCommGrpCat.{u + 1}) :
    (Functor.const S.Etaleᵒᵖ).obj A ⟶
      ((etaleRestriction p).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)).obj :=
  CategoryTheory.Functor.restrictionConstantMap S.smallEtaleTopology X.smallEtaleTopology
    (siteEtalePostcompose p) A

instance restrictionConstantMap_locallyInjective {X S : Scheme.{u}} (p : S ⟶ X) [Etale p]
    (A : AddCommGrpCat.{u + 1}) :
    Presheaf.IsLocallyInjective S.smallEtaleTopology (restrictionConstantMap p A) :=
  CategoryTheory.Functor.restrictionConstantMap_locallyInjective
    S.smallEtaleTopology X.smallEtaleTopology (siteEtalePostcompose p) A

instance restrictionConstantMap_locallySurjective {X S : Scheme.{u}} (p : S ⟶ X) [Etale p]
    (A : AddCommGrpCat.{u + 1}) :
    Presheaf.IsLocallySurjective S.smallEtaleTopology (restrictionConstantMap p A) :=
  CategoryTheory.Functor.restrictionConstantMap_locallySurjective
    S.smallEtaleTopology X.smallEtaleTopology (siteEtalePostcompose p) A

/-- The locally bijective original unit gives an actual constant-restriction
isomorphism, without a point, finiteness or connectedness hypothesis. -/
def etaleRestrictionConstantIso {X S : Scheme.{u}} (p : S ⟶ X) [Etale p]
    (A : AddCommGrpCat.{u + 1}) :
    (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A ≅
      (etaleRestriction p).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A) :=
  CategoryTheory.Functor.constantRestrictionIso S.smallEtaleTopology X.smallEtaleTopology
    (siteEtalePostcompose p) A

/-- The restriction isomorphism retains the original constant-presheaf unit. -/
theorem etaleRestrictionConstantIso_unit {X S : Scheme.{u}} (p : S ⟶ X) [Etale p]
    (A : AddCommGrpCat.{u + 1}) :
    constantPresheafUnit S A ≫ (etaleRestrictionConstantIso p A).hom.hom =
      restrictionConstantMap p A :=
  CategoryTheory.Functor.constantRestrictionIso_unit S.smallEtaleTopology X.smallEtaleTopology
    (siteEtalePostcompose p) A

/-- Literal values on one original chart determine the full restricted
coefficient map after the unit-compatible constant identifications. -/
theorem etaleRestriction_map_constant_of_unit_eq {X : Scheme.{u}} (U : X.Etale)
    (A B : AddCommGrpCat.{u + 1})
    (q : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A ⟶
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj B)
    (g : A ⟶ B)
    (h : ∀ a, (constantPresheafUnit X B).app (op U) (g a) =
      q.hom.app (op U) ((constantPresheafUnit X A).app (op U) a)) :
    (etaleRestrictionConstantIso U.hom A).hom ≫ (etaleRestriction U.hom).map q =
      (constantSheaf U.left.smallEtaleTopology AddCommGrpCat.{u + 1}).map g ≫
        (etaleRestrictionConstantIso U.hom B).hom :=
  CategoryTheory.Functor.constantRestriction_map_of_unit_eq
    U.left.smallEtaleTopology X.smallEtaleTopology (siteEtalePostcompose U.hom)
    (U := U) (fun V => MorphismProperty.Over.homMk V.hom rfl (by trivial)) A B q g h

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteColimits
