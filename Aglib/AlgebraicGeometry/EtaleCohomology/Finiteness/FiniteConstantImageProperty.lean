/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finiteness.HigherImageFiniteCogenerators
public import Mathlib.Algebra.Category.Grp.Ulift

/-! # The original finite-constant image property in one fixed degree

The same coefficient functor and finite-product construction are shared by
fixed-degree consumers. No extension closure in other degrees is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.FiniteConstantImage

universe u

attribute [local instance] hasSheafifyLarge HasDerivedCategory.standard

/-- The constant abelian sheaf of a small coefficient group. -/
abbrev coefficientFunctor (X : Scheme.{u}) :
    AddCommGrpCat.{u} ⥤ AbelianSheaf.{u, u + 1} X :=
  AddCommGrpCat.uliftFunctor.{u + 1, u} ⋙
    constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}

instance coefficientFunctor_additive (X : Scheme.{u}) :
    (coefficientFunctor X).Additive := by
  dsimp [coefficientFunctor, constantSheaf]
  infer_instance

instance coefficientFunctor_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (coefficientFunctor X) := by
  dsimp [coefficientFunctor, constantSheaf]
  infer_instance

/-- Constructibility of the higher image of the constant coefficient sheaf. -/
abbrev property {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ) :
    ObjectProperty AddCommGrpCat.{u} :=
  let Q : ObjectProperty (AbelianSheaf.{u, u + 1} S) := Constructible.IsConstructible
  Q.inverseImage (coefficientFunctor X ⋙ higherDirectImage f q)

instance property_iso {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ) :
    (property f q).IsClosedUnderIsomorphisms := by
  dsimp [property]
  infer_instance

instance property_products {X S : Scheme.{u}} (f : X ⟶ S) (q : ℕ) :
    (property f q).IsClosedUnderFiniteProducts := by
  let Q : ObjectProperty (AbelianSheaf.{u, u + 1} S) := Constructible.IsConstructible
  let : Q.IsClosedUnderIsomorphisms := inferInstance
  let : Q.IsClosedUnderFiniteProducts := by
    constructor
    intro J _
    apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
    rintro _ ⟨E, hE⟩
    exact Q.prop_of_iso (Pi.isoLimit E)
      (Constructible.FiniteCogenerators.isConstructible_finiteProduct
        (fun j : J => E.obj ⟨j⟩) (fun j => hE ⟨j⟩))
  constructor
  intro J _
  change (Q.inverseImage (coefficientFunctor X ⋙ higherDirectImage f q)).IsClosedUnderLimitsOfShape
    (Discrete J)
  infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology.FiniteConstantImage
