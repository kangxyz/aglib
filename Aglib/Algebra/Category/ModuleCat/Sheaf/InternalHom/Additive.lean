/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.TensorAdjunction
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Additive and left exact structure of the original internal Hom

The existing internal-Hom right adjoint is additive and preserves limits. Its
source-variable maps are the existing slice precomposition maps, assembled as
whole natural transformations and a contravariant functor. Identity and
composition laws use the same native maps. No exactness of tensor with the
source, local freeness, finiteness or preservation of injectives is asserted.

Sources: `InternalHom/TensorAdjunction` for the actual adjunction and
`InternalHom/Functor` for its original two-variable coefficient maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe uC vC r

namespace SheafOfModules.InternalHom

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
  (R : Sheaf J CommRingCat.{max uC vC r})

/-- The original internal-Hom functor is additive on its actual slice coefficient maps. -/
instance homFunctor_additive (M : SheafOfModulesOfCommRing R) :
    (homFunctor.{uC, vC, r} R M).Additive where
  map_add {X Y f g} := by
    apply SheafOfModules.hom_ext
    ext U : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    change (_ : RawHom R M _ U.unop) = _
    ext V m
    rfl

/-- Original source precomposition, as a whole natural transformation in the target. -/
def precomposeNatTrans {M M' : SheafOfModulesOfCommRing R} (a : M' ⟶ M) :
    homFunctor.{uC, vC, r} R M ⟶ homFunctor.{uC, vC, r} R M' where
  app N := map R a (𝟙 N)
  naturality N N' b := by
    change map R (𝟙 M) b ≫ map R a (𝟙 N') =
      map R a (𝟙 N) ≫ map R (𝟙 M') b
    rw [map_comp, map_comp]
    simp

/-- Evaluation of source precomposition is the original two-variable Hom map. -/
theorem precomposeNatTrans_app {M M' : SheafOfModulesOfCommRing R}
    (a : M' ⟶ M) (N : SheafOfModulesOfCommRing R) :
    (precomposeNatTrans.{uC, vC, r} R a).app N = map R a (𝟙 N) := rfl

/-- Whole source precomposition preserves identities. -/
@[simp]
theorem precomposeNatTrans_id (M : SheafOfModulesOfCommRing R) :
    precomposeNatTrans.{uC, vC, r} R (𝟙 M) = 𝟙 (homFunctor.{uC, vC, r} R M) := by
  apply NatTrans.ext
  funext N
  exact map_id R

/-- Whole source precomposition reverses composition on the original arrows. -/
theorem precomposeNatTrans_comp {M M' M'' : SheafOfModulesOfCommRing R}
    (a : M' ⟶ M) (b : M'' ⟶ M') :
    precomposeNatTrans.{uC, vC, r} R a ≫ precomposeNatTrans.{uC, vC, r} R b =
      precomposeNatTrans.{uC, vC, r} R (b ≫ a) := by
  apply NatTrans.ext
  funext N
  change map R a (𝟙 N) ≫ map R b (𝟙 N) = map R (b ≫ a) (𝟙 N)
  simpa only [Category.id_comp] using map_comp R a (𝟙 N) b (𝟙 N)

/-- The existing internal Hom as a functor in both original variables. -/
def bifunctor : (SheafOfModulesOfCommRing R)ᵒᵖ ⥤
    SheafOfModulesOfCommRing R ⥤ SheafOfModulesOfCommRing R where
  obj M := homFunctor.{uC, vC, r} R M.unop
  map a := precomposeNatTrans.{uC, vC, r} R a.unop
  map_id M := precomposeNatTrans_id.{uC, vC, r} R M.unop
  map_comp a b := (precomposeNatTrans_comp.{uC, vC, r} R a.unop b.unop).symm

section TensorAdjunction

variable [HasSheafify J AddCommGrpCat.{max uC vC r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]

/-- The existing right-tensor functor is additive through the original adjunction. -/
instance tensorRightFunctor_additive (M : SheafOfModulesOfCommRing R) :
    (tensorRightFunctor.{uC, vC, r} R M).Additive :=
  (tensorHomAdjunction.{uC, vC, r} R M).left_adjoint_additive

/-- The original tensor-Hom adjunction exhibits the existing Hom functor as a right adjoint. -/
instance homFunctor_isRightAdjoint (M : SheafOfModulesOfCommRing R) :
    (homFunctor.{uC, vC, r} R M).IsRightAdjoint :=
  (tensorHomAdjunction.{uC, vC, r} R M).isRightAdjoint

/-- The original Hom functor preserves finite limits, with no local-freeness premise. -/
instance homFunctor_preservesFiniteLimits (M : SheafOfModulesOfCommRing R) :
    PreservesFiniteLimits (homFunctor.{uC, vC, r} R M) := inferInstance

end TensorAdjunction

end SheafOfModules.InternalHom
