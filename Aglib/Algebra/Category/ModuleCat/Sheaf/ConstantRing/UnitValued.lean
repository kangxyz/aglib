/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.UnitUnderlying
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Underlying

/-!
# The original constant-unit map as a module-valued map

The existing moduleUnitConstantMap is linear for the original coefficient
actions. Regard the same functions as a ModuleCat-valued natural transformation
through the existing inverse coefficient equivalence. Its underlying additive
map is exactly the original map, so its proved local bijectivity is retained.
This supplies the actual injective constant-value map used by the local Hom
boundary induction, without choosing another unit or scalar ring.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe c h w

namespace ModuleCat.Sheaf.ConstantRing

variable {C : Type c} [Category.{h} C] (J : GrothendieckTopology C)
  (Λ : Type w) [Ring Λ] [HasWeakSheafify J RingCat.{w}]
  [J.WEqualsLocallyBijective RingCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]

/-- The existing constant-unit functions are linear for the original coefficient actions. -/
def moduleUnitConstantLinearMap :
    (Functor.const Cᵒᵖ).obj (ModuleCat.of Λ Λ) ⟶
      ((moduleSheafEquivalence J Λ).inverse.obj (moduleUnit J Λ)).obj where
  app U := ModuleCat.ofHom (X := ModuleCat.of Λ Λ)
    (Y := ((moduleSheafEquivalence J Λ).inverse.obj (moduleUnit J Λ)).obj.obj U) {
    toFun := fun a => (moduleUnitConstantMap J Λ).app U a
    map_add' a b := ((moduleUnitConstantMap J Λ).app U).hom.map_add a b
    map_smul' a b := by
      change ULift.up ((constantRingUnit J Λ).app U (a * b)) =
        ULift.up ((constantRingUnit J Λ).app U a * (constantRingUnit J Λ).app U b)
      exact congrArg ULift.up (((constantRingUnit J Λ).app U).hom.map_mul a b) }
  naturality U V f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact NatTrans.naturality_apply (moduleUnitConstantMap J Λ) f a

/-- Forgetting scalars gives exactly the original constant-unit natural transformation. -/
theorem moduleUnitConstantLinearMap_underlying :
    Functor.whiskerRight (moduleUnitConstantLinearMap J Λ)
        (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w}) = moduleUnitConstantMap J Λ := by
  ext U a
  rfl

/-- The module-valued unit has the original constant-ring-unit component function. -/
theorem moduleUnitConstantLinearMap_app (U : Cᵒᵖ) (a : Λ) :
    (moduleUnitConstantLinearMap J Λ).app U a =
      ULift.up ((constantRingUnit J Λ).app U a) := rfl

/-- The original module-valued constant-unit map is locally surjective. -/
instance moduleUnitConstantLinearMap_isLocallySurjective :
    CategoryTheory.Presheaf.IsLocallySurjective J (moduleUnitConstantLinearMap J Λ) := by
  let : CategoryTheory.Presheaf.IsLocallySurjective J (moduleUnitConstantMap J Λ) :=
    moduleUnitConstantMap_isLocallySurjective J Λ
  rw [CategoryTheory.Presheaf.isLocallySurjective_iff_whisker_forget]
  change CategoryTheory.Presheaf.IsLocallySurjective J
    (Functor.whiskerRight (moduleUnitConstantMap J Λ)
      (CategoryTheory.forget AddCommGrpCat.{w}))
  infer_instance

/-- The original module-valued constant-unit map is locally injective. -/
instance moduleUnitConstantLinearMap_isLocallyInjective :
    CategoryTheory.Presheaf.IsLocallyInjective J (moduleUnitConstantLinearMap J Λ) := by
  let : CategoryTheory.Presheaf.IsLocallyInjective J (moduleUnitConstantMap J Λ) :=
    moduleUnitConstantMap_isLocallyInjective J Λ
  rw [← CategoryTheory.Presheaf.isLocallyInjective_forget_iff]
  change CategoryTheory.Presheaf.IsLocallyInjective J
    (Functor.whiskerRight (moduleUnitConstantMap J Λ)
      (CategoryTheory.forget AddCommGrpCat.{w}))
  infer_instance

end ModuleCat.Sheaf.ConstantRing
