/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.GlobalHom
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Unit

/-!
# The selected lifted unit at the original tensor-Hom boundary

The cohomology comparison uses the existing lifted rank-one module, while the
native tensor construction uses its original unit. At aligned carrier size,
the actual componentwise ULift equivalence identifies these two existing units.
Whiskering the original global-Hom comparison by this specified isomorphism
retains the selected cohomological unit; no new module realization is propagated.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe c h r

namespace SheafOfModules

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{r})

/-- The aligned lifted unit is identified with the native tensor unit by the actual ULift maps. -/
def liftedUnitIso : liftedUnit.{c, h, r, r} R ≅ unit R where
  hom.val :=
    { app := fun U => ModuleCat.ofHom (ULift.moduleEquiv.toLinearMap)
      naturality := by intros; ext; rfl }
  inv.val :=
    { app := fun U => ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap)
      naturality := by intros; ext; rfl }
  hom_inv_id := by ext U; rfl
  inv_hom_id := by ext U; rfl

/-- The original forward unit map forgets exactly the existing ULift wrapper. -/
theorem liftedUnitIso_hom_app (U : Cᵒᵖ) (x : (liftedUnit.{c, h, r, r} R).val.obj U) :
    (liftedUnitIso R).hom.val.app U x = x.down := rfl

/-- The original inverse unit map inserts exactly the existing ULift wrapper. -/
theorem liftedUnitIso_inv_app (U : Cᵒᵖ) (x : (unit R).val.obj U) :
    (liftedUnitIso R).inv.val.app U x = ULift.up x := rfl

end SheafOfModules

namespace SheafOfModules.InternalHom

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c h r} RingCat.{max c h r})]
  (R : Sheaf J CommRingCat.{max c h r})
  [HasSheafify J AddCommGrpCat.{max c h r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c h r}]

/-- The whole original global-Hom comparison retains the chosen lifted cohomological unit. -/
def liftedUnitCoyonedaIso (M : SheafOfModulesOfCommRing R) :
    homFunctor.{c, h, r} R M ⋙
        preadditiveCoyoneda.obj (op (SheafOfModules.liftedUnit.{c, h, max c h r, max c h r}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) ≅
      preadditiveCoyoneda.obj (op M) :=
  Functor.isoWhiskerLeft (homFunctor.{c, h, r} R M)
      (preadditiveCoyoneda.mapIso
        (SheafOfModules.liftedUnitIso
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).symm.op)
    ≪≫ unitCoyonedaIso.{c, h, r} R M

/-- The lifted-unit comparison is original unit precomposition followed by uncurrying. -/
theorem liftedUnitCoyonedaIso_hom_app_apply (M N : SheafOfModulesOfCommRing R)
    (f : SheafOfModules.liftedUnit.{c, h, max c h r, max c h r}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⟶ sheaf R M N) :
    (liftedUnitCoyonedaIso.{c, h, r} R M).hom.app N f =
      unitHomAddEquiv.{c, h, r} R M N
        ((SheafOfModules.liftedUnitIso
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).inv ≫ f) := rfl

end SheafOfModules.InternalHom
