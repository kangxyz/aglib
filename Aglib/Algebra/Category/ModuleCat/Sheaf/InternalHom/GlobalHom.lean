/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.Additive

/-!
# The whole original global-Hom comparison for internal Hom

Maps from the actual unit module into the existing internal Hom identify with
maps from its source into its target. The comparison uses the same tensor-Hom
adjunction and the inverse of the original tensor left unitor. It is assembled
as a natural isomorphism of additive Hom functors before object evaluation.
Both coefficient naturalities retain the original slice precomposition,
postcomposition and uncurrying maps. No acyclicity or Ext comparison is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModulesOfCommRing (tensorProduct tensorMap tensorLeftUnitIso)

universe uC vC r

namespace SheafOfModules.InternalHom

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
  (R : Sheaf J CommRingCat.{max uC vC r})
  [HasSheafify J AddCommGrpCat.{max uC vC r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]

/-- Uncurrying source precomposition is tensoring that same source arrow. -/
theorem uncurry_precompose {M M' N P : SheafOfModulesOfCommRing R}
    (a : M' ⟶ M) (h : N ⟶ sheaf R M P) :
    uncurry.{uC, vC, r} R N M' P (h ≫ map R a (𝟙 P)) =
      tensorMap R (𝟙 N) a ≫ uncurry.{uC, vC, r} R N M P h := by
  apply SheafOfModulesOfCommRing.tensor_hom_ext R
  intro U x y
  refine (uncurry_tmul.{uC, vC, r} R N M' P (h ≫ map R a (𝟙 P)) U x y).trans
    ((map_apply R a (𝟙 P) U.unop (h.val.app U x) (op (Over.mk (𝟙 U.unop))) y).trans ?_)
  exact (((congrArg (fun z : (tensorProduct R N M).val.obj U =>
      (uncurry.{uC, vC, r} R N M P h).val.app U z)
      (SheafOfModulesOfCommRing.tensor_map_tensorSection R (𝟙 N) a U x y)).trans
    (uncurry_tmul.{uC, vC, r} R N M P h U x (a.val.app U y)))).symm

/-- The original tensor-Hom adjunction and unit give the global additive Hom equivalence. -/
def unitHomAddEquiv (M N : SheafOfModulesOfCommRing R) :
    (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⟶
        sheaf R M N) ≃+ (M ⟶ N) :=
  ((tensorHomAdjunction.{uC, vC, r} R M).homAddEquiv
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) N).symm.trans
    ((preadditiveCoyoneda.mapIso
      ((tensorLeftUnitIso R).app M).symm.op).app N).addCommGroupIsoToAddEquiv

/-- The comparison is original uncurrying after the inverse original tensor unitor. -/
theorem unitHomAddEquiv_apply (M N : SheafOfModulesOfCommRing R)
    (h : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⟶
      sheaf R M N) :
    unitHomAddEquiv.{uC, vC, r} R M N h =
      (tensorLeftUnitIso R).inv.app M ≫ uncurry.{uC, vC, r} R _ M N h := by
  change (tensorLeftUnitIso R).inv.app M ≫
      ((tensorHomAdjunction.{uC, vC, r} R M).homEquiv _ N).symm h = _
  rw [tensorHomAdjunction_homEquiv]
  rfl

/-- The original global-Hom comparison is natural in the target coefficient. -/
theorem unitHomAddEquiv_naturality (M : SheafOfModulesOfCommRing R)
    {N N' : SheafOfModulesOfCommRing R} (b : N ⟶ N')
    (h : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⟶
      sheaf R M N) :
    unitHomAddEquiv.{uC, vC, r} R M N' (h ≫ map R (𝟙 M) b) =
      unitHomAddEquiv.{uC, vC, r} R M N h ≫ b := by
  rw [unitHomAddEquiv_apply, unitHomAddEquiv_apply, uncurry_map, Category.assoc]

/-- The whole comparison is an isomorphism of the original additive Hom functors. -/
def unitCoyonedaIso (M : SheafOfModulesOfCommRing R) :
    homFunctor.{uC, vC, r} R M ⋙
        preadditiveCoyoneda.obj
          (op (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) ≅
      preadditiveCoyoneda.obj (op M) :=
  NatIso.ofComponents (fun N => (unitHomAddEquiv.{uC, vC, r} R M N).toAddCommGrpIso) (fun b => by
    ext h
    exact unitHomAddEquiv_naturality.{uC, vC, r} R M b h)

/-- Evaluation of the whole comparison is the original unit-Hom additive equivalence. -/
theorem unitCoyonedaIso_hom_app_apply (M N : SheafOfModulesOfCommRing R)
    (h : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⟶
      sheaf R M N) :
    (unitCoyonedaIso.{uC, vC, r} R M).hom.app N h = unitHomAddEquiv.{uC, vC, r} R M N h := rfl

/-- The global-Hom comparison retains the original source-coefficient naturality. -/
theorem unitHomAddEquiv_precompose {M M' N : SheafOfModulesOfCommRing R}
    (a : M' ⟶ M)
    (h : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⟶
      sheaf R M N) :
    unitHomAddEquiv.{uC, vC, r} R M' N (h ≫ map R a (𝟙 N)) =
      a ≫ unitHomAddEquiv.{uC, vC, r} R M N h := by
  rw [unitHomAddEquiv_apply, unitHomAddEquiv_apply, uncurry_precompose]
  have hu := (tensorLeftUnitIso R).inv.naturality a
  change a ≫ (tensorLeftUnitIso R).inv.app M =
    (tensorLeftUnitIso R).inv.app M' ≫ tensorMap R (𝟙 _) a at hu
  rw [← Category.assoc, ← hu, Category.assoc]

/-- The source-coefficient square holds for the whole original natural transformations. -/
theorem unitCoyonedaIso_precompose {M M' : SheafOfModulesOfCommRing R} (a : M' ⟶ M) :
    Functor.whiskerRight (precomposeNatTrans.{uC, vC, r} R a)
        (preadditiveCoyoneda.obj
          (op (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))) ≫
        (unitCoyonedaIso.{uC, vC, r} R M').hom =
      (unitCoyonedaIso.{uC, vC, r} R M).hom ≫ preadditiveCoyoneda.map a.op := by
  ext N h
  exact unitHomAddEquiv_precompose.{uC, vC, r} R a h

end SheafOfModules.InternalHom
