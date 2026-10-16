/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.Restriction
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.FreeTop
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Rank
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic

/-!
# The actual top exterior line on the original local basis cover

An actual local basis of fixed rank supplies a local determinant frame of
the original sheaf exterior power. The resulting singleton local bases
retain exactly the original covering index and opens. Thus the top exterior
power has rank one and defines an object of the existing line-bundle type.
All schemes and coefficient rings are allowed, including rank zero.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})

/-- The top exterior frame determined by an actual ordered local free presentation. -/
def moduleExteriorTopOverIso (M : X.Modules) (n : ℕ) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.free
      (R := X.ringCatSheaf.over U) (ULift.{u} (Fin n))) :
    (moduleExteriorPower X M n).over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (moduleExteriorPowerOverIso X M n U).symm ≪≫
    (SheafOfModulesOfCommRing.exteriorPowerFunctor (X.sheaf.over U) n).mapIso e ≪≫
      SheafOfModulesOfCommRing.exteriorTopFreeIso (X.sheaf.over U) n

/-- The local frame evaluates original wedges by the determinant of their original coordinates. -/
theorem moduleExteriorTopOverIso_mk (M : X.Modules) (n : ℕ) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.free
      (R := X.ringCatSheaf.over U) (ULift.{u} (Fin n)))
    (V : (Over U)ᵒᵖ) (s : Fin n → (M.over U).val.obj V) :
    (moduleExteriorTopOverIso X M n U e).hom.val.app V
        ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf M n).app
          ((Over.forget U).op.obj V) s) =
      (SheafOfModulesOfCommRing.freeFinSectionsBasis (X.sheaf.over U) n V).det
        (fun i => e.hom.val.app V (s i)) := by
  change (SheafOfModulesOfCommRing.exteriorTopFreeHom (X.sheaf.over U) n).val.app V
      (((SheafOfModulesOfCommRing.exteriorPowerFunctor (X.sheaf.over U) n).map e.hom).val.app V
        ((moduleExteriorPowerOverIso X M n U).inv.val.app V
          ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf M n).app
            ((Over.forget U).op.obj V) s))) = _
  exact (congrArg
    (fun z => (SheafOfModulesOfCommRing.exteriorTopFreeHom (X.sheaf.over U) n).val.app V
      (((SheafOfModulesOfCommRing.exteriorPowerFunctor (X.sheaf.over U) n).map e.hom).val.app V z))
    (moduleExteriorPowerOverIso_inv_mk X M n U V s)).trans
    ((congrArg
      ((SheafOfModulesOfCommRing.exteriorTopFreeHom (X.sheaf.over U) n).val.app V)
      (SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk
        (X.sheaf.over U) e.hom n V s)).trans
      (SheafOfModulesOfCommRing.exteriorTopFreeHom_mk
        (X.sheaf.over U) n V (fun i => e.hom.val.app V (s i))))

variable (M : X.Modules) (n : ℕ) (q : M.LocalGeneratorsData.{u}) [q.IsLocallyFreeData]
  (e : ∀ i, (q.generators i).I ≃ Fin n)

/-- The determinant trivializations use precisely the original local basis presentations. -/
def moduleExteriorTopLocalIso (i : q.I) :
    (moduleExteriorPower X M n).over (q.X i) ≅
      SheafOfModules.unit (X.ringCatSheaf.over (q.X i)) :=
  moduleExteriorTopOverIso X M n (q.X i)
    ((asIso (q.generators i).π).symm ≪≫
      (SheafOfModules.freeFunctor (R := X.ringCatSheaf.over (q.X i))).mapIso
        ((e i).trans Equiv.ulift.symm).toIso)

/-- The singleton local free presentations induced by the original determinant frames. -/
def moduleExteriorTopLocalFreeIso (i : q.I) :
    SheafOfModules.free (R := X.ringCatSheaf.over (q.X i)) PUnit.{u + 1} ≅
      (moduleExteriorPower X M n).over (q.X i) :=
  coproductUniqueIso (fun _ : PUnit.{u + 1} =>
    SheafOfModules.unit (X.ringCatSheaf.over (q.X i))) ≪≫
      (moduleExteriorTopLocalIso X M n q e i).symm

/-- Top exterior singleton bases on exactly the given covering opens and index set. -/
def moduleExteriorTopGeneratorsData : (moduleExteriorPower X M n).LocalGeneratorsData.{u} where
  I := q.I
  X := q.X
  coversTop := q.coversTop
  generators i :=
    (SheafOfModules.free.generatingSections
      (R := X.ringCatSheaf.over (q.X i)) PUnit.{u + 1}).ofEpi
        (moduleExteriorTopLocalFreeIso X M n q e i).hom

/-- The covering index is the original one. -/
theorem moduleExteriorTopGeneratorsData_I :
    (moduleExteriorTopGeneratorsData X M n q e).I = q.I := rfl

/-- The covering opens are the original ones. -/
theorem moduleExteriorTopGeneratorsData_X (i : q.I) :
    (moduleExteriorTopGeneratorsData X M n q e).X i = q.X i := rfl

instance moduleExteriorTopGeneratorsData_isLocallyFree :
    (moduleExteriorTopGeneratorsData X M n q e).IsLocallyFreeData where
  isIso i := by
    change q.I at i
    exact inferInstanceAs (IsIso
      ((SheafOfModules.free.generatingSections
        (R := X.ringCatSheaf.over (q.X i)) PUnit.{u + 1}).ofEpi
          (moduleExteriorTopLocalFreeIso X M n q e i).hom).π)

instance moduleExteriorTopGeneratorsData_isFiniteType :
    (moduleExteriorTopGeneratorsData X M n q e).IsFiniteType where
  isFiniteType i := by
    constructor
    change Finite PUnit.{u + 1}
    infer_instance

omit [q.IsLocallyFreeData] in
/-- The top exterior power of a displayed rank-`n` sheaf has the existing
local rank-one property. -/
theorem moduleExteriorTop_isLocallyRankOne (hM : SheafHasRank M n) :
    Invertible.IsLocallyRankOne X (moduleExteriorPower X M n) := by
  classical
  obtain ⟨q, hq, he⟩ := hM
  let := hq
  exact ⟨moduleExteriorTopGeneratorsData X M n q (fun i => (he i).some),
    inferInstance, fun _ => ⟨Equiv.refl _⟩⟩

omit [q.IsLocallyFreeData] in
/-- The top exterior power has rank one in the original fixed-rank interface, including `n = 0`. -/
theorem moduleExteriorTop_hasRank (hM : SheafHasRank M n) :
    SheafHasRank (moduleExteriorPower X M n) 1 := by
  classical
  obtain ⟨q, hq, he⟩ := hM
  let := hq
  refine ⟨moduleExteriorTopGeneratorsData X M n q (fun i => (he i).some),
    inferInstance, fun _ => ?_⟩
  exact ⟨Equiv.ofUnique PUnit.{u + 1} (Fin 1)⟩

omit [q.IsLocallyFreeData] in
/-- Fixed-rank top exterior powers are finite locally free without a Noetherian hypothesis. -/
theorem moduleExteriorTop_isFiniteLocallyFree (hM : SheafHasRank M n) :
    IsFiniteLocallyFree X (moduleExteriorPower X M n) :=
  (moduleExteriorTop_hasRank X M n hM).isFiniteLocallyFree

omit [q.IsLocallyFreeData] in
/-- The actual top exterior sheaf in the existing line-bundle type. -/
def moduleDeterminantLineBundle (hM : SheafHasRank M n) : Invertible.LineBundle X :=
  ⟨moduleExteriorPower X M n, moduleExteriorTop_isLocallyRankOne X M n hM⟩

end AlgebraicGeometry.Scheme.Modules
