/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Module.TransferInstance

/-!
# The actual target-ring action on ambient Ext

The original native Ext carrier receives an explicit, non-global target-ring
module structure through native higher coinduction. Its scalar action is proved
to be the original Yoneda precomposition, and restriction along the original
ring map recovers the unchanged ambient scalar action. No action of the target
ring on the coefficient is assumed. The installed derived-homology comparison
is linear for this same action, independently of its injective resolution.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Abelian
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w a b
namespace ModuleCat
variable {R S : Type u} [CommRing R] [CommRing S]
  [HasExt.{w} (ModuleCat.{u} R)] (q : R →+* S) (N : ModuleCat.{u} R) (n : ℕ)

/-- Explicit target-ring action on the original Ext carrier; not a global instance. -/
@[instance_reducible]
def coinducedExtSourceModule :
    Module S (Ext.{w} ((restrictScalars q).obj (ModuleCat.of S S)) N n) :=
  (coextendScalarsRightDerivedExtAddEquiv q N (injectiveResolution N) n).symm.module S

/-- Every target scalar is the original native Yoneda source multiplication. -/
theorem coinducedExtSourceModule_smul (s : S)
    (x : Ext.{w} ((restrictScalars q).obj (ModuleCat.of S S)) N n) :
    letI := coinducedExtSourceModule q N n
    s • x = (Ext.mk₀ ((restrictScalars q).map
      (ModuleCat.ofHom (LinearMap.mulRight S s)))).comp x (zero_add n) := by
  let E := coextendScalarsRightDerivedExtAddEquiv q N (injectiveResolution N) n
  change E (s • E.symm x) = _
  rw [coextendScalarsRightDerivedExtAddEquiv_smul, E.apply_symm_apply]

/-- Restriction of this source action is the original ambient Ext action. -/
@[simp]
theorem coinducedExtSourceModule_map_smul (r : R)
    (x : Ext.{w} ((restrictScalars q).obj (ModuleCat.of S S)) N n) :
    letI := coinducedExtSourceModule q N n
    q r • x = r • x := by
  let := coinducedExtSourceModule q N n
  rw [coinducedExtSourceModule_smul]
  have hm : (restrictScalars q).map (ModuleCat.ofHom (LinearMap.mulRight S (q r))) =
      r • 𝟙 ((restrictScalars q).obj (ModuleCat.of S S)) := by
    ext s
    change (show S from s) * q r = q r * (show S from s)
    exact mul_comm _ _
  rw [hm]
  simp only [Ext.mk₀_smul, Ext.smul_comp, Ext.mk₀_id_comp]

variable [HasDerivedCategory.{a} (ModuleCat.{u} R)]
  [HasDerivedCategory.{b} (ModuleCat.{u} S)]

/-- The unchanged installed derived-homology comparison is target-linear. -/
def derivedCoextendScalarsPlusHomologyExtSourceLinearEquiv
    (J : InjectiveResolution N) :
    letI := coinducedExtSourceModule q N n
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).obj
      ((coextendScalars q).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj N)) ≃ₗ[S]
      Ext.{w} ((restrictScalars q).obj (ModuleCat.of S S)) N n := by
  letI := coinducedExtSourceModule q N n
  refine { __ := derivedCoextendScalarsPlusHomologyExtAddEquiv q N J n
           map_smul' := ?_ }
  intro s x
  exact (derivedCoextendScalarsPlusHomologyExtAddEquiv_smul q N J n s x).trans
    (coinducedExtSourceModule_smul q N n s _).symm

/-- The source-linear comparison has the original additive comparison as its map. -/
@[simp]
theorem derivedCoextendScalarsPlusHomologyExtSourceLinearEquiv_toAddEquiv
    (J : InjectiveResolution N) :
    letI := coinducedExtSourceModule q N n
    (derivedCoextendScalarsPlusHomologyExtSourceLinearEquiv q N n J).toAddEquiv =
      derivedCoextendScalarsPlusHomologyExtAddEquiv q N J n := rfl

end ModuleCat
