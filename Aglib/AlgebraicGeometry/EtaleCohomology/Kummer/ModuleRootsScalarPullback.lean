/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ModuleCohomology

/-! Original pullback of scalar multiples at degree zero. -/

open CategoryTheory CategoryTheory.Abelian
open GroupCohomology.Kummer.Coefficients

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wY

attribute [local instance] hasSheafifyLarge hasSheafifyModules

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) (hn : 0 < n)
  (hi : IsUnit (n : Γ(X, ⊤)))

set_option hygiene false in
local notation "Λ" => ULift.{u + 1} (ZMod n)

variable [HasExt.{wX} (ModuleSheaf X Λ)] [HasExt.{wY} (ModuleSheaf Y Λ)]

/-- Original roots pullback of a scalar multiple of a degree-zero coefficient map. -/
theorem moduleRootsUnitExtPullback_mk₀_nsmul
    (b : moduleUnit X Λ ⟶ moduleRootsOfUnity X n) (m : ℕ) :
    let F := moduleInverseImage f Λ
    let e := moduleUnitInverseImageIso f n
    let r := moduleRootsOfUnityInverseImageIso f n hn hi
    moduleRootsUnitExtPullback f n hn hi 0 (Ext.mk₀ (m • b)) =
      Ext.mk₀ (m • (e.inv ≫ F.map b ≫ r.hom)) := by
  intro F e r
  rw [moduleRootsUnitExtPullback_apply, moduleUnitExtPullback_apply, Ext.mapExactFunctor_mk₀]
  rw [Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]
  change Ext.mk₀ (e.inv ≫ F.map (m • b) ≫ r.hom) = _
  apply congrArg Ext.mk₀
  have hm := F.map_nsmul (f := b) (n := m)
  rw [hm, Preadditive.nsmul_comp, Preadditive.comp_nsmul]

end AlgebraicGeometry.Scheme.EtaleCohomology
