/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ModuleCohomology

/-! Original roots coefficient change and scalar forgetting. -/

open CategoryTheory CategoryTheory.Abelian
open GroupCohomology.Kummer.Coefficients

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wM wA

attribute [local instance] hasSheafifyLarge hasSheafifyModules

variable (X : Scheme.{u}) (n : ℕ)
  [HasExt.{wM} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X)]

set_option hygiene false in
local notation "Λ" => ULift.{u + 1} (ZMod n)

/-- An original coefficient map to roots commutes with forgetting scalars. -/
theorem moduleRootsUnitExtCohomologyAddEquiv_postcomp (q : ℕ)
    {M : ModuleSheaf X Λ} (b : M ⟶ moduleRootsOfUnity X n)
    (x : Ext.{wM} (moduleUnit X Λ) M q) :
    let R := constantRing X Λ
    let F := SheafOfModules.toSheaf R
    moduleRootsUnitExtCohomologyAddEquiv X n q ((x.comp (Ext.mk₀ b)) (add_zero q)) =
      Sheaf.H.map (F.map b ≫ (moduleRootsOfUnityUnderlyingIso X n).hom) q
        (etaleModuleExtCohomologyAddEquivLargeScalars.{u, wM, wA} X R M q x) := by
  dsimp only
  rw [moduleRootsUnitExtCohomologyAddEquiv_apply, moduleUnitExtAddEquiv_naturality]
  exact (Sheaf.H.map_comp_apply _ _ _).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
