/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ModuleRootsScalarPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.ModuleRootsSectionPullback

/-! Detection of the original scalar roots value by its original pullback. -/

open CategoryTheory CategoryTheory.Abelian
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open Coefficients

universe u aS aX wS wX

attribute [local instance] hasSheafifyLarge hasSheafifyModules

variable {S X : Scheme.{u}} [ConnectedSpace S] (p : X ⟶ S)
  (o : S ⟶ X) (ho : o ≫ p = 𝟙 S) (n : ℕ) (hn : 0 < n)
  (hi : IsUnit (n : Γ(S, ⊤)))
  [HasExt.{aS} (AbelianSheaf.{u, u + 1} S)] [HasExt.{aX} (AbelianSheaf.{u, u + 1} X)]

set_option hygiene false in
local notation "Λ" => ULift.{u + 1} (ZMod n)

variable [HasExt.{wS} (ModuleSheaf S Λ)] [HasExt.{wX} (ModuleSheaf X Λ)]

include ho in
/-- The original section detects the original scalar roots value on the base
from its value in the same transported coefficient on the total space. -/
theorem rootsScalarValue_of_pullback
    (x : Sheaf.H.{aS} (mu S n) 0) (b : moduleUnit S Λ ⟶ moduleRootsOfUnity S n)
    (m : ℕ)
    (h :
      let b' := (moduleUnitInverseImageIso p n).inv ≫ (moduleInverseImage p Λ).map b ≫
        (moduleRootsOfUnityInverseImageIso p n hn hi).hom
      rootsCohomologyPullback.{u, aS, aX} p n hn hi 0 x =
        moduleRootsUnitExtCohomologyAddEquiv.{u, wX, aX} X n 0 (Ext.mk₀ (m • b'))) :
    x = moduleRootsUnitExtCohomologyAddEquiv.{u, wS, aS} S n 0 (Ext.mk₀ (m • b)) := by
  let E := moduleRootsUnitExtCohomologyAddEquiv.{u, wS, aS} S n 0
  let F := moduleRootsUnitExtCohomologyAddEquiv.{u, wX, aX} X n 0
  let R := rootsCohomologyPullback.{u, aS, aX} p n hn hi 0
  let L := rootsCohomologyPullback.{u, aX, aS} o n hn (levelInvertible p n hi) 0
  let z : Ext.{wS} (moduleUnit S Λ) (moduleRootsOfUnity S n) 0 := Ext.mk₀ (m • b)
  have h₁ := DFunLike.congr_fun (moduleRootsUnitExtCohomologyPullback_square.{u, wS, wX, aS, aX}
    p n hn hi 0) z
  have h₂ := moduleRootsUnitExtPullback_mk₀_nsmul.{u, wS, wX} p n hn hi b m
  have h₃ : R (E z) = _ := h₁.symm.trans (congrArg F h₂)
  calc
    _ = L (R x) := (rootsCohomologyPullback_section p o ho n hn hi 0 x).symm
    _ = L (R (E z)) := congrArg L (h.trans h₃.symm)
    _ = _ := rootsCohomologyPullback_section p o ho n hn hi 0 (E z)

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
