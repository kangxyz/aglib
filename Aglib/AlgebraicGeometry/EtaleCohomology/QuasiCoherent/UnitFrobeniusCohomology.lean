/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.UnitFrobeniusPullback

/-! # Original cohomology of the étale unit-Frobenius square

The actual additive coefficient pullback and native pullback-unit map commute
with original Frobenius in every degree. This is a direct application of the
proved coefficient square and native cohomology pullback naturality, retaining
independent Ext universes on the two schemes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules

universe u eX eY

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] hasSheafifyLarge isQuasicoherent_unit

variable {X Y : Scheme.{u}} (a : Y ⟶ X) [Etale a]
  (p : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (hY : (p : Γ(Y, ⊤)) = 0)
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]

/-- The original coefficient cohomology pullback, followed by the native
unit comparison, commutes with the original additive Frobenius. -/
theorem unitFrobenius_cohomologyPullback (q : ℕ)
    (x : Sheaf.H.{eX} (additiveCoefficient X (SheafOfModules.unit X.ringCatSheaf)) q) :
    Sheaf.H.map (additiveCoefficientMap Y (pullbackUnitIso a).hom) q
      (additiveCoefficientCohomologyPullback.{u, eX, eY} a
        (SheafOfModules.unit X.ringCatSheaf) q
        (Sheaf.H.map (unitFrobenius X p hp hX) q x)) =
    Sheaf.H.map (unitFrobenius Y p hp hY) q
      (Sheaf.H.map (additiveCoefficientMap Y (pullbackUnitIso a).hom) q
        (additiveCoefficientCohomologyPullback.{u, eX, eY} a
          (SheafOfModules.unit X.ringCatSheaf) q x)) := by
  change Sheaf.H.map (additiveCoefficientMap Y (pullbackUnitIso a).hom) q
    (Sheaf.H.map (additiveCoefficientPullback a (SheafOfModules.unit X.ringCatSheaf)) q
      (cohomologyPullback a (additiveCoefficient X (SheafOfModules.unit X.ringCatSheaf)) q
        (Sheaf.H.map (unitFrobenius X p hp hX) q x))) =
    Sheaf.H.map (unitFrobenius Y p hp hY) q
      (Sheaf.H.map (additiveCoefficientMap Y (pullbackUnitIso a).hom) q
        (Sheaf.H.map (additiveCoefficientPullback a (SheafOfModules.unit X.ringCatSheaf)) q
          (cohomologyPullback a (additiveCoefficient X (SheafOfModules.unit X.ringCatSheaf))
            q x)))
  rw [cohomologyPullback_coefficientMap]
  simp only [← Sheaf.H.map_comp_apply, Category.assoc]
  exact congrArg (fun k => Sheaf.H.map k q
    (cohomologyPullback.{u, eX, eY} a
      (additiveCoefficient X (SheafOfModules.unit X.ringCatSheaf)) q x))
    (unitFrobenius_pullback a p hp hX hY)

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
