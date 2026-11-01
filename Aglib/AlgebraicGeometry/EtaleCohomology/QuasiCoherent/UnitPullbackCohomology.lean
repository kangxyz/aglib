/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.UnitFrobeniusPullback

/-! # Original cohomology of the pulled-back unit coefficient

The original coefficient pullback and native module-unit comparison induce an
injective composite on original cohomology. Their whole Frobenius square is
retained on every cohomology value of the original inverse-image coefficient.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

universe u e

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] hasSheafifyLarge Scheme.Modules.isQuasicoherent_unit

variable {X Y : Scheme.{u}} (a : Y ⟶ X) [Etale a] (q : ℕ)
  [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]

/-- The actual inverse coefficient maps cancel the original nested unit
comparison on every original inverse-image cohomology value. -/
theorem unitPullbackCohomology_leftInverse
    (x : Sheaf.H.{e} ((inverseImage a).obj
      (additiveCoefficient X (SheafOfModules.unit X.ringCatSheaf))) q) :
    Sheaf.H.map (inv (additiveCoefficientPullback a
      (SheafOfModules.unit X.ringCatSheaf))) q
      (Sheaf.H.map (additiveCoefficientMap Y (Scheme.Modules.pullbackUnitIso a).inv) q
        (Sheaf.H.map (additiveCoefficientMap Y (Scheme.Modules.pullbackUnitIso a).hom) q
          (Sheaf.H.map (additiveCoefficientPullback a
            (SheafOfModules.unit X.ringCatSheaf)) q x))) = x := by
  have hc := congrArg (fun k => Sheaf.H.map k q
      (Sheaf.H.map (additiveCoefficientPullback a
        (SheafOfModules.unit X.ringCatSheaf)) q x))
    (additiveCoefficientMap_comp Y (Scheme.Modules.pullbackUnitIso a).hom
      (Scheme.Modules.pullbackUnitIso a).inv)
  rw [Iso.hom_inv_id, additiveCoefficientMap_id] at hc
  simp only [Sheaf.H.map_comp_apply, Sheaf.H.map_id_apply] at hc
  rw [← hc, ← Sheaf.H.map_comp_apply, IsIso.hom_inv_id, Sheaf.H.map_id_apply]

/-- The unchanged nested coefficient comparison is injective in every degree. -/
theorem unitPullbackCohomology_injective : Function.Injective
    (fun x : Sheaf.H.{e} ((inverseImage a).obj
        (additiveCoefficient X (SheafOfModules.unit X.ringCatSheaf))) q =>
      Sheaf.H.map (additiveCoefficientMap Y (Scheme.Modules.pullbackUnitIso a).hom) q
        (Sheaf.H.map (additiveCoefficientPullback a
          (SheafOfModules.unit X.ringCatSheaf)) q x)) := by
  intro x y h
  have hh := congrArg (fun z => Sheaf.H.map
    (inv (additiveCoefficientPullback a (SheafOfModules.unit X.ringCatSheaf))) q
      (Sheaf.H.map (additiveCoefficientMap Y (Scheme.Modules.pullbackUnitIso a).inv) q z)) h
  exact (unitPullbackCohomology_leftInverse a q x).symm.trans
    (hh.trans (unitPullbackCohomology_leftInverse a q y))

/-- The full original unit-Frobenius square on inverse-image cohomology, not
only values in the image of geometric cohomology pullback. -/
theorem unitFrobenius_inverseImage_cohomology
    (p : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (hY : (p : Γ(Y, ⊤)) = 0)
    (x : Sheaf.H.{e} ((inverseImage a).obj
      (additiveCoefficient X (SheafOfModules.unit X.ringCatSheaf))) q) :
    Sheaf.H.map (additiveCoefficientMap Y (Scheme.Modules.pullbackUnitIso a).hom) q
      (Sheaf.H.map (additiveCoefficientPullback a
        (SheafOfModules.unit X.ringCatSheaf)) q
        (Sheaf.H.map ((inverseImage a).map (unitFrobenius X p hp hX)) q x)) =
    Sheaf.H.map (unitFrobenius Y p hp hY) q
      (Sheaf.H.map (additiveCoefficientMap Y (Scheme.Modules.pullbackUnitIso a).hom) q
        (Sheaf.H.map (additiveCoefficientPullback a
          (SheafOfModules.unit X.ringCatSheaf)) q x)) := by
  have h := congrArg (fun k => Sheaf.H.map k q x)
    (unitFrobenius_pullback a p hp hX hY)
  simpa only [Sheaf.H.map_comp_apply] using h

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
