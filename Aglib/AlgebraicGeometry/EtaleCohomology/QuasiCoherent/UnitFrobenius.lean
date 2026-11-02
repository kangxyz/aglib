/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.StructureComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.CoefficientMaps
public import Aglib.AlgebraicGeometry.EtaleCohomology.ArtinSchreier.Frobenius
public import Aglib.AlgebraicGeometry.Modules.Pullback.UnitMultiplication

/-! # Original Frobenius and scalar multiplication on the unit coefficient

The unchanged additive structure-sheaf Frobenius acts on the unchanged
quasi-coherent unit coefficient through its original structure comparison.
Its scalar equation uses the native module multiplication map, not a claim
that Frobenius is linear or that its geometric morphism is flat.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

attribute [local instance] isQuasicoherent_unit

variable (X : Scheme.{u})

/-- The original structure comparison is the actual pullback-unit map on sections. -/
theorem additiveUnitStructureIso_hom_down (U : X.Etale)
    (s : (additiveCoefficient X (SheafOfModules.unit X.ringCatSheaf)).obj.obj (op U)) :
    (((additiveUnitStructureIso X).hom.hom.app (op U)) s).down =
      Scheme.Modules.Hom.app (pullbackUnitIso U.hom).hom ⊤ s.down := by
  rfl

/-- Original coefficient multiplication has its original scalar on each étale test. -/
theorem additiveUnitStructureIso_unitMul_down (r : Γ(X, ⊤)) (U : X.Etale)
    (s : (additiveCoefficient X (SheafOfModules.unit X.ringCatSheaf)).obj.obj (op U)) :
    ((additiveUnitStructureIso X).hom.hom.app (op U)
      ((additiveCoefficientMap X (unitMul X r)).hom.app (op U) s)).down =
      (show Γ(U.left, ⊤) from
        (((additiveUnitStructureIso X).hom.hom.app (op U)) s).down) *
        (show Γ(U.left, ⊤) from U.hom.appTop.hom r) := by
  rw [additiveUnitStructureIso_hom_down, additiveCoefficientMap_down,
    additiveUnitStructureIso_hom_down]
  have h := congrArg (fun k => Scheme.Modules.Hom.app k ⊤ s.down)
    (unitMul_pullback U.hom r)
  change Scheme.Modules.Hom.app (pullbackUnitIso U.hom).hom ⊤
      (Scheme.Modules.Hom.app ((Scheme.Modules.pullback U.hom).map (unitMul X r)) ⊤ s.down) =
    Scheme.Modules.Hom.app (unitMul U.left (U.hom.appTop.hom r)) ⊤
      (Scheme.Modules.Hom.app (pullbackUnitIso U.hom).hom ⊤ s.down) at h
  refine h.trans ?_
  rw [unitMul_app]
  change _ * U.left.presheaf.map (𝟙 (op ⊤)) (U.hom.appTop.hom r) = _
  have hr := ConcreteCategory.congr_hom (U.left.presheaf.map_id (op ⊤))
    (U.hom.appTop.hom r)
  exact congrArg (fun z : Γ(U.left, ⊤) =>
    (show Γ(U.left, ⊤) from
      Scheme.Modules.Hom.app (pullbackUnitIso U.hom).hom ⊤ s.down) * z) hr

variable (p : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)

/-- Original additive Frobenius on the original quasi-coherent unit coefficient. -/
def unitFrobenius :
    additiveCoefficient X (SheafOfModules.unit X.ringCatSheaf) ⟶
      additiveCoefficient X (SheafOfModules.unit X.ringCatSheaf) :=
  (additiveUnitStructureIso X).hom ≫ structureFrobenius X p hp hX ≫
    (additiveUnitStructureIso X).inv

/-- The original structure comparison intertwines the two literal additive maps. -/
@[reassoc]
theorem unitFrobenius_structure :
    unitFrobenius X p hp hX ≫ (additiveUnitStructureIso X).hom =
      (additiveUnitStructureIso X).hom ≫ structureFrobenius X p hp hX := by
  simp only [unitFrobenius, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The same original map is the prime power in native structure-section coordinates. -/
theorem unitFrobenius_structure_apply (U : X.Etale)
    (s : (additiveCoefficient X (SheafOfModules.unit X.ringCatSheaf)).obj.obj (op U)) :
    ((additiveUnitStructureIso X).hom.hom.app (op U)
      ((unitFrobenius X p hp hX).hom.app (op U) s)).down =
      (show Γ(U.left, ⊤) from
        (((additiveUnitStructureIso X).hom.hom.app (op U)) s).down) ^ p :=
  congrArg (fun k => (k.hom.app (op U) s).down) (unitFrobenius_structure X p hp hX)

/-- Frobenius carries the original scalar multiplication by `r` to that by `r^p`. -/
theorem unitFrobenius_unitMul (r : Γ(X, ⊤)) :
    additiveCoefficientMap X (unitMul X r) ≫ unitFrobenius X p hp hX =
      unitFrobenius X p hp hX ≫ additiveCoefficientMap X (unitMul X (r ^ p)) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply (unitSectionsAddEquiv X ((Scheme.Etale.forget X).obj U.unop)).injective
  change ((additiveUnitStructureIso X).hom.hom.app U
      ((unitFrobenius X p hp hX).hom.app U
        ((additiveCoefficientMap X (unitMul X r)).hom.app U s))).down =
    ((additiveUnitStructureIso X).hom.hom.app U
      ((additiveCoefficientMap X (unitMul X (r ^ p))).hom.app U
        ((unitFrobenius X p hp hX).hom.app U s))).down
  rw [unitFrobenius_structure_apply, additiveUnitStructureIso_unitMul_down,
    additiveUnitStructureIso_unitMul_down, unitFrobenius_structure_apply, map_pow, mul_pow]

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
