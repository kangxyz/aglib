/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde

public import Aglib.AlgebraicGeometry.Modules.Pullback.UnitMultiplication
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom


/-!
# AlgebraicGeometry / Modules / StructureSheaf / AffineMultiplication

Source: `Blowup/IdealFrames.lean`.
Incoming SHA256: `48943a629dd5e5789b4db855f39649beb197cd0c8b1407dfb5016010f45eaa6e`.
The original constructors, maps, universe bounds and mathematical hypotheses are retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Original multiplication on an affine structure module. -/
def affineMultiplication (S : Type u) [CommRing S] (s : S) :
    (show (Spec (.of S)).Modules from SheafOfModules.unit (Spec (.of S)).ringCatSheaf) ⟶
      (show (Spec (.of S)).Modules from SheafOfModules.unit (Spec (.of S)).ringCatSheaf) :=
  tilde.map (ModuleCat.ofHom (LinearMap.mulLeft S s))
@[reassoc]
theorem affineMultiplication_comp (S : Type u) [CommRing S] (s t : S) :
    affineMultiplication S s ≫ affineMultiplication S t = affineMultiplication S (s * t) := by
  rw [affineMultiplication, affineMultiplication, affineMultiplication, ← tilde.map_comp]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change t * (s * x) = (s * t) * x
  ac_rfl
private theorem tildeUnit_toOpen_top (S : Type u) [CommRing S] (s : S) :
    tilde.toOpen (R := .of S) (ModuleCat.of S S) ⊤ s =
      (Scheme.ΓSpecIso (.of S)).inv s := rfl
private theorem affineMultiplication_top_one (S : Type u) [CommRing S] (s : S) :
    (affineMultiplication S s).val.app (op ⊤) (1 : Γ(Spec (.of S), ⊤)) =
      (Scheme.ΓSpecIso (.of S)).inv s := by
  have h := ConcreteCategory.congr_hom
    (tilde.toOpen_map_app (R := .of S) (M := ModuleCat.of S S)
      (N := ModuleCat.of S S) (ModuleCat.ofHom (LinearMap.mulLeft S s)) ⊤) (1 : S)
  change (affineMultiplication S s).val.app (op ⊤)
      (tilde.toOpen (R := .of S) (ModuleCat.of S S) ⊤ (1 : S)) =
    tilde.toOpen (R := .of S) (ModuleCat.of S S) ⊤ (s * 1) at h
  rw [mul_one] at h
  have h1 : tilde.toOpen (R := .of S) (ModuleCat.of S S) ⊤ (1 : S) =
      (1 : Γ(Spec (.of S), ⊤)) :=
    (tildeUnit_toOpen_top S 1).trans (map_one (Scheme.ΓSpecIso (.of S)).inv.hom)
  exact (congrArg
    (fun x : Γ(Spec (.of S), ⊤) => (affineMultiplication S s).val.app (op ⊤) x)
      h1.symm).trans (h.trans (tildeUnit_toOpen_top S s))
/-- The original affine scalar map is multiplication by its original structure-sheaf section. -/
theorem affineMultiplication_eq_unitMul (S : Type u) [CommRing S] (s : S) :
    affineMultiplication S s = unitMul (Spec (.of S)) ((Scheme.ΓSpecIso (.of S)).inv s) := by
  apply (unitHomGlobalSectionsEquiv (Spec (.of S))
    (SheafOfModules.unit (Spec (.of S)).ringCatSheaf)).injective
  change (affineMultiplication S s).val.app (op ⊤) (1 : Γ(Spec (.of S), ⊤)) = _
  rw [affineMultiplication_top_one]
  change (Scheme.ΓSpecIso (.of S)).inv s =
    1 * (Spec (.of S)).presheaf.map (𝟙 (op (⊤ : (Spec (.of S)).Opens)))
      ((Scheme.ΓSpecIso (.of S)).inv s)
  rw [CategoryTheory.Functor.map_id]
  exact (one_mul _).symm
/-- Native affine pullback carries the original multiplication map to its image coefficient. -/
theorem affineMultiplication_pullback {S T : Type u} [CommRing S] [CommRing T]
    (φ : S →+* T) (s : S) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).map
        (affineMultiplication S s) ≫ (pullbackUnitIso (Spec.map (CommRingCat.ofHom φ))).hom =
      (pullbackUnitIso (Spec.map (CommRingCat.ofHom φ))).hom ≫
        affineMultiplication T (φ s) := by
  have hc : (Spec.map (CommRingCat.ofHom φ)).appTop ((Scheme.ΓSpecIso (.of S)).inv s) =
      (Scheme.ΓSpecIso (.of T)).inv (φ s) :=
    congrArg (fun q : CommRingCat.of S ⟶ Γ(Spec (.of T), ⊤) => q s)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm
  simp only [affineMultiplication_eq_unitMul]
  rw [unitMul_pullback, hc]

end AlgebraicGeometry.Scheme.Modules
