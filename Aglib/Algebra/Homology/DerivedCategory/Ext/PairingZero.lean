/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.ZMod

/-!
# Degree-zero normalization of the original Yoneda pairing

The exact-functor pairing evaluated on a degree-zero morphism is its original
Yoneda precomposition or postcomposition. In particular the original identity
acts as the unit. Scalar multiples use the already selected ZMod actions, with
no linear-category structure or new Ext realization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u v u' v' w w'

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {X Y : C}

/-- The original degree-zero map preserves natural multiples already on morphisms. -/
theorem mk₀_nsmul (m : ℕ) (f : X ⟶ Y) : mk₀ (m • f) = m • mk₀ f :=
  _root_.map_nsmul (addEquiv₀ (X := X) (Y := Y)).symm m f

end CategoryTheory.Abelian.Ext

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  {A : D} {F G : C}

/-- Evaluation on an original degree-zero coefficient morphism is postcomposition. -/
theorem extPairing_mk₀_right {r : ℕ} (c : Ext.{w'} A (L.obj F) r) (f : F ⟶ G) :
    extPairing L A c (Ext.mk₀ f) (add_zero r) =
      c.comp (Ext.mk₀ (L.map f)) (add_zero r) := by
  simp only [extPairing, Ext.mapExactFunctor_mk₀]

/-- Evaluation on an original degree-zero source morphism is precomposition. -/
theorem extPairing_mk₀_left {s : ℕ} (f : A ⟶ L.obj F) (e : Ext.{w} F G s) :
    extPairing L A (Ext.mk₀ f) e (zero_add s) =
      (Ext.mk₀ f).comp (e.mapExactFunctor L) (zero_add s) := rfl

/-- The original coefficient identity is the right unit of the pairing. -/
theorem extPairing_mk₀_id_right {r : ℕ} (c : Ext.{w'} A (L.obj F) r) :
    extPairing L A c (Ext.mk₀ (𝟙 F)) (add_zero r) = c := by
  rw [extPairing_mk₀_right, L.map_id, Ext.comp_mk₀_id]

/-- The original source identity leaves exactly the original exact-functor Ext map. -/
theorem extPairing_mk₀_id_left {s : ℕ} (e : Ext.{w} F G s) :
    extPairing L (L.obj F) (Ext.mk₀ (𝟙 (L.obj F))) e (zero_add s) =
      e.mapExactFunctor L := by
  rw [extPairing_mk₀_left, Ext.mk₀_id_comp]

variable (n : ℕ)

/-- The entire bilinear map evaluated on a scalar multiple of a degree-zero map. -/
theorem extPairingLinearMap_smul_mk₀_right {r : ℕ}
    [Module (ZMod n) (Ext.{w'} A (L.obj F) r)]
    [Module (ZMod n) (Ext.{w} F G 0)]
    [Module (ZMod n) (Ext.{w'} A (L.obj G) r)]
    (a : ZMod n) (f : F ⟶ G) :
    (extPairingLinearMap L A n F G r 0 r (add_zero r)).flip (a • Ext.mk₀ f) =
      a • AddMonoidHom.toZModLinearMap n ((Ext.mk₀ (L.map f)).postcomp A (add_zero r)) := by
  ext c
  simp only [LinearMap.flip_apply, LinearMap.map_smul, LinearMap.smul_apply,
    extPairingLinearMap_apply_apply, extPairing_mk₀_right]
  rfl

/-- Scalar multiples of the original identity act by the selected canonical scalars. -/
theorem extPairingLinearMap_smul_mk₀_id_right {r : ℕ}
    [Module (ZMod n) (Ext.{w'} A (L.obj F) r)]
    [Module (ZMod n) (Ext.{w} F F 0)] (a : ZMod n) :
    (extPairingLinearMap L A n F F r 0 r (add_zero r)).flip
        (a • Ext.mk₀ (𝟙 F)) = a • LinearMap.id := by
  ext c
  simp only [LinearMap.flip_apply, LinearMap.map_smul, LinearMap.smul_apply,
    LinearMap.id_apply, extPairingLinearMap_apply_apply, extPairing_mk₀_id_right]

/-- Scalar multiples of a source morphism scale the original precomposition map. -/
theorem extPairingLinearMap_smul_mk₀_left {s : ℕ}
    [Module (ZMod n) (Ext.{w'} A (L.obj F) 0)]
    [Module (ZMod n) (Ext.{w} F G s)]
    [Module (ZMod n) (Ext.{w'} A (L.obj G) s)]
    (a : ZMod n) (f : A ⟶ L.obj F) :
    extPairingLinearMap L A n F G 0 s s (zero_add s) (a • Ext.mk₀ f) =
      a • extPairingLinearMap L A n F G 0 s s (zero_add s) (Ext.mk₀ f) :=
  (extPairingLinearMap L A n F G 0 s s (zero_add s)).map_smul a (Ext.mk₀ f)

end CategoryTheory.Functor
