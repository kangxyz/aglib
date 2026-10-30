/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.YonedaPairing
public import Mathlib.Algebra.Module.ZMod

/-!
# Annihilation and canonical ZMod actions on Ext

An equation `n • 𝟙 = 0` at either endpoint annihilates every corresponding Ext
group. The canonical action is Mathlib's `AddCommGroup.zmodModule`, retained as
named declarations for local instances. Every modulus is allowed, including zero.
Exact-functor Yoneda pairings are linear for these actions because every additive
map between `ZMod n`-modules is linear. No linear-category structure is required.

Sources: Mathlib `Ext/Basic.lean`, additivity of `mk₀` and Yoneda composition;
`Algebra/Module/ZMod.lean`, `AddCommGroup.zmodModule` and
`AddMonoidHom.toZModLinearMap`. This is the categorical content of the original
etale `Duality/ZModLinear` construction.
-/

@[expose] public noncomputable section

universe w w' u v u' v'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {X Y : C} {q : ℕ} (n : ℕ)

/-- Annihilation of the source identity annihilates Ext in every degree. -/
theorem nsmul_eq_zero_of_nsmul_id_left (hX : n • 𝟙 X = 0) (e : Ext.{w} X Y q) :
    n • e = 0 := by
  have h : ∀ m : ℕ, (Ext.mk₀ (m • 𝟙 X)).comp e (zero_add q) = m • e := by
    intro m
    induction m with
    | zero => simp only [zero_nsmul, Ext.mk₀_zero, Ext.zero_comp]
    | succ m ih => simp only [succ_nsmul, Ext.mk₀_add, Ext.add_comp, ih, Ext.mk₀_id_comp]
  rw [← h n, hX, Ext.mk₀_zero, Ext.zero_comp]

/-- Annihilation of the target identity annihilates Ext in every degree. -/
theorem nsmul_eq_zero_of_nsmul_id_right (hY : n • 𝟙 Y = 0) (e : Ext.{w} X Y q) :
    n • e = 0 := by
  have h : ∀ m : ℕ, e.comp (Ext.mk₀ (m • 𝟙 Y)) (add_zero q) = m • e := by
    intro m
    induction m with
    | zero => simp only [zero_nsmul, Ext.mk₀_zero, Ext.comp_zero]
    | succ m ih => simp only [succ_nsmul, Ext.mk₀_add, Ext.comp_add, ih, Ext.comp_mk₀_id]
  rw [← h n, hY, Ext.mk₀_zero, Ext.comp_zero]

/-- The canonical ZMod action supplied by annihilation of the source identity. -/
abbrev zmodModuleOfNsmulIdLeft (hX : n • 𝟙 X = 0) (Y : C) (q : ℕ) :
    Module (ZMod n) (Ext.{w} X Y q) :=
  AddCommGroup.zmodModule (nsmul_eq_zero_of_nsmul_id_left n hX)

/-- The same canonical ZMod action supplied by annihilation of the target identity. -/
abbrev zmodModuleOfNsmulIdRight (X : C) (hY : n • 𝟙 Y = 0) (q : ℕ) :
    Module (ZMod n) (Ext.{w} X Y q) :=
  AddCommGroup.zmodModule (nsmul_eq_zero_of_nsmul_id_right n hY)

end CategoryTheory.Abelian.Ext

namespace CategoryTheory.Functor

section Annihilation

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] (L : C ⥤ D) [L.Additive]

/-- An additive functor preserves annihilation of an identity morphism. -/
theorem nsmul_id_eq_zero_obj (n : ℕ) {X : C} (hX : n • 𝟙 X = 0) :
    n • 𝟙 (L.obj X) = 0 := by
  simpa only [Functor.map_nsmul, Functor.map_id, Functor.map_zero] using congrArg L.map hX

end Annihilation

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  (A : D) (n : ℕ)

/-- The exact-functor pairing as a bilinear map for the supplied canonical ZMod actions. -/
def extPairingLinearMap (F G : C) (r s t : ℕ) (h : r + s = t)
    [Module (ZMod n) (Ext.{w'} A (L.obj F) r)] [Module (ZMod n) (Ext.{w} F G s)]
    [Module (ZMod n) (Ext.{w'} A (L.obj G) t)] :
    Ext.{w'} A (L.obj F) r →ₗ[ZMod n] Ext.{w} F G s →ₗ[ZMod n]
      Ext.{w'} A (L.obj G) t :=
  AddMonoidHom.toZModLinearMap n ((AddMonoidHom.toZModLinearMapEquiv n).toAddMonoidHom.comp
    (extPairingHom L A F G r s t h))

/-- The bilinear map retains the original Yoneda formula. -/
@[simp]
theorem extPairingLinearMap_apply_apply (F G : C) (r s t : ℕ) (h : r + s = t)
    [Module (ZMod n) (Ext.{w'} A (L.obj F) r)] [Module (ZMod n) (Ext.{w} F G s)]
    [Module (ZMod n) (Ext.{w'} A (L.obj G) t)]
    (c : Ext.{w'} A (L.obj F) r) (e : Ext.{w} F G s) :
    extPairingLinearMap L A n F G r s t h c e = extPairing L A c e h := rfl

/-- The linear dual map into total degree `d`, retaining `r ≤ d`. -/
def extPairingDualLinearMap (F G : C) (d r : ℕ) (hr : r ≤ d)
    [Module (ZMod n) (Ext.{w'} A (L.obj F) r)] [Module (ZMod n) (Ext.{w} F G (d - r))]
    [Module (ZMod n) (Ext.{w'} A (L.obj G) d)] :
    Ext.{w'} A (L.obj F) r →ₗ[ZMod n] Ext.{w} F G (d - r) →ₗ[ZMod n]
      Ext.{w'} A (L.obj G) d :=
  extPairingLinearMap L A n F G r (d - r) d (by lia)

/-- The linear transpose into total degree `d`, retaining `s ≤ d`. -/
def extPairingTransposeLinearMap (F G : C) (d s : ℕ) (hs : s ≤ d)
    [Module (ZMod n) (Ext.{w'} A (L.obj F) (d - s))] [Module (ZMod n) (Ext.{w} F G s)]
    [Module (ZMod n) (Ext.{w'} A (L.obj G) d)] :
    Ext.{w} F G s →ₗ[ZMod n] Ext.{w'} A (L.obj F) (d - s) →ₗ[ZMod n]
      Ext.{w'} A (L.obj G) d :=
  (extPairingLinearMap L A n F G (d - s) s d (by lia)).flip

end CategoryTheory.Functor
