/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.Cohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.PairingTranspose
public import Mathlib.Algebra.Module.ZMod

/-!
# `ℤ/n`-linearity of the duality pairing

Let `n` be a natural number and `Λ = ULift (ZMod n)`, so that `ModuleSheaf X Λ` is the category
`Sh(X_et, n)` of sheaves of `ℤ/n`-modules (Milne, *Lectures on Étale Cohomology* v2.21,
p. 102). Multiplication by `n` is zero on every object
(`moduleSheaf_uLiftZMod_nsmul_id_eq_zero`), so every group `Ext^q(F, G)` computed there is
killed by `n` (`moduleSheaf_uLiftZMod_ext_nsmul_eq_zero`), and so is
`H^r_c(U, F) = Ext^r(Λ_X, j_! F)`. The same holds for the compactly supported cohomology
`CompactSupport.H j F₀ r` of the underlying abelian sheaf `F₀`
(`compactSupport_uLiftZMod_nsmul_eq_zero`), since `n` kills `j_! F₀`. Each of these groups
therefore carries its canonical `ZMod n`-module structure `AddCommGroup.zmodModule`
(`moduleSheafExtZModModule`, `compactSupportZModModule`; named declarations, used as local
instances), for every `n`, including `0` (where it is the integer module).

Every additive map between such groups is `ZMod n`-linear (Mathlib's
`AddMonoidHom.toZModLinearMap`). Hence the dual map of the pairing is `ZMod n`-bilinear:

* `moduleLowerShriekPairingDualLinearMap`:
  `H^r_c(U, F) →ₗ[ZMod n] (Ext^{d-r}(F, G) →ₗ[ZMod n] H^d_c(U, G))`, and
* `moduleLowerShriekPairingTransposeLinearMap`:
  `Ext^s(F, G) →ₗ[ZMod n] (H^{d-s}_c(U, F) →ₗ[ZMod n] H^d_c(U, G))`,

both given by `(c, e) ↦ φ(c, e)`. This is the `ℤ/n`-module structure through which
`Hom(-, ℤ/n)` is applied to the lower rows of the diagrams in the proof of Milne, loc. cit.,
Thm. 14.7, p. 94; no dual group or trace is formed here.
-/

@[expose] public noncomputable section

universe w w' w'' u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

section Torsion

variable {X : Scheme.{u}} (n : ℕ)

/-- In sheaves of `ℤ/n`-modules over the constant ring, multiplication by `n` is zero. -/
theorem moduleSheaf_uLiftZMod_nsmul_id_eq_zero (F : ModuleSheaf X (ULift.{u + 1} (ZMod n))) :
    n • 𝟙 F = 0 := by
  have hΛ : (n : ULift.{u + 1} (ZMod n)) = 0 := ULift.ext _ _ (by simp)
  apply (SheafOfModules.toSheaf (constantRing X (ULift.{u + 1} (ZMod n)))).map_injective
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
  apply Sheaf.hom_ext
  ext V x
  have hR : (n : (constantRing X (ULift.{u + 1} (ZMod n))).obj.obj V) = 0 := by
    rw [← map_natCast ((constantRingUnit X (ULift.{u + 1} (ZMod n))).app V).hom n]
    exact (congrArg ((constantRingUnit X (ULift.{u + 1} (ZMod n))).app V).hom hΛ).trans
      (map_zero _)
  have hM : ∀ y : F.val.obj V, n • y = 0 := fun y => by
    rw [← Nat.cast_smul_eq_nsmul ((constantRing X (ULift.{u + 1} (ZMod n))).obj.obj V), hR,
      zero_smul]
  exact hM x

variable [HasExt.{w} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]

/-- Every Ext group between sheaves of `ℤ/n`-modules is killed by `n`. -/
theorem moduleSheaf_uLiftZMod_ext_nsmul_eq_zero {F G : ModuleSheaf X (ULift.{u + 1} (ZMod n))}
    {q : ℕ} (e : Ext.{w} F G q) : n • e = 0 := by
  have h : ∀ m : ℕ, (Ext.mk₀ (m • 𝟙 F)).comp e (zero_add q) = m • e := by
    intro m
    induction m with
    | zero => simp only [zero_nsmul, Ext.mk₀_zero, Ext.zero_comp]
    | succ m ih => simp only [succ_nsmul, Ext.mk₀_add, Ext.add_comp, ih, Ext.mk₀_id_comp]
  rw [← h n, moduleSheaf_uLiftZMod_nsmul_id_eq_zero, Ext.mk₀_zero, Ext.zero_comp]

/-- The canonical `ZMod n`-module structure on an Ext group between sheaves of `ℤ/n`-modules. -/
abbrev moduleSheafExtZModModule (F G : ModuleSheaf X (ULift.{u + 1} (ZMod n))) (q : ℕ) :
    Module (ZMod n) (Ext.{w} F G q) :=
  AddCommGroup.zmodModule (moduleSheaf_uLiftZMod_ext_nsmul_eq_zero n)

end Torsion

section CompactSupport

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ)
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} X)]

/-- Compactly supported cohomology of the underlying abelian sheaf of a sheaf of
`ℤ/n`-modules is killed by `n`. -/
theorem compactSupport_uLiftZMod_nsmul_eq_zero (F : ModuleSheaf U (ULift.{u + 1} (ZMod n))) (r : ℕ)
    (x : CompactSupport.H.{w'} j
      ((SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).obj F) r) :
    n • x = 0 := by
  let F₀ := (SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).obj F
  have hF : n • 𝟙 F₀ = 0 := by
    have h := congrArg (SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).map
      (moduleSheaf_uLiftZMod_nsmul_id_eq_zero n F)
    rwa [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] at h
  have hG : n • 𝟙 ((etaleLowerShriek j).obj F₀) = 0 := by
    have h := congrArg (etaleLowerShriek j).map hF
    rwa [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] at h
  have hm : ∀ m : ℕ, Sheaf.H.map (m • 𝟙 ((etaleLowerShriek j).obj F₀)) r x = m • x := by
    intro m
    induction m with
    | zero => simp only [zero_nsmul, Sheaf.H.map_apply, Ext.mk₀_zero, Ext.comp_zero]
    | succ m ih => simp only [succ_nsmul, Sheaf.H.map_add_apply, ih, Sheaf.H.map_id_apply]
  rw [← hm n, hG, Sheaf.H.map_apply, Ext.mk₀_zero, Ext.comp_zero]

/-- The canonical `ZMod n`-module structure on compactly supported cohomology of the underlying
abelian sheaf of a sheaf of `ℤ/n`-modules. -/
abbrev compactSupportZModModule (F : ModuleSheaf U (ULift.{u + 1} (ZMod n))) (r : ℕ) :
    Module (ZMod n) (CompactSupport.H.{w'} j
      ((SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).obj F) r) :=
  AddCommGroup.zmodModule (compactSupport_uLiftZMod_nsmul_eq_zero j n F r)

end CompactSupport

section Linear

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] (n : ℕ)
  [HasExt.{w} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{w'} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]

attribute [local instance] moduleSheafExtZModModule

/-- The dual map of the pairing as a `ZMod n`-bilinear map
`H^r_c(U, F) →ₗ (Ext^{d-r}(F, G) →ₗ H^d_c(U, G))`, for `r ≤ d`. -/
def moduleLowerShriekPairingDualLinearMap (F G : ModuleSheaf U (ULift.{u + 1} (ZMod n)))
    (d r : ℕ) (hr : r ≤ d) :
    Ext.{w'} (moduleUnit X (ULift.{u + 1} (ZMod n)))
        ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj F) r →ₗ[ZMod n]
      Ext.{w} F G (d - r) →ₗ[ZMod n]
        Ext.{w'} (moduleUnit X (ULift.{u + 1} (ZMod n)))
          ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj G) d :=
  AddMonoidHom.toZModLinearMap n ((AddMonoidHom.toZModLinearMapEquiv n).toAddMonoidHom.comp
    (moduleLowerShriekPairingDualHom j (ULift.{u + 1} (ZMod n)) F G d r hr))

@[simp]
theorem moduleLowerShriekPairingDualLinearMap_apply_apply
    (F G : ModuleSheaf U (ULift.{u + 1} (ZMod n))) (d r : ℕ) (hr : r ≤ d)
    (c : Ext.{w'} (moduleUnit X (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj F) r)
    (e : Ext.{w} F G (d - r)) :
    moduleLowerShriekPairingDualLinearMap j n F G d r hr c e =
      moduleLowerShriekPairing j (ULift.{u + 1} (ZMod n)) c e (by lia) :=
  rfl

/-- The transposed map of the pairing as a `ZMod n`-bilinear map
`Ext^s(F, G) →ₗ (H^{d-s}_c(U, F) →ₗ H^d_c(U, G))`, for `s ≤ d`. -/
def moduleLowerShriekPairingTransposeLinearMap (F G : ModuleSheaf U (ULift.{u + 1} (ZMod n)))
    (d s : ℕ) (hs : s ≤ d) :
    Ext.{w} F G s →ₗ[ZMod n]
      Ext.{w'} (moduleUnit X (ULift.{u + 1} (ZMod n)))
          ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj F) (d - s) →ₗ[ZMod n]
        Ext.{w'} (moduleUnit X (ULift.{u + 1} (ZMod n)))
          ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj G) d :=
  AddMonoidHom.toZModLinearMap n ((AddMonoidHom.toZModLinearMapEquiv n).toAddMonoidHom.comp
    (moduleLowerShriekPairingTransposeHom j (ULift.{u + 1} (ZMod n)) F G d s hs))

@[simp]
theorem moduleLowerShriekPairingTransposeLinearMap_apply_apply
    (F G : ModuleSheaf U (ULift.{u + 1} (ZMod n))) (d s : ℕ) (hs : s ≤ d)
    (e : Ext.{w} F G s)
    (c : Ext.{w'} (moduleUnit X (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj F) (d - s)) :
    moduleLowerShriekPairingTransposeLinearMap j n F G d s hs e c =
      moduleLowerShriekPairing j (ULift.{u + 1} (ZMod n)) c e (by lia) :=
  rfl

end Linear

end AlgebraicGeometry.Scheme.EtaleCohomology
