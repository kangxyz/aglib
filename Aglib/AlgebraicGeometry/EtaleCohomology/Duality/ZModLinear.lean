/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.Cohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.PairingTranspose
public import Aglib.Algebra.Homology.DerivedCategory.Ext.ZMod
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ZMod

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
    n • 𝟙 F = 0 :=
  ModuleCat.Sheaf.ConstantRing.uLiftZMod_nsmul_id_eq_zero.{u + 1, u, u + 1, u + 1}
    (Scheme.smallEtaleTopology X) n F

variable [HasExt.{w} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]

/-- Every Ext group between sheaves of `ℤ/n`-modules is killed by `n`. -/
theorem moduleSheaf_uLiftZMod_ext_nsmul_eq_zero {F G : ModuleSheaf X (ULift.{u + 1} (ZMod n))}
    {q : ℕ} (e : Ext.{w} F G q) : n • e = 0 :=
  Ext.nsmul_eq_zero_of_nsmul_id_left n (moduleSheaf_uLiftZMod_nsmul_id_eq_zero n F) e

/-- The canonical `ZMod n`-module structure on an Ext group between sheaves of `ℤ/n`-modules. -/
abbrev moduleSheafExtZModModule (F G : ModuleSheaf X (ULift.{u + 1} (ZMod n))) (q : ℕ) :
    Module (ZMod n) (Ext.{w} F G q) :=
  Ext.zmodModuleOfNsmulIdLeft n (moduleSheaf_uLiftZMod_nsmul_id_eq_zero n F) G q

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
  have hF := Functor.nsmul_id_eq_zero_obj
    (SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))) n
    (moduleSheaf_uLiftZMod_nsmul_id_eq_zero n F)
  exact Ext.nsmul_eq_zero_of_nsmul_id_right n
    ((etaleLowerShriek j).nsmul_id_eq_zero_obj n hF) x

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
  Functor.extPairingDualLinearMap (moduleLowerShriek j (ULift.{u + 1} (ZMod n)))
    (moduleUnit X (ULift.{u + 1} (ZMod n))) n F G d r hr

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
  Functor.extPairingTransposeLinearMap (moduleLowerShriek j (ULift.{u + 1} (ZMod n)))
    (moduleUnit X (ULift.{u + 1} (ZMod n))) n F G d s hs

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
