/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.Trace
public import Aglib.Algebra.Homology.DerivedCategory.Ext.PairingZero
public import Aglib.Algebra.Homology.DerivedCategory.Ext.AcyclicComparison
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# The original curve duality maps followed by normalized trace

The actual exact-functor Yoneda pairing is followed by the normalized module
trace. Its two curried directions take values in the existing `Module.Dual`
over `ZMod n`. The whole bilinear map, original morphism naturality and degree-zero
normalizations are retained. This constructs the maps of curve duality without
asserting perfectness or comparing the Aglib Kummer normalization with SGA signs.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u w w' w''

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients Scheme.OverField

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard moduleSheafExtZModModule

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{w} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{w'} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{w''} (AbelianSheaf.{u, u + 1} X.left)]

/-- The original Yoneda bilinear map followed by the canonical normalized module trace. -/
def moduleTracePairingLinearMap (F : ModuleSheaf U (ULift.{u + 1} (ZMod n)))
    (r s : ℕ) (h : r + s = 2) :
    Ext.{w'} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
        ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj F) r →ₗ[ZMod n]
      Module.Dual (ZMod n) (Ext.{w} F (moduleRootsOfUnity U n) s) :=
  (Functor.extPairingLinearMap (moduleLowerShriek j (ULift.{u + 1} (ZMod n)))
    (moduleUnit X.left (ULift.{u + 1} (ZMod n))) n F (moduleRootsOfUnity U n) r s 2 h).compr₂
      (moduleCompactSupportTraceLinearMap X hX D hfin hclosed j hD n hn hunit hinv)

/-- Evaluation retains the original Yoneda composition and the already normalized trace. -/
@[simp]
theorem moduleTracePairingLinearMap_apply_apply
    (F : ModuleSheaf U (ULift.{u + 1} (ZMod n))) (r s : ℕ) (h : r + s = 2)
    (c : Ext.{w'} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj F) r)
    (e : Ext.{w} F (moduleRootsOfUnity U n) s) :
    moduleTracePairingLinearMap X hX D hfin hclosed j hD n hn hunit hinv F r s h c e =
      moduleCompactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit hinv
        (moduleLowerShriekPairing j (ULift.{u + 1} (ZMod n)) c e h) := rfl

/-- The map `φʳ` into the native ZMod dual, for `r ≤ 2`. -/
def moduleDualityMap (F : ModuleSheaf U (ULift.{u + 1} (ZMod n))) (r : ℕ) (hr : r ≤ 2) :
    Ext.{w'} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
        ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj F) r →ₗ[ZMod n]
      Module.Dual (ZMod n) (Ext.{w} F (moduleRootsOfUnity U n) (2 - r)) :=
  moduleTracePairingLinearMap X hX D hfin hclosed j hD n hn hunit hinv F r (2 - r) (by lia)

/-- The map `ψˢ` into the native ZMod dual, for `s ≤ 2`. -/
def moduleDualityTransposeMap (F : ModuleSheaf U (ULift.{u + 1} (ZMod n)))
    (s : ℕ) (hs : s ≤ 2) :
    Ext.{w} F (moduleRootsOfUnity U n) s →ₗ[ZMod n]
      Module.Dual (ZMod n)
        (Ext.{w'} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
          ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj F) (2 - s)) :=
  (moduleTracePairingLinearMap X hX D hfin hclosed j hD n hn hunit hinv
    F (2 - s) s (by lia)).flip

/-- The whole `φ` map is the existing linear Yoneda map postcomposed with trace. -/
theorem moduleDualityMap_eq (F : ModuleSheaf U (ULift.{u + 1} (ZMod n)))
    (r : ℕ) (hr : r ≤ 2) :
    moduleDualityMap X hX D hfin hclosed j hD n hn hunit hinv F r hr =
      (moduleLowerShriekPairingDualLinearMap j n F (moduleRootsOfUnity U n) 2 r hr).compr₂
        (moduleCompactSupportTraceLinearMap X hX D hfin hclosed j hD n hn hunit hinv) := rfl

/-- The whole `ψ` map uses the same trace and the original transposed Yoneda map. -/
theorem moduleDualityTransposeMap_eq (F : ModuleSheaf U (ULift.{u + 1} (ZMod n)))
    (s : ℕ) (hs : s ≤ 2) :
    moduleDualityTransposeMap X hX D hfin hclosed j hD n hn hunit hinv F s hs =
      (moduleLowerShriekPairingTransposeLinearMap j n F (moduleRootsOfUnity U n) 2 s hs).compr₂
        (moduleCompactSupportTraceLinearMap X hX D hfin hclosed j hD n hn hunit hinv) := rfl

/-- Whole coefficient naturality: the two original Yoneda actions are adjoint under trace. -/
theorem moduleTracePairingLinearMap_naturality
    {F F' : ModuleSheaf U (ULift.{u + 1} (ZMod n))} (f : F ⟶ F')
    (r s : ℕ) (h : r + s = 2) :
    (moduleTracePairingLinearMap X hX D hfin hclosed j hD n hn hunit hinv F' r s h).comp
        (AddMonoidHom.toZModLinearMap n
          ((Ext.mk₀ ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map f)).postcomp
            (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (add_zero r))) =
      (moduleTracePairingLinearMap X hX D hfin hclosed j hD n hn hunit hinv F r s h).compl₂
        (AddMonoidHom.toZModLinearMap n
          ((Ext.mk₀ f).precomp (moduleRootsOfUnity U n) (zero_add s))) := by
  ext c e
  exact congrArg (moduleCompactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit hinv)
    (moduleLowerShriekPairing_naturality f c e h)

/-- The whole extension-class connecting square retains the original sign `+1`. -/
theorem moduleTracePairingLinearMap_extClass
    {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact)
    (r r' s s' : ℕ) (hr : r + 1 = r') (hs : 1 + s = s')
    (h : r' + s = 2) (h' : r + s' = 2) :
    (moduleTracePairingLinearMap X hX D hfin hclosed j hD n hn hunit hinv S.X₁ r' s h).comp
        (AddMonoidHom.toZModLinearMap n
          ((shortExact_moduleLowerShriek j (ULift.{u + 1} (ZMod n)) hS).extClass.postcomp
            (moduleUnit X.left (ULift.{u + 1} (ZMod n))) hr)) =
      (moduleTracePairingLinearMap X hX D hfin hclosed j hD n hn hunit hinv S.X₃ r s' h').compl₂
        (AddMonoidHom.toZModLinearMap n
          (hS.extClass.precomp (moduleRootsOfUnity U n) hs)) := by
  ext c e
  exact congrArg (moduleCompactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit hinv)
    (moduleLowerShriekPairing_extClass hS c e hr hs h h')

/-- The whole square for Mathlib's signed connecting map retains its original sign. -/
theorem moduleTracePairingLinearMap_δ
    {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact)
    (r r' s s' : ℕ) (hr : r + 1 = r') (hs : s + 1 = s')
    (h : r' + s = 2) (h' : r + s' = 2) :
    (moduleTracePairingLinearMap X hX D hfin hclosed j hD n hn hunit hinv S.X₃ r s' h').compl₂
        (AddMonoidHom.toZModLinearMap n (Ext.δ hS s s' hs)) =
      (s' : ℤ).negOnePow •
        (moduleTracePairingLinearMap X hX D hfin hclosed j hD n hn hunit hinv S.X₁ r' s h).comp
          (AddMonoidHom.toZModLinearMap n
            ((shortExact_moduleLowerShriek j (ULift.{u + 1} (ZMod n)) hS).extClass.postcomp
              (moduleUnit X.left (ULift.{u + 1} (ZMod n))) hr)) := by
  ext c e
  change moduleCompactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit hinv
      (moduleLowerShriekPairing j _ c (Ext.δ hS s s' hs e) h') =
    (s' : ℤ).negOnePow •
      moduleCompactSupportTraceAddEquiv X hX D hfin hclosed j hD n hn hunit hinv
        (moduleLowerShriekPairing j _
          (c.comp (shortExact_moduleLowerShriek j _ hS).extClass hr) e h)
  rw [moduleLowerShriekPairing_δ hS c e hr hs h h']
  simp only [Units.smul_def, map_zsmul]

/-- In compact-support degree zero the whole map is original source precomposition
and exact lower shriek, followed by the same normalized trace. -/
theorem moduleTracePairingLinearMap_mk₀_left
    (F : ModuleSheaf U (ULift.{u + 1} (ZMod n)))
    (f : moduleUnit X.left (ULift.{u + 1} (ZMod n)) ⟶
      (moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj F) :
    moduleTracePairingLinearMap X hX D hfin hclosed j hD n hn hunit hinv F 0 2 rfl
        (Ext.mk₀ f) =
      (moduleCompactSupportTraceLinearMap X hX D hfin hclosed j hD n hn hunit hinv).comp
        (AddMonoidHom.toZModLinearMap n
          ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).extPrecompMap
            f (moduleRootsOfUnity U n) 2)) := rfl

/-- Evaluation on a scalar multiple of an original degree-zero map is the original
coefficient postcomposition followed by trace. -/
theorem moduleTracePairingLinearMap_smul_mk₀
    (F : ModuleSheaf U (ULift.{u + 1} (ZMod n))) (a : ZMod n)
    (f : F ⟶ moduleRootsOfUnity U n) :
    (moduleTracePairingLinearMap X hX D hfin hclosed j hD n hn hunit hinv F 2 0 rfl).flip
        (a • Ext.mk₀ f) =
      a • (moduleCompactSupportTraceLinearMap X hX D hfin hclosed j hD n hn hunit hinv).comp
        (AddMonoidHom.toZModLinearMap n
          ((Ext.mk₀ ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map f)).postcomp
            (moduleUnit X.left (ULift.{u + 1} (ZMod n))) (add_zero 2))) := by
  ext c
  change moduleCompactSupportTraceLinearMap X hX D hfin hclosed j hD n hn hunit hinv
      ((Functor.extPairingLinearMap _ _ n F (moduleRootsOfUnity U n) 2 0 2 rfl).flip
        (a • Ext.mk₀ f) c) = _
  rw [Functor.extPairingLinearMap_smul_mk₀_right]
  exact (moduleCompactSupportTraceLinearMap X hX D hfin hclosed j hD n hn hunit hinv).map_smul a _

/-- Evaluation against the original identity is exactly the original normalized trace. -/
theorem moduleTracePairingLinearMap_mk₀_id :
    (moduleTracePairingLinearMap X hX D hfin hclosed j hD n hn hunit hinv
      (moduleRootsOfUnity U n) 2 0 rfl).flip (Ext.mk₀ (𝟙 (moduleRootsOfUnity U n))) =
      moduleCompactSupportTraceLinearMap X hX D hfin hclosed j hD n hn hunit hinv := by
  ext c
  change moduleCompactSupportTraceLinearMap X hX D hfin hclosed j hD n hn hunit hinv
    (Functor.extPairing _ _ c (Ext.mk₀ (𝟙 _)) (add_zero 2)) = _
  rw [Functor.extPairing_mk₀_id_right]

end AlgebraicGeometry.Scheme.EtaleCohomology
