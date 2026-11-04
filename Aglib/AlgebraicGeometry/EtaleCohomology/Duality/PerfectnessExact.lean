/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.PerfectnessExact
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.CoefficientDevissage

/-!
# Original trace perfectness on a middle coefficient

The complete variable-functor Ext construction supplies the six rows. The
native instance below supplies its original lower-shriek functor, Ext actions,
trace pairing and unsigned extension-class laws. No comparison or desired
commutativity field is assumed in the native statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u wU wX wA

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients Scheme.OverField

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard moduleSheafExtZModModule

variable {k : Type u} [Field k] [IsAlgClosed k] (X : FScheme k) (hX : Curve.Properties X)
  (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(X.left, ⊤)))
  [HasExt.{wU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wX} (ModuleSheaf X.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} X.left)]

private theorem original_pairing_coefficient_value
    {F G : ModuleSheaf U (ULift.{u + 1} (ZMod n))} (f : F ⟶ G)
    (r : ℕ) (hr : r ≤ 2)
    (c : Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj F) r)
    (e : Ext.{wU} G (moduleRootsOfUnity U n) (2 - r)) :
    moduleDualityMap.{u, wU, wX, wA} X hX D hfin hclosed j hD n hn hunit hinv G r hr
        (c.comp (Ext.mk₀ ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).map f))
          (add_zero r)) e =
      moduleDualityMap.{u, wU, wX, wA} X hX D hfin hclosed j hD n hn hunit hinv F r hr c
        ((Ext.mk₀ f).comp e (zero_add (2 - r))) := by
  have h := moduleDualityMap_naturality.{u, wU, wX, wA}
    X hX D hfin hclosed j hD n hn hunit hinv f r hr
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) e

private theorem original_pairing_boundary_zero_value
    {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact)
    (c : Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj S.X₃) 0)
    (e : Ext.{wU} S.X₁ (moduleRootsOfUnity U n) (2 - 1)) :
    moduleDualityMap.{u, wU, wX, wA} X hX D hfin hclosed j hD n hn hunit hinv S.X₁ 1
        (by decide) (c.comp
          (shortExact_moduleLowerShriek j (ULift.{u + 1} (ZMod n)) hS).extClass rfl) e =
      moduleDualityMap.{u, wU, wX, wA} X hX D hfin hclosed j hD n hn hunit hinv S.X₃ 0
        (by decide) c (hS.extClass.comp e (show 1 + (2 - 1) = (2 - 0 : ℕ) from by omega)) := by
  have h := moduleTracePairingLinearMap_extClass.{u, wU, wX, wA}
    X hX D hfin hclosed j hD n hn hunit hinv hS 0 1 (2 - 1) (2 - 0)
      rfl (by omega) (by omega) (by omega)
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) e

private theorem original_pairing_boundary_one_value
    {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact)
    (c : Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj S.X₃) 1)
    (e : Ext.{wU} S.X₁ (moduleRootsOfUnity U n) (2 - 2)) :
    moduleDualityMap.{u, wU, wX, wA} X hX D hfin hclosed j hD n hn hunit hinv S.X₁ 2
        (by decide) (c.comp
          (shortExact_moduleLowerShriek j (ULift.{u + 1} (ZMod n)) hS).extClass rfl) e =
      moduleDualityMap.{u, wU, wX, wA} X hX D hfin hclosed j hD n hn hunit hinv S.X₃ 1
        (by decide) c (hS.extClass.comp e (show 1 + (2 - 2) = (2 - 1 : ℕ) from by omega)) := by
  have h := moduleTracePairingLinearMap_extClass.{u, wU, wX, wA}
    X hX D hfin hclosed j hD n hn hunit hinv hS 1 2 (2 - 2) (2 - 1)
      rfl (by omega) (by omega) (by omega)
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) e

/-- Both original adjoints pass from the outer coefficients to an actual
middle coefficient. All new law inputs of the homological construction are
proved here from the original trace pairing and unsigned extension classes. -/
theorem moduleDualityMap_middle_isPerfPair_of_shortExact
    {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact)
    (hA : ∀ r hr, (moduleDualityMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv S.X₁ r hr).IsPerfPair)
    (hQ : ∀ r hr, (moduleDualityMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv S.X₃ r hr).IsPerfPair)
    (hCA : Subsingleton (Ext.{wX} (moduleUnit X.left (ULift.{u + 1} (ZMod n)))
      ((moduleLowerShriek j (ULift.{u + 1} (ZMod n))).obj S.X₁) 3))
    (hEQ : Subsingleton (Ext.{wU} S.X₃ (moduleRootsOfUnity U n) 3))
    (r : ℕ) (hr : r ≤ 2) :
    (moduleDualityMap.{u, wU, wX, wA}
      X hX D hfin hclosed j hD n hn hunit hinv S.X₂ r hr).IsPerfPair := by
  let Λ := ULift.{u + 1} (ZMod n)
  let L := moduleLowerShriek j Λ
  let A := moduleUnit X.left Λ
  let N := moduleRootsOfUnity U n
  let compactModule : ∀ (F : ModuleSheaf U Λ) (q : ℕ),
      Module (ZMod n) (Ext.{wX} A (L.obj F) q) :=
    fun F q => moduleSheafExtZModModule n A (L.obj F) q
  let sourceModule : ∀ (F : ModuleSheaf U Λ) (q : ℕ),
      Module (ZMod n) (Ext.{wU} F N q) :=
    fun F q => moduleSheafExtZModModule n F N q
  let P := fun F r hr => moduleDualityMap.{u, wU, wX, wA}
    X hX D hfin hclosed j hD n hn hunit hinv F r hr
  have hL := shortExact_moduleLowerShriek j Λ hS
  exact Ext.isPerfPair_middle_of_shortExact L A N n hn
    (compactModule := compactModule) (sourceModule := sourceModule) hS hL P
    (fun f r hr c e => original_pairing_coefficient_value
      X hX D hfin hclosed j hD n hn hunit hinv f r hr c e)
    (original_pairing_boundary_zero_value X hX D hfin hclosed j hD n hn hunit hinv hS)
    (original_pairing_boundary_one_value X hX D hfin hclosed j hD n hn hunit hinv hS)
    hA hQ hCA hEQ r hr

end AlgebraicGeometry.Scheme.EtaleCohomology
