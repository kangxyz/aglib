/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.CompactSupportPairing

/-!
# Tests for the Yoneda pairing on compactly supported cohomology of abelian sheaves

The examples take an open immersion `j : U ⟶ X`, `Λ = ULift (ZMod n)` and `G = μ_n`: the
pairing `H^r_c(U, F₀) × Ext^{2-r}_{U,n}(F, μ_n) → H^2_c(U, μ_n)` on `CompactSupport.H`, with
values in the Kummer sheaf `μ_n`, and its naturality and connecting-map squares. They guard the
axioms of every new declaration.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

namespace AglibTest.EtaleDualityCompactSupportPairing

attribute [local instance] hasSheafifyLarge

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ)

local instance (Y : Scheme.{u}) : HasExt.{u + 2} (ModuleSheaf Y (ULift.{u + 1} (ZMod n))) :=
  HasExt.standard _

local instance (Y : Scheme.{u}) : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} Y) :=
  HasExt.standard _

/-- The degree-two pairing with values in `H^2_c(U, μ_n)` of the Kummer sheaf. -/
example (F : ModuleSheaf U (ULift.{u + 1} (ZMod n))) (r : ℕ) (hr : r ≤ 2)
    (x : CompactSupport.H.{u + 2} j
      ((SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).obj F) r)
    (e : Ext.{u + 2} F (moduleRootsOfUnity U n) (2 - r)) :
    CompactSupport.H.{u + 2} j (GroupCohomology.Kummer.Coefficients.mu U n) 2 :=
  compactSupportRootsPairing.{u + 2, u + 2} j n x e (by lia)

/-- Naturality in the first variable, for `G = μ_n`. -/
example {F F' : ModuleSheaf U (ULift.{u + 1} (ZMod n))} (f : F ⟶ F') {r s : ℕ}
    (x : CompactSupport.H.{u + 2} j
      ((SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).obj F) r)
    (e' : Ext.{u + 2} F' (moduleRootsOfUnity U n) s) :
    compactSupportPairing.{u + 2, u + 2} j _
        (CompactSupport.H.map j
          ((SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).map f) r x) e' rfl =
      compactSupportPairing.{u + 2, u + 2} j _ x ((Ext.mk₀ f).comp e' (zero_add s)) rfl :=
  compactSupportPairing_naturality f x e' rfl

/-- Connecting maps, sign `+1`, for `G = μ_n`. -/
example {S : ShortComplex (ModuleSheaf U (ULift.{u + 1} (ZMod n)))} (hS : S.ShortExact)
    (r s : ℕ)
    (x : CompactSupport.H.{u + 2} j
      ((SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).obj S.X₃) r)
    (e : Ext.{u + 2} S.X₁ (moduleRootsOfUnity U n) s) :
    compactSupportPairing.{u + 2, u + 2} j _
        (CompactSupport.δ j
          (hS.map_of_exact (SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))))
          r (r + 1) rfl x) e rfl =
      compactSupportPairing.{u + 2, u + 2} j _ x (hS.extClass.comp e (add_comm 1 s))
        (by lia) :=
  compactSupportPairing_δ hS x e (add_comm 1 s) rfl (by lia)

end AglibTest.EtaleDualityCompactSupportPairing

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.compactSupportPairing' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.compactSupportPairing

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.compactSupportPairingHom' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.compactSupportPairingHom

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.compactSupportPairingHom_apply_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.compactSupportPairingHom_apply_apply

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.compactSupportPairing_moduleLowerShriekCohomologyAddEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.compactSupportPairing_moduleLowerShriekCohomologyAddEquiv

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.compactSupportPairing_naturality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.compactSupportPairing_naturality

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.compactSupportPairing_comp_mk₀' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.compactSupportPairing_comp_mk₀

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.compactSupportPairing_δ' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.compactSupportPairing_δ

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.compactSupportRootsPairing' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.compactSupportRootsPairing

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.compactSupportRootsPairing_def' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.compactSupportRootsPairing_def
