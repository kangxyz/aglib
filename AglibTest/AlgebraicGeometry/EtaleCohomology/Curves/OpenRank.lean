/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.OpenRank

/-! Original cohomology, internal auxiliary worlds, and the actual localization maps. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.OverField.Curve
open AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
open AlgebraicGeometry.Scheme.EtaleCohomology.Curves
open GroupCohomology.Kummer.Coefficients

universe u wM wMU wA wAU

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable {k : Type u} [Field k] [IsAlgClosed k] {C : FScheme k}
  (hC : Curve.Properties C) (D : Set C.left) [Finite D]
  (hclosed : ∀ x ∈ D, IsClosed ({x} : Set C.left))
  {U : Scheme.{u}} (j : U ⟶ C.left) [IsOpenImmersion j]
  (hD : Set.range j = Dᶜ) (hne : D.Nonempty)
  [HasExt.{wAU} (AbelianSheaf.{u, u + 1} U)]

example (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) :
    Nat.card (Sheaf.H.{wAU} (mu U n) 1) =
      n ^ (2 * coherentGenus k C + Nat.card D - 1) :=
  card_rootsOne_of_finite_nonempty_complement hC D hclosed j hD hne n hn hunit

example : Nat.card (Sheaf.H.{wAU} (mu U 1) 1) = 1 :=
  (card_rootsOne_of_finite_nonempty_complement hC D hclosed j hD hne 1 (by decide)
    (by simpa only [Nat.cast_one] using (isUnit_one : IsUnit (1 : k)))).trans (one_pow _)

example (hg : coherentGenus k C = 0) (n : ℕ) (hn : 0 < n)
    (hunit : IsUnit (n : k)) :
    Nat.card (Sheaf.H.{wAU} (ConstantFinite.coefficient (ULift.{u} (ZMod n)) U) 1) =
      n ^ (Nat.card D - 1) := by
  simpa only [hg, Nat.mul_zero, Nat.zero_add] using
    card_constantOne_of_finite_nonempty_complement hC D hclosed j hD hne n hn hunit

example (hunit : IsUnit (6 : k)) :
    Nat.card (Sheaf.H.{wAU} (mu U 6) 1) =
      6 ^ (2 * coherentGenus k C + Nat.card D - 1) :=
  card_rootsOne_of_finite_nonempty_complement hC D hclosed j hD hne 6 (by decide) hunit

section OriginalMaps

variable (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
  [HasExt.{wM} (ModuleSheaf C.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wMU} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{wA} (AbelianSheaf.{u, u + 1} C.left)]

local instance : Fintype D := Fintype.ofFinite D

example : Function.Exact (Kummer.rootsCohomologyPullback j n hn
    (modulePoint_globalLevelInvertible n hunit) 1)
    (rootsOneLocalizationBoundary hC D hclosed j hD n hn hunit) :=
  rootsOneLocalizationBoundary_exact hC D hclosed j hD n hn hunit

example : (rootsOneLocalizationBoundary hC D hclosed j hD n hn hunit).range =
    (∑ x : D, Pi.evalAddMonoidHom (fun _ : D => ZMod n) x).ker :=
  rootsOneLocalizationBoundary_range hC D hclosed j hD n hn hunit

end OriginalMaps

end
