/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ZMod
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ZModLocallyConstant

/-! # Constructible modules agree with the original positive ZMod coefficients

The general finite-type module predicate agrees, at every positive modulus,
with the original finite-abelian constructibility predicate. The proof uses
the same affine opens, strata and immersions in both directions. Consequently
the canonical bounded lift of an original constructible abelian coefficient
is constructible as an actual module-valued sheaf, not merely after forgetting.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- Lift an original finite-abelian partition without changing any of its
actual strata, their immersions, or its cover of the original scheme. -/
def ConstructiblePartition.ofZModUnderlying {X : Scheme.{u}} (n : ℕ)
    (F : ModuleSheaf (ZMod n) X)
    (t : Constructible.ConstructiblePartition ((moduleUnderlying (ZMod n) X).obj F)) :
    ConstructiblePartition F where
  toFiniteLocallyClosedPartition := t.toFiniteLocallyClosedPartition
  locally_constant i := isFiniteTypeLocallyConstant_of_zmodUnderlying n
    ((isFiniteLocallyConstant_iff_of_iso
      ((moduleInverseImageUnderlyingIso (ZMod n) (t.inclusion i)).app F)).mpr
        (t.locally_constant i))

/-- Original finite-abelian constructibility implies finite-type module
constructibility for genuine ZMod coefficients, even at modulus zero. -/
theorem isConstructible_of_zmodUnderlying {X : Scheme.{u}} (n : ℕ)
    {F : ModuleSheaf (ZMod n) X}
    (hF : Constructible.IsConstructible ((moduleUnderlying (ZMod n) X).obj F)) :
    IsConstructible F := by
  intro U
  obtain ⟨t⟩ := hF U
  let t' := Constructible.ConstructiblePartition.ofIso t
    ((moduleInverseImageUnderlyingIso (ZMod n) U.1.ι).app F).symm
  exact ⟨ConstructiblePartition.ofZModUnderlying n _ t'⟩

/-- At positive modulus the general module predicate is exactly the original
finite-abelian constructibility predicate on its original underlying sheaf. -/
theorem isConstructible_zmod_iff {X : Scheme.{u}} (n : ℕ) (hn : 0 < n)
    (F : ModuleSheaf (ZMod n) X) :
    IsConstructible F ↔
      Constructible.IsConstructible ((moduleUnderlying (ZMod n) X).obj F) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact ⟨isConstructible_underlying, isConstructible_of_zmodUnderlying n⟩

/-- Canonical conversion of an original bounded coefficient preserves and
reflects constructibility as genuine modules at every positive modulus. -/
theorem isConstructible_canonicalZModSheaf_iff {X : Scheme.{u}} (n : ℕ) (hn : 0 < n)
    (F : AbelianSheaf.{u, u + 1} X) (hF : n • 𝟙 F = 0) :
    IsConstructible (TorsionZMod.sheaf X.smallEtaleTopology n F hF) ↔
      Constructible.IsConstructible F :=
  (isConstructible_zmod_iff n hn _).trans (isConstructible_zmodSheaf_iff n F hF)

/-- A constructible abelian coefficient on a qcqs scheme admits a positive
modulus and a genuinely constructible module lift with its original underlying isomorphism. -/
theorem exists_constructible_zmodSheaf {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (F : AbelianSheaf.{u, u + 1} X) (hF : Constructible.IsConstructible F) :
    ∃ n : ℕ, 0 < n ∧ ∃ M : ModuleSheaf (ZMod n) X,
      IsConstructible M ∧ Nonempty ((moduleUnderlying (ZMod n) X).obj M ≅ F) := by
  obtain ⟨n, hn, hk⟩ := exists_positive_annihilator_of_isConstructible F hF
  refine ⟨n, hn, TorsionZMod.sheaf X.smallEtaleTopology n F hk, ?_,
    ⟨TorsionZMod.sheafUnderlyingIso X.smallEtaleTopology n F hk⟩⟩
  exact (isConstructible_canonicalZModSheaf_iff n hn F hk).mpr hF

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
