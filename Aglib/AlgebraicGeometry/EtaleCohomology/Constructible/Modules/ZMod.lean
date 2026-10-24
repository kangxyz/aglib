/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionColimit.Bounded
public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Sheaf
public import Mathlib.RingTheory.Finiteness.Cardinality

/-! # Actual ZMod coefficients of constructible abelian sheaves

The canonical scalar conversion retains the original abelian sheaf, its finite
local trivializations, and its actual constructible strata. There is no second
finite-abelian constructibility predicate. On a qcqs scheme the established
positive-annihilator theorem produces a genuine ZMod-valued lift of every
constructible abelian coefficient. This adapter does not identify finite
cardinality with finite generation over an arbitrary coefficient ring.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} (n : ℕ) (F : AbelianSheaf.{u, u + 1} X)
  (hF : n • 𝟙 F = 0)

/-- Canonical scalar conversion preserves and reflects the original finite
local constancy predicate through its original underlying isomorphism. -/
theorem isFiniteLocallyConstant_zmodSheaf_iff :
    IsFiniteLocallyConstant
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})).obj
          (TorsionZMod.sheaf X.smallEtaleTopology n F hF)) ↔
      IsFiniteLocallyConstant F :=
  isFiniteLocallyConstant_iff_of_iso
    (TorsionZMod.sheafUnderlyingIso X.smallEtaleTopology n F hF)

/-- Canonical scalar conversion preserves and reflects constructibility with
the same affine-local locally closed partitions of the original scheme. -/
theorem isConstructible_zmodSheaf_iff :
    IsConstructible
      ((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})).obj
          (TorsionZMod.sheaf X.smallEtaleTopology n F hF)) ↔
      IsConstructible F :=
  isConstructible_iff_of_iso
    (TorsionZMod.sheafUnderlyingIso X.smallEtaleTopology n F hF)

/-- The module conversion transports every original coefficient map, and its
comparison has the original map as its actual underlying composite. -/
@[reassoc]
theorem zmodSheafMap_underlying {G : AbelianSheaf.{u, u + 1} X}
    (hG : n • 𝟙 G = 0) (f : F ⟶ G) :
    (sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})).map
      (TorsionZMod.sheafMap X.smallEtaleTopology n hF hG f) ≫
        (TorsionZMod.sheafUnderlyingIso X.smallEtaleTopology n G hG).hom =
      (TorsionZMod.sheafUnderlyingIso X.smallEtaleTopology n F hF).hom ≫ f :=
  TorsionZMod.sheafMap_underlying X.smallEtaleTopology n hF hG f

/-- Every constructible abelian coefficient on a qcqs scheme has a positive
modulus and an actual module-valued lift with its original underlying sheaf. -/
theorem exists_zmodSheaf_of_isConstructible
    [CompactSpace X] [QuasiSeparatedSpace X] (h : IsConstructible F) :
    ∃ n : ℕ, 0 < n ∧ ∃ M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n)),
      Nonempty (((sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} (ZMod n)) AddCommGrpCat.{u + 1})).obj M) ≅ F) := by
  obtain ⟨n, hn, hkill⟩ := exists_positive_annihilator_of_isConstructible F h
  exact ⟨n, hn, TorsionZMod.sheaf X.smallEtaleTopology n F hkill,
    ⟨TorsionZMod.sheafUnderlyingIso X.smallEtaleTopology n F hkill⟩⟩

/-- Over a positive finite residue ring, and only in this specialization,
finite generation of a local module value is equivalent to finite cardinality. -/
theorem finite_zmodModule_iff (n : ℕ) (hn : 0 < n)
    (M : ModuleCat.{u + 1} (ZMod n)) :
    Module.Finite (ZMod n) M ↔ Finite M := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact Module.finite_iff_finite

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
