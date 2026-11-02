/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.UniverseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.ConstantRestriction

/-! # Universe naturality of the original cohomology pullback and constant restriction

Both Ext universes may change independently. These are equations for the
existing maps, not replacement definitions of pullback or restriction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u e₀ e₁ d₀ d₁

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}}
  [HasExt.{e₀} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{e₁} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{d₀} (AbelianSheaf.{u, u + 1} S)]
  [HasExt.{d₁} (AbelianSheaf.{u, u + 1} S)]

/-- Original cohomology pullback commutes with independent universe changes. -/
theorem cohomologyPullback_chgUniv (f : S ⟶ X)
    (L : AbelianSheaf.{u, u + 1} X) (q : ℕ) (x : Sheaf.H.{e₀} L q) :
    Ext.chgUniv.{d₁} (cohomologyPullback.{u, e₀, d₀} f L q x) =
      cohomologyPullback.{u, e₁, d₁} f L q (Ext.chgUniv.{e₁} x) := by
  rw [cohomologyPullback_apply.{u, e₀, d₀},
    cohomologyPullback_apply.{u, e₁, d₁},
    Ext.chgUniv_comp.{_, _, d₀, d₁}, Ext.chgUniv_mk₀.{_, _, d₀, d₁}]
  exact congrArg (fun z =>
    (Ext.mk₀ (((inverseImageConstantIso f).app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv) : Ext.{d₁} _ _ 0).comp z (zero_add q))
    (Ext.chgUniv_mapExactFunctor.{_, _, _, _, e₀, e₁, d₀, d₁} (inverseImage f) x)

open Curves

/-- The original constant restriction retains its coefficient transport under
independent changes of the source and target Ext universes. -/
theorem Curves.constantRestriction_chgUniv
    (A : Type u) [AddCommGroup A] (f : S ⟶ X) (q : ℕ)
    (x : Sheaf.H.{e₀} (ConstantFinite.coefficient A X) q) :
    Ext.chgUniv.{d₁} (constantRestriction.{u, e₀, d₀} A f q x) =
      constantRestriction.{u, e₁, d₁} A f q (Ext.chgUniv.{e₁} x) := by
  rw [constantRestriction_apply, Sheaf.H.map_apply, Ext.chgUniv_comp,
    Ext.chgUniv_mk₀, cohomologyPullback_chgUniv.{u, e₀, e₁, d₀, d₁},
    constantRestriction_apply, Sheaf.H.map_apply]

/-- Vanishing of the same original restriction is independent of both Ext
universe choices. This transports a classwise effacement witness unchanged. -/
theorem Curves.constantRestriction_eq_zero_iff_chgUniv
    (A : Type u) [AddCommGroup A] (f : S ⟶ X) (q : ℕ)
    (x : Sheaf.H.{e₀} (ConstantFinite.coefficient A X) q) :
    constantRestriction.{u, e₀, d₀} A f q x = 0 ↔
      constantRestriction.{u, e₁, d₁} A f q (Ext.chgUniv.{e₁} x) = 0 := by
  have hchange := constantRestriction_chgUniv.{u, e₀, e₁, d₀, d₁} A f q x
  constructor
  · intro h
    rw [← hchange, h, Ext.chgUniv_zero]
  · intro h
    apply (Ext.chgUniv.{d₁, d₀}).injective
    simpa only [Ext.chgUniv_zero] using hchange.trans h

end AlgebraicGeometry.Scheme.EtaleCohomology
