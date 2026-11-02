/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.DegreeQuotient

/-! Interface examples and approved-foundation guards for the shared provider. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Curve.Properties X)

/-- The curve degree quotient retains level one and does not carry a selected basepoint. -/
example : Nonempty (PicardGroup X.left ⧸
    (nsmulAddMonoidHom (α := PicardGroup X.left) 1).range ≃+ ZMod 1) :=
  ⟨Curve.picardQuotientDegreeEquiv hX 1 (by simp)⟩

/-- Its original projection is degree modulo the level. -/
example (n : ℕ) (hn : IsUnit (n : k)) (c : PicardGroup X.left) :
    Curve.picardQuotientDegreeEquiv hX n hn (QuotientAddGroup.mk c) =
      Curve.curveDegreeMod hX n c :=
  Curve.picardQuotientDegreeEquiv_mk hX n hn c






/-- info: 'AlgebraicGeometry.Scheme.OverField.Curve.curveDegreeMod_ker_of_isUnit_of_isAlgClosed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.curveDegreeMod_ker_of_isUnit_of_isAlgClosed

/-- info: 'AlgebraicGeometry.Scheme.OverField.Curve.picardQuotientDegreeEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.picardQuotientDegreeEquiv

/-- info: 'AlgebraicGeometry.Scheme.OverField.Curve.picardQuotientDegreeEquiv_mk' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.picardQuotientDegreeEquiv_mk
