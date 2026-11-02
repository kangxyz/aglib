/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Picard.KummerQuotient

/-!
# Original Picard quotient maps and their whole Kummer square

These interfaces retain identity, composition and the original representatives at every
natural level, then the whole boundary square at a positive invertible level, with independent
Ext universes on the two schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.EtaleCohomology
open AlgebraicGeometry.Scheme.Modules.Invertible
open GroupCohomology.Kummer.CoefficientBaseChange

universe u w w'

namespace AglibTest.PicardKummerQuotient

variable {X S T : Scheme.{u}}

/-- Quotient pullback retains geometric identity without a level-invertibility hypothesis. -/
example (n : ℕ) : Picard.picardQuotientPullback (𝟙 X) n = AddMonoidHom.id _ :=
  Picard.picardQuotientPullback_id n

/-- Quotient pullback retains the whole composition law. -/
example (f : S ⟶ X) (g : T ⟶ S) (n : ℕ) :
    (Picard.picardQuotientPullback g n).comp (Picard.picardQuotientPullback f n) =
      Picard.picardQuotientPullback (g ≫ f) n :=
  Picard.picardQuotientPullback_comp f g n

/-- The shared constructor preserves the literal original Picard representative. -/
example (f : S ⟶ X) (n : ℕ) (c : PicardGroup X) :
    Picard.picardQuotientPullback f n (QuotientAddGroup.mk c) =
      QuotientAddGroup.mk (pullbackClass f c) :=
  Picard.picardQuotientPullback_mk f n c

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- The whole boundary square preserves independent source and target Ext universes. -/
example (f : S ⟶ X) (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :
    (Kummer.rootsCohomologyPullback f n hn hinv 2).comp
        (Picard.picardQuotientBoundary X n hn hinv) =
      (Picard.picardQuotientBoundary S n hn (levelInvertible f n hinv)).comp
        (Picard.picardQuotientPullback f n) :=
  Picard.picardQuotientBoundary_naturality f n hn hinv

/-- The pre-existing evaluated statement is retained. -/
example (f : S ⟶ X) (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (c : PicardGroup X ⧸ (nsmulAddMonoidHom (α := PicardGroup X) n).range) :
    Kummer.rootsCohomologyPullback f n hn hinv 2 (Picard.picardQuotientBoundary X n hn hinv c) =
      Picard.picardQuotientBoundary S n hn (levelInvertible f n hinv)
        (Picard.picardQuotientPullback f n c) :=
  Picard.picardQuotientBoundary_pullback f n hn hinv c

end AglibTest.PicardKummerQuotient

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Picard.picardQuotientPullback' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Picard.picardQuotientPullback

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Picard.picardQuotientPullback_id' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Picard.picardQuotientPullback_id

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Picard.picardQuotientPullback_comp' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Picard.picardQuotientPullback_comp

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Picard.picardQuotientBoundary_naturality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Picard.picardQuotientBoundary_naturality

/-- info: 'AlgebraicGeometry.Scheme.EtaleCohomology.Picard.picardQuotientBoundary_pullback' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.EtaleCohomology.Picard.picardQuotientBoundary_pullback
