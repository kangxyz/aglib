/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ClosedPointPrefix

/-!
# Original structural maps of finite closed-point prefixes

The composite is defined directly on the existing finite prefixes. It does not
require extension to an infinite path, and retains the actual selected points.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix

variable {eligible : (Y : Scheme.{u}) → Y → Prop} {X : Scheme.{u}} {x : X}

/-- The original finite composite from the actual endpoint to the original root. -/
def toBase : {n : ℕ} → (p : Prefix eligible X x n) → (scheme p ⟶ X)
  | 0, _ => 𝟙 X
  | _n + 1, p => (datum (parent p)).map ≫ toBase (parent p)

@[simp]
theorem toBase_zero (p : Prefix eligible X x 0) : toBase p = 𝟙 X := rfl

/-- Appending a child prepends its original blowdown to the same structural map. -/
@[simp]
theorem toBase_snoc {n : ℕ} (p : Prefix eligible X x n)
    (y : Child eligible (scheme p) (point p)) :
    toBase (snoc p y) = (datum p).map ≫ toBase p := rfl

/-- The original selected endpoint lies over the original root point. -/
@[simp]
theorem toBase_point {n : ℕ} (p : Prefix eligible X x n) :
    toBase p (point p) = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp : (datum (parent p)).map p.2.val = point (parent p) := p.2.property.2.1
    exact (congrArg (fun y : scheme (parent p) => toBase (parent p) y) hp).trans
      (ih (parent p))

end AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix
