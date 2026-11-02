/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ClosedPointPrefix.Composite
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.PointBlowupChain

/-!
# The actual point chain of a finite closed-point prefix

Only the selected finite levels are used. Their genuine dimension-two centres
give the existing native point-chain witness for the original finite composite.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix

variable {eligible : (Y : Scheme.{u}) → Y → Prop} {X : Scheme.{u}} {x : X}

/-- A finite prefix gives a native chain when its actual earlier centres have
local dimension two. No infinite continuation or future regularity is assumed. -/
def pointBlowupChain_toBase (hx : IsClosed ({x} : Set X))
    {n : ℕ} (p : Prefix eligible X x n)
    (hd : ∀ m (hm : m < n),
      ringKrullDim ((scheme (truncate (Nat.le_of_lt hm) p)).presheaf.stalk
        (point (truncate (Nat.le_of_lt hm) p))) = 2) :
    PointBlowupChain (toBase p) := by
  induction n with
  | zero => exact PointBlowupChain.refl X
  | succ n ih =>
    let q := parent p
    have hc : PointBlowupChain (toBase q) := ih q (fun m hm => by
      have h := hd m (Nat.lt_trans hm (Nat.lt_succ_self n))
      exact Eq.mp (congrArg
        (fun r : Prefix eligible X x m =>
          ringKrullDim ((scheme r).presheaf.stalk (point r)) = 2)
        (truncate_succ (Nat.le_of_lt hm) p)) h)
    have hdim : ringKrullDim ((scheme q).presheaf.stalk (point q)) = 2 := by
      exact Eq.mp (congrArg
        (fun r : Prefix eligible X x n =>
          ringKrullDim ((scheme r).presheaf.stalk (point r)) = 2)
        ((truncate_succ (Nat.le_refl n) p).trans (truncate_refl (parent p))))
        (hd n (Nat.lt_succ_self n))
    have hs : PointBlowupChain (datum q).map := by
      have hstep : PointBlowupChain (𝟙 (datum q).Y ≫ (datum q).map) :=
        PointBlowupChain.cons (point q) (point_closed hx q)
          hdim (𝟙 (datum q).Y) (PointBlowupChain.refl (datum q).Y)
      exact Eq.mp (congrArg (fun f : (datum q).Y ⟶ scheme q => PointBlowupChain f)
        (Category.id_comp (datum q).map)) hstep
    exact hc.comp hs

end AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix
