/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # A specified common open chart is the actual pullback -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A common open chart whose actual image is the intersection is cartesian.
The conclusion retains the given factorization maps. -/
theorem isPullback_of_openImmersion_range_inter
    {P U V Y : Scheme.{u}} (j : P ⟶ Y) [IsOpenImmersion j]
    (a : P ⟶ U) (b : P ⟶ V) (f : U ⟶ Y) (g : V ⟶ Y)
    [IsOpenImmersion f] [IsOpenImmersion g]
    (ha : a ≫ f = j) (hb : b ≫ g = j)
    (hr : Set.range j = Set.range f ∩ Set.range g) : IsPullback a b f g := by
  have w : a ≫ f = b ≫ g := ha.trans hb.symm
  let l (q : PullbackCone f g) : q.pt ⟶ P := IsOpenImmersion.lift j (q.fst ≫ f) (by
    rintro _ ⟨x, rfl⟩
    rw [hr]
    refine ⟨⟨q.fst x, rfl⟩, ⟨q.snd x, ?_⟩⟩
    change (q.snd ≫ g) x = (q.fst ≫ f) x
    rw [q.condition])
  have hl (q : PullbackCone f g) : l q ≫ j = q.fst ≫ f :=
    IsOpenImmersion.lift_fac j (q.fst ≫ f) _
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk w l
    (fun q => (cancel_mono f).mp (by rw [Category.assoc, ha, hl]))
    (fun q => (cancel_mono g).mp (by rw [Category.assoc, hb, hl, q.condition]))
    (by
      intro q m hm _
      apply (cancel_mono j).mp
      rw [hl, ← ha, ← Category.assoc, hm]))

end AlgebraicGeometry
