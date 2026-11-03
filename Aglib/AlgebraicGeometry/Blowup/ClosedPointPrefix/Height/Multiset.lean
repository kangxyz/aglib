/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ClosedPointPrefix.Height
public import Mathlib.Data.Multiset.MapFold

/-!
# The multiset of existing heights at actual finite eligible roots

Only the native multiset constructor is added. Every entry is the existing
least empty level of the original prefix family; no height or tree is replaced.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

namespace AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix

variable {eligible : (Y : Scheme.{u}) → Y → Prop} {X : Scheme.{u}}
    (hroots : {x : X | eligible X x}.Finite)
    (hlevels : ∀ x : X, eligible X x → ∃ n, IsEmpty (Prefix eligible X x n))

/-- The native multiset of the existing heights at the actual finite eligible roots. -/
def heightMultiset : Multiset ℕ := by
  classical
  exact hroots.toFinset.val.attach.map fun z =>
    height (hlevels z.val (hroots.mem_toFinset.mp z.property))

/-- Any total abbreviation of the same actual heights gives the same native multiset. -/
theorem heightMultiset_eq_map (w : X → ℕ)
    (hw : ∀ (x : X) (hx : eligible X x), height (hlevels x hx) = w x) :
    heightMultiset hroots hlevels = hroots.toFinset.val.map w := by
  classical
  unfold heightMultiset
  rw [← Multiset.attach_map_val' hroots.toFinset.val w]
  apply Multiset.map_congr rfl
  intro z _
  exact hw z.val (hroots.mem_toFinset.mp z.property)

end AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix
