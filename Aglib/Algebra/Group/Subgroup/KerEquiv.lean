/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Tactic.Abel

/-!
# Kernels under retractions and under commuting comparisons

A retraction `r : A →+ B` with a section `s` splits its source:
`AddMonoidHom.retractionAddEquiv : A ≃+ B × ker r`, `c ↦ (r c, c - s (r c))`. Two additive
maps compared by an additive equivalence of their sources and an injective additive map of
their targets have equivalent kernels (`AddMonoidHom.kerAddEquivOfComm`). The groups are
commutative, in arbitrary universes.

The current consumer is the Picard tangent space
(`Aglib.AlgebraicGeometry.Picard.Tangent.Thickening`).
-/

@[expose] public section

namespace AddMonoidHom

/-- A retraction of additive groups splits the source: `A ≃+ B × ker r`,
`c ↦ (r c, c - s (r c))`. -/
def retractionAddEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (r : A →+ B) (s : B →+ A) (hrs : ∀ b, r (s b) = b) : A ≃+ B × r.ker where
  toFun c := (r c, ⟨c - s (r c), by rw [AddMonoidHom.mem_ker, map_sub, hrs, sub_self]⟩)
  invFun a := s a.1 + a.2.1
  left_inv c := by
    change s (r c) + (c - s (r c)) = c
    abel
  right_inv a := by
    obtain ⟨a, k, hk⟩ := a
    have hk' : r k = 0 := hk
    refine Prod.ext ?_ (Subtype.ext ?_)
    · change r (s a + k) = a
      rw [map_add, hrs, hk', add_zero]
    · change s a + k - s (r (s a + k)) = k
      rw [map_add, hrs, hk', add_zero]
      abel
  map_add' c d := by
    refine Prod.ext (map_add r c d) (Subtype.ext ?_)
    change c + d - s (r (c + d)) = (c - s (r c)) + (d - s (r d))
    rw [map_add, map_add]
    abel

/-- Additive maps compared by an additive equivalence of sources and an injective additive
map of targets have equivalent kernels. -/
def kerAddEquivOfComm {A B A' B' : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup A'] [AddCommGroup B'] (f : A →+ B) (f' : A' →+ B') (eA : A ≃+ A')
    (eB : B →+ B') (heB : Function.Injective eB) (hcomm : ∀ a, eB (f a) = f' (eA a)) :
    f.ker ≃+ f'.ker where
  toFun c := ⟨eA c.1, by
    rw [AddMonoidHom.mem_ker, ← hcomm, AddMonoidHom.mem_ker.mp c.2, map_zero]⟩
  invFun x := ⟨eA.symm x.1, by
    rw [AddMonoidHom.mem_ker]
    apply heB
    rw [hcomm, AddEquiv.apply_symm_apply, AddMonoidHom.mem_ker.mp x.2, map_zero]⟩
  left_inv c := Subtype.ext (eA.symm_apply_apply c.1)
  right_inv x := Subtype.ext (eA.apply_symm_apply x.1)
  map_add' c d := Subtype.ext (map_add eA c.1 d.1)

end AddMonoidHom
