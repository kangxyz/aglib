/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupTheory.Torsion.Levels

/-!
# Equivalences of natural torsion levels


Source: `R5Lab.Aglib.GroupTheory.Torsion.Equivalence`.
Packet SHA-256:
`ede5baef8279fa81b49d4df9a703ae1b06a33b2b77778565b4eb22ac938e1cea`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

noncomputable section
namespace AddEquiv
section TorsionSubgroupTransport
variable {P Q : Type*} [AddCommGroup P] [AddCommGroup Q]

/-- Restriction of an actual point-group equivalence to literal multiplication kernels. -/
def torsionByNat (n : ℕ) (e : P ≃+ Q) :
    AddSubgroup.torsionBy P (n : ℤ) ≃+ AddSubgroup.torsionBy Q (n : ℤ) where
  toFun x := ⟨e x.val, by
    apply AddSubgroup.torsionBy.nsmul_iff.mpr
    have hx : n • x.val = 0 := AddSubgroup.torsionBy.nsmul_iff.mp x.property
    rw [← map_nsmul, hx, map_zero]⟩
  invFun y := ⟨e.symm y.val, by
    apply AddSubgroup.torsionBy.nsmul_iff.mpr
    have hy : n • y.val = 0 := AddSubgroup.torsionBy.nsmul_iff.mp y.property
    rw [← map_nsmul, hy, map_zero]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (e.map_add x.val y.val)

end TorsionSubgroupTransport
end AddEquiv
