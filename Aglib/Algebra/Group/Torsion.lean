/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.GroupTheory.Index

/-!
# Transport and finiteness of actual additive torsion subgroups


Source: `R5Lab.Aglib.Algebra.Group.Torsion`.
Packet SHA-256:
`0ca5e3f850d6bd411485899b7dbfe97ad1c62cff19a9325f56dbc8cf84c2c84e`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

namespace AddCommGroup

section Torsion

variable {A C : Type*} [AddCommGroup A] [AddCommGroup C]

/-- Additive equivalences transport the actual torsion subgroups.
Source: auxiliary torsion algebra for `K2-015#thm:k2015-characters`, at the module snapshot. -/
def torsionTransport (e : A ≃+ C) : AddCommGroup.torsion A ≃+ AddCommGroup.torsion C where
  toFun x := ⟨e x, (AddCommGroup.le_comap_torsion e.toAddMonoidHom) x.property⟩
  invFun x := ⟨e.symm x, (AddCommGroup.le_comap_torsion e.symm.toAddMonoidHom) x.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_add' x y := Subtype.ext (map_add e (x : A) (y : A))

/-- Torsion of a binary product is the product of the actual torsion subgroups.
Source: auxiliary torsion algebra for `K2-015#thm:k2015-characters`, at the module snapshot. -/
def torsionProductEquiv (A C : Type*) [AddCommGroup A] [AddCommGroup C] :
    AddCommGroup.torsion (A × C) ≃+ AddCommGroup.torsion A × AddCommGroup.torsion C where
  toFun x :=
    let h : x.val.1 ∈ AddCommGroup.torsion A ∧ x.val.2 ∈ AddCommGroup.torsion C := by
      simpa only [AddCommGroup.torsion_sum, AddSubgroup.mem_prod] using x.property
    (⟨x.val.1, h.1⟩, ⟨x.val.2, h.2⟩)
  invFun x := ⟨(x.1.val, x.2.val), by
    rw [AddCommGroup.torsion_sum]
    exact ⟨x.1.property, x.2.property⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- A finite additive group equals its torsion subgroup, by the finite-order theorem.
Source: auxiliary base-torsion algebra for `K2-015#thm:k2015-characters`, at the module snapshot. -/
def finiteTorsionEquiv (A : Type*) [AddCommGroup A] [Finite A] : AddCommGroup.torsion A ≃+ A where
  toFun := Subtype.val
  invFun x := ⟨x, isOfFinAddOrder_of_finite x⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- A finite constant subgroup and finite quotient torsion imply finite original
torsion. No quotient section or splitting is required. -/
theorem finite_torsion_of_finite_quotient (S : AddSubgroup A)
    [Finite S] [Finite (AddCommGroup.torsion (A ⧸ S))] :
    Finite (AddCommGroup.torsion A) := by
  let q := QuotientAddGroup.mk' S
  let f : AddCommGroup.torsion A →+ AddCommGroup.torsion (A ⧸ S) :=
    (q.comp (AddCommGroup.torsion A).subtype).codRestrict
      (AddCommGroup.torsion (A ⧸ S))
      (fun x => AddCommGroup.le_comap_torsion q x.property)
  let e : f.ker → S := fun x =>
    ⟨x.val.val, (QuotientAddGroup.eq_zero_iff x.val.val).mp
      (congrArg Subtype.val x.property)⟩
  have he : Function.Injective e := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : S => (z : A)) h
  let : Finite f.ker := Finite.of_injective e he
  exact f.finite_iff_finite_ker_range.mpr ⟨inferInstance, inferInstance⟩


/-- The actual torsion subgroup is a torsion `ℤ`-module; no global finiteness is required.
Source: auxiliary input preparation for `K2-015#lem:k2015-frobenius`, at the module snapshot. -/
theorem torsion_isTorsion_int (A : Type*) [AddCommGroup A] :
    Module.IsTorsion ℤ (AddCommGroup.torsion A) := by
  apply isAddTorsion_iff_isTorsion_int.mp
  intro x
  apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
  obtain ⟨n, hn, hzero⟩ := x.property.exists_nsmul_eq_zero
  exact ⟨n, hn, Subtype.ext hzero⟩

end Torsion

end AddCommGroup
