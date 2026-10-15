/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.BaseChange

/-! A prerequisite for the higher-simplex finite-cycle pullback attached to
K2-018#prop:k2018-arithmetic-characters, source revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982. The result is ordinary module theory,
with no projectivity assumption on the module being extended.

## Extraction basis

Transferred from `R5Lab.RingTheory.LocalLength.TorsionFreeBaseChange` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`18dac8e178a5ad512b07fe6e9eee530a18d8d6c2b6aedfe99493b3728ebb5739`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped _root_.TensorProduct
namespace Module
universe u v w
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [Module.Flat R S]

/-- Flat scalar extension from a domain preserves torsion-free modules. Embed into
the fraction-field extension, which is flat, and tensor that injection. -/
theorem torsionFree_baseChange (M : Type w) [AddCommGroup M] [Module R M]
    [Module.IsTorsionFree R M] : Module.IsTorsionFree S (S ⊗[R] M) := by
  let F := FractionRing R
  let V := F ⊗[R] M
  let i : M →ₗ[R] V := _root_.TensorProduct.mk R F M 1
  have hi : Function.Injective i := by
    apply (IsLocalizedModule.injective_iff_isRegular (nonZeroDivisors R) i).mpr
    intro r
    exact (IsRegular.of_ne_zero (nonZeroDivisors.ne_zero r.property)).isSMulRegular
  let : Module.Flat R V := Module.Flat.trans R F V
  let f : S ⊗[R] M →ₗ[S] S ⊗[R] V :=
    _root_.TensorProduct.AlgebraTensorModule.lTensor S S i
  have hf : Function.Injective f := Module.Flat.lTensor_preserves_injective_linearMap i hi
  exact hf.moduleIsTorsionFree f (fun s x => f.map_smul s x)

end Module
