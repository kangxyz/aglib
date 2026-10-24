/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.Length

/-!
# Length from an original scalar factorization

If two original linear maps compose to multiplication by a scalar, the
kernel of the forward map lies in the original scalar torsion. The exact
kernel/range sequence bounds the source length by that torsion length and
the target length. All lengths are in `ℕ∞`; no finiteness or splitting is
assumed. The current consumer is the separable surface H1 bound obtained
from its actual trace-coordinate and adjugate maps.
-/

@[expose] public section

namespace Module

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- A scalar factorization bounds the original source length by its
original scalar-torsion length and the actual target length. -/
theorem length_le_torsionBy_add_of_comp_smul_id (d : R)
    (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (h : g.comp f = d • LinearMap.id) :
    Module.length R M ≤
      Module.length R (Submodule.torsionBy R M d) + Module.length R N := by
  have hker : LinearMap.ker f ≤ Submodule.torsionBy R M d := by
    intro x hx
    change f x = 0 at hx
    change d • x = 0
    have he := DFunLike.congr_fun h x
    change g (f x) = d • x at he
    rw [hx, map_zero] at he
    exact he.symm
  have hexact : Function.Exact (LinearMap.ker f).subtype f.rangeRestrict := by
    intro x
    constructor
    · intro hx
      have hz : f x = 0 := congrArg (fun y : LinearMap.range f => (y : N)) hx
      exact ⟨⟨x, hz⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact Subtype.ext y.property
  calc
    Module.length R M = Module.length R (LinearMap.ker f) +
        Module.length R (LinearMap.range f) :=
      Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict
        Subtype.val_injective (LinearMap.surjective_rangeRestrict f) hexact
    _ ≤ Module.length R (Submodule.torsionBy R M d) + Module.length R N :=
      add_le_add
        (Module.length_le_of_injective (Submodule.inclusion hker)
          (Submodule.inclusion_injective hker))
        (Module.length_le_of_injective (LinearMap.range f).subtype Subtype.val_injective)

end Module

namespace Module

variable {A B M N : Type*} [CommRing A] [CommRing B]
  [IsLocalRing A] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  [AddCommGroup N] [Module A N]

/-- Scalar restriction converts the actual torsion bound by the original
residue degree. The forward and reverse maps need only be A-linear. -/
theorem length_le_torsionBy_mul_residue_add_of_comp_smul_id (d : A)
    (f : M →ₗ[A] N) (g : N →ₗ[A] M)
    (h : g.comp f = d • LinearMap.id) :
    Module.length B M ≤
      Module.length B (Submodule.torsionBy B M (algebraMap A B d)) *
          Module.length (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) +
        Module.length A N := by
  have hrestrict : Module.length B M ≤ Module.length A M := by
    calc
      Module.length B M = Module.length B (⊤ : Submodule B M) := Module.length_top.symm
      _ ≤ Module.length A ((⊤ : Submodule B M).restrictScalars A) :=
        Submodule.length_le_length_restrictScalars A (⊤ : Submodule B M)
      _ = Module.length A M :=
        ((Submodule.topEquiv : (⊤ : Submodule B M) ≃ₗ[B] M).restrictScalars A).length_eq
  have ht : Submodule.torsionBy A M d =
      (Submodule.torsionBy B M (algebraMap A B d)).restrictScalars A := by
    ext x
    change d • x = 0 ↔ algebraMap A B d • x = 0
    rw [IsScalarTower.algebraMap_smul]
  calc
    Module.length B M ≤ Module.length A M := hrestrict
    _ ≤ Module.length A (Submodule.torsionBy A M d) + Module.length A N :=
      length_le_torsionBy_add_of_comp_smul_id d f g h
    _ = Module.length B (Submodule.torsionBy B M (algebraMap A B d)) *
          Module.length (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) +
        Module.length A N := by
      rw [ht]
      congr 1
      exact IsLocalRing.length_restrictScalars A B
        (Submodule.torsionBy B M (algebraMap A B d))

end Module
