/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Module.SnakeLemma
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Tactic.Abel

/-!
# Actual homology of scalar multiplication

Scalar kernels, cokernels, induced maps, quotient equivalences and the six-term snake sequence
are constructed on the given modules. Exactness hypotheses are explicit; no regularity, flatness
or finite-length assumption is imposed by these constructions.

## Extraction basis

Transferred subsets of `R5Lab.RingTheory.LocalLength.PrincipalEulerAdditivity` at revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, source SHA-256
`26ee2397a837a665bc1b1c6f248fdacdc0d43009ea147acb68137233d7c5446d`. Objects, universes,
canonical maps and
actual premises are retained; declarations use native mathematical namespaces.
-/

@[expose] public section

noncomputable section

namespace Module
universe u v w z
variable {A : Type u} [CommRing A]
variable {U : Type v} {V : Type w} {W : Type z}
variable [AddCommGroup U] [Module A U] [AddCommGroup V] [Module A V]
variable [AddCommGroup W] [Module A W]

/-- The kernel of multiplication by `t` on `N`. -/
abbrev ScalarKernel (N : Type*) [AddCommGroup N] [Module A N] (t : A) :=
  LinearMap.ker (LinearMap.lsmul A N t)

/-- The cokernel of multiplication by `t` on `N`. -/
abbrev ScalarCokernel (N : Type*) [AddCommGroup N] [Module A N] (t : A) :=
  N ⧸ LinearMap.range (LinearMap.lsmul A N t)

/-- The linear map between kernels of multiplication by `t` induced by `f`. -/
def scalarKernelMap (f : U →ₗ[A] V) (t : A) :
    ScalarKernel U t →ₗ[A] ScalarKernel V t :=
  (f.comp (ScalarKernel U t).subtype).codRestrict (ScalarKernel V t) fun x => by
    change t • f x = 0
    rw [← f.map_smul]
    simpa only [LinearMap.mem_ker, LinearMap.lsmul_apply, map_zero] using congrArg f x.property

@[simp] theorem scalarKernelMap_apply (f : U →ₗ[A] V) (t : A) (x : ScalarKernel U t) :
    (scalarKernelMap f t x : V) = f x := rfl

/-- The linear map between cokernels of multiplication by `t` induced by `f`. -/
def scalarCokernelMap (f : U →ₗ[A] V) (t : A) :
    ScalarCokernel U t →ₗ[A] ScalarCokernel V t :=
  Submodule.mapQ _ _ f (by
    rintro x ⟨y, rfl⟩
    exact ⟨f y, (f.map_smul t y).symm⟩)

@[simp] theorem scalarCokernelMap_mk (f : U →ₗ[A] V) (t : A) (x : U) :
    scalarCokernelMap f t (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) := rfl

theorem scalarKernelMap_injective (f : U →ₗ[A] V) (hf : Function.Injective f) (t : A) :
    Function.Injective (scalarKernelMap f t) := by
  intro x y hxy
  apply Subtype.ext
  exact hf (congrArg Subtype.val hxy)

theorem scalarKernelMap_exact (f : U →ₗ[A] V) (g : V →ₗ[A] W)
    (hf : Function.Injective f) (hex : Function.Exact f g) (t : A) :
    Function.Exact (scalarKernelMap f t) (scalarKernelMap g t) := by
  intro x
  constructor
  · intro hx
    have hgx : g x = 0 := congrArg Subtype.val hx
    obtain ⟨y, hy⟩ := (hex x).mp hgx
    have hty : t • y = 0 := hf (by
      rw [f.map_smul, hy, map_zero]
      exact x.property)
    exact ⟨⟨y, hty⟩, Subtype.ext hy⟩
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    exact hex.apply_apply_eq_zero y

theorem scalarCokernelMap_surjective (g : V →ₗ[A] W)
    (hg : Function.Surjective g) (t : A) :
    Function.Surjective (scalarCokernelMap g t) := by
  intro x
  obtain ⟨w, rfl⟩ := (LinearMap.range (LinearMap.lsmul A W t)).mkQ_surjective x
  obtain ⟨v, rfl⟩ := hg w
  exact ⟨Submodule.Quotient.mk v, rfl⟩

theorem scalarCokernelMap_exact (f : U →ₗ[A] V) (g : V →ₗ[A] W)
    (hg : Function.Surjective g) (hex : Function.Exact f g) (t : A) :
    Function.Exact (scalarCokernelMap f t) (scalarCokernelMap g t) := by
  intro x
  induction x using Quotient.inductionOn' with
  | h v =>
    constructor
    · intro hx
      have hmem : g v ∈ LinearMap.range (LinearMap.lsmul A W t) :=
        (Submodule.Quotient.mk_eq_zero _).mp hx
      obtain ⟨w, hw⟩ := hmem
      obtain ⟨v', hv'⟩ := hg w
      have hzero : g (v - t • v') = 0 := by
        rw [map_sub, g.map_smul, hv']
        exact sub_eq_zero.mpr hw.symm
      obtain ⟨u, hu⟩ := (hex _).mp hzero
      refine ⟨Submodule.Quotient.mk u, ?_⟩
      change (Submodule.Quotient.mk (f u) : ScalarCokernel V t) = Submodule.Quotient.mk v
      apply (Submodule.Quotient.eq _).mpr
      refine ⟨-v', ?_⟩
      rw [hu, LinearMap.lsmul_apply, smul_neg]
      abel
    · rintro ⟨y, hy⟩
      rw [← hy]
      induction y using Quotient.inductionOn' with
      | h u =>
        change (Submodule.Quotient.mk (g (f u)) : ScalarCokernel W t) = 0
        rw [hex.apply_apply_eq_zero, Submodule.Quotient.mk_zero]

theorem scalarSquare (f : U →ₗ[A] V) (t : A) :
    f.comp (LinearMap.lsmul A U t) = (LinearMap.lsmul A V t).comp f := by
  ext x
  exact f.map_smul t x

/-- The connecting homomorphism for multiplication by t on a short exact
sequence of the actual modules, without regularity on the intermediate terms. -/
def principalConnecting (f : U →ₗ[A] V) (g : V →ₗ[A] W)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) (t : A) : ScalarKernel W t →ₗ[A] ScalarCokernel U t :=
  SnakeLemma.δ' (LinearMap.lsmul A U t) (LinearMap.lsmul A V t) (LinearMap.lsmul A W t)
    f g hex f g hex (scalarSquare f t) (scalarSquare g t)
    (ScalarKernel W t).subtype (LinearMap.exact_subtype_ker_map _)
    (LinearMap.range (LinearMap.lsmul A U t)).mkQ (LinearMap.exact_map_mkQ_range _)
    hg hf

theorem principalConnecting_exact_right (f : U →ₗ[A] V) (g : V →ₗ[A] W)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) (t : A) :
    Function.Exact (scalarKernelMap g t) (principalConnecting f g hf hg hex t) := by
  exact SnakeLemma.exact_δ'_right
    (LinearMap.lsmul A U t) (LinearMap.lsmul A V t) (LinearMap.lsmul A W t)
    f g hex f g hex (scalarSquare f t) (scalarSquare g t)
    (ScalarKernel V t).subtype (LinearMap.exact_subtype_ker_map _)
    (ScalarKernel W t).subtype (LinearMap.exact_subtype_ker_map _)
    (LinearMap.range (LinearMap.lsmul A U t)).mkQ (LinearMap.exact_map_mkQ_range _)
    hg hf (scalarKernelMap g t) (by ext x; rfl) (Submodule.subtype_injective _)

theorem principalConnecting_exact_left (f : U →ₗ[A] V) (g : V →ₗ[A] W)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) (t : A) :
    Function.Exact (principalConnecting f g hf hg hex t) (scalarCokernelMap f t) := by
  exact SnakeLemma.exact_δ'_left
    (LinearMap.lsmul A U t) (LinearMap.lsmul A V t) (LinearMap.lsmul A W t)
    f g hex f g hex (scalarSquare f t) (scalarSquare g t)
    (ScalarKernel W t).subtype (LinearMap.exact_subtype_ker_map _)
    (LinearMap.range (LinearMap.lsmul A U t)).mkQ (LinearMap.exact_map_mkQ_range _)
    (LinearMap.range (LinearMap.lsmul A V t)).mkQ (LinearMap.exact_map_mkQ_range _)
    hg hf (scalarCokernelMap f t) (by ext x; rfl) (Submodule.mkQ_surjective _)

/-- The linear equivalence between kernels of multiplication by `t` induced by `e`. -/
def scalarKernelEquiv (e : U ≃ₗ[A] V) (t : A) : ScalarKernel U t ≃ₗ[A] ScalarKernel V t :=
  LinearEquiv.ofLinearMap (scalarKernelMap e.toLinearMap t) (scalarKernelMap e.symm.toLinearMap t)
    (by ext x; exact e.apply_symm_apply x) (by ext x; exact e.symm_apply_apply x)

/-- The linear equivalence between cokernels of multiplication by `t` induced by `e`. -/
def scalarCokernelEquiv (e : U ≃ₗ[A] V) (t : A) :
    ScalarCokernel U t ≃ₗ[A] ScalarCokernel V t :=
  Submodule.Quotient.equiv _ _ e (by
    ext y
    constructor
    · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
      exact ⟨e u, (e.map_smul t u).symm⟩
    · rintro ⟨v, rfl⟩
      refine ⟨t • e.symm v, ⟨e.symm v, rfl⟩, ?_⟩
      change e (t • e.symm v) = t • v
      rw [e.map_smul, e.apply_symm_apply])

end Module
