/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Finiteness.Exact
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Ideal.Operations

/-!
# The algebraic pullback model for bounded-error reconstruction

The model is the native kernel of the difference of the two given maps.
Its projection retains the bounded kernel and cokernel defects. Finiteness
uses finiteness of the original kernel and a Noetherian target, not
finiteness of the completed source over the uncompleted ring.
-/

@[expose] public section

namespace LinearMap

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- The native kernel presenting the pullback of the original linear maps. -/
abbrev pullbackKernel (f : M →ₗ[R] P) (g : N →ₗ[R] P) :=
  (f.coprod (-g)).ker

/-- The original second-coordinate projection on the pullback kernel. -/
def pullbackKernelSnd (f : M →ₗ[R] P) (g : N →ₗ[R] P) :
    pullbackKernel f g →ₗ[R] N :=
  (snd R M N).comp (pullbackKernel f g).subtype

/-- The original kernel enters the pullback by the first coordinate. -/
def kerToPullbackKernel (f : M →ₗ[R] P) (g : N →ₗ[R] P) :
    f.ker →ₗ[R] pullbackKernel f g :=
  ((inl R M N).comp f.ker.subtype).codRestrict _ (by
    intro x
    change f x.val + -(g 0) = 0
    simpa only [map_zero, neg_zero, add_zero] using
      (show f x.val = 0 from x.property))

/-- The kernel of the pullback projection is the original kernel. -/
theorem kerToPullbackKernel_exact (f : M →ₗ[R] P) (g : N →ₗ[R] P) :
    Function.Exact (kerToPullbackKernel f g) (pullbackKernelSnd f g) := by
  intro x
  constructor
  · intro hx
    have hx0 : x.val.2 = 0 := hx
    have hxf : f x.val.1 = 0 := by
      have h := x.property
      change f x.val.1 + -(g x.val.2) = 0 at h
      simpa only [hx0, map_zero, neg_zero, add_zero] using h
    refine ⟨⟨x.val.1, hxf⟩, ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl hx0.symm
  · rintro ⟨y, rfl⟩
    rfl

/-- A finite kernel and Noetherian second factor give a finite pullback
model even when the first factor itself is not finite. -/
theorem finite_pullbackKernel (f : M →ₗ[R] P) (g : N →ₗ[R] P)
    [Module.Finite R f.ker] [IsNoetherian R N] :
    Module.Finite R (pullbackKernel f g) :=
  Module.Finite.of_exact_of_isNoetherian _ _ (kerToPullbackKernel_exact f g)

/-- An ideal annihilating the original kernel annihilates the actual kernel
of the pullback projection. -/
theorem smul_ker_pullbackKernelSnd_eq_bot (f : M →ₗ[R] P) (g : N →ₗ[R] P)
    (J : Ideal R) (hker : J • f.ker = ⊥) :
    J • (pullbackKernelSnd f g).ker = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.smul_le.mpr
  intro a ha x hx
  have hx0 : x.val.2 = 0 := hx
  have hxf : f x.val.1 = 0 := by
    have h := x.property
    change f x.val.1 + -(g x.val.2) = 0 at h
    simpa only [hx0, map_zero, neg_zero, add_zero] using h
  have hax : a • x.val.1 = 0 := by
    have hmem := Submodule.smul_mem_smul ha (show x.val.1 ∈ f.ker from hxf)
    rw [hker] at hmem
    exact hmem
  change a • x = 0
  apply Subtype.ext
  exact Prod.ext hax (by change a • x.val.2 = 0; rw [hx0, smul_zero])

/-- An ideal killing the original cokernel kills the pullback projection's
cokernel, without any surjectivity assumption on the second map. -/
theorem smul_top_le_range_pullbackKernelSnd (f : M →ₗ[R] P) (g : N →ₗ[R] P)
    (J : Ideal R) (hcoker : J • (⊤ : Submodule R P) ≤ f.range) :
    J • (⊤ : Submodule R N) ≤ (pullbackKernelSnd f g).range := by
  apply Submodule.smul_le.mpr
  intro a ha n _
  obtain ⟨m, hm⟩ := hcoker (Submodule.smul_mem_smul ha (Submodule.mem_top : g n ∈ ⊤))
  refine ⟨⟨(m, a • n), ?_⟩, rfl⟩
  change f m + -(g (a • n)) = 0
  rw [map_smul, hm, add_neg_cancel]

/-- The original first-coordinate projection, retained for the completion
comparison rather than replaced by an abstract isomorphism. -/
def pullbackKernelFst (f : M →ₗ[R] P) (g : N →ₗ[R] P) :
    pullbackKernel f g →ₗ[R] M :=
  (fst R M N).comp (pullbackKernel f g).subtype

/-- The pullback square commutes for its actual two coordinate projections. -/
theorem pullbackKernel_comm (f : M →ₗ[R] P) (g : N →ₗ[R] P) :
    f.comp (pullbackKernelFst f g) = g.comp (pullbackKernelSnd f g) := by
  ext x
  have h := x.property
  change f x.val.1 + -(g x.val.2) = 0 at h
  change f x.val.1 = g x.val.2
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using h)

variable {Q : Type*} [AddCommGroup Q] [Module R Q]

/-- A compatible pair of original maps has a canonical lift to the native
pullback kernel. -/
def liftPullbackKernel (f : M →ₗ[R] P) (g : N →ₗ[R] P)
    (a : Q →ₗ[R] M) (b : Q →ₗ[R] N) (h : f.comp a = g.comp b) :
    Q →ₗ[R] pullbackKernel f g :=
  (a.prod b).codRestrict _ (by
    intro x
    change f (a x) + -(g (b x)) = 0
    have hx : f (a x) = g (b x) := LinearMap.congr_fun h x
    rw [hx, add_neg_cancel])

@[simp]
theorem pullbackKernelFst_lift (f : M →ₗ[R] P) (g : N →ₗ[R] P)
    (a : Q →ₗ[R] M) (b : Q →ₗ[R] N) (h : f.comp a = g.comp b) :
    (pullbackKernelFst f g).comp (liftPullbackKernel f g a b h) = a := rfl

@[simp]
theorem pullbackKernelSnd_lift (f : M →ₗ[R] P) (g : N →ₗ[R] P)
    (a : Q →ₗ[R] M) (b : Q →ₗ[R] N) (h : f.comp a = g.comp b) :
    (pullbackKernelSnd f g).comp (liftPullbackKernel f g a b h) = b := rfl

/-- Uniqueness is for the original two projections, the equation needed to
identify restriction and gluing maps after proving reconstruction. -/
theorem pullbackKernel_hom_ext (f : M →ₗ[R] P) (g : N →ₗ[R] P)
    {a b : Q →ₗ[R] pullbackKernel f g}
    (hfst : (pullbackKernelFst f g).comp a = (pullbackKernelFst f g).comp b)
    (hsnd : (pullbackKernelSnd f g).comp a = (pullbackKernelSnd f g).comp b) :
    a = b := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact Prod.ext (LinearMap.congr_fun hfst x) (LinearMap.congr_fun hsnd x)

end LinearMap
