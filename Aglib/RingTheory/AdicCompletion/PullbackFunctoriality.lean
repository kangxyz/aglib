/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.BoundedPullback

/-!
# Functoriality of the native module pullback

Maps can vary both factors and the common target. Projection equations,
identity and composition retain the original maps used in reconstruction.
-/

@[expose] public section

namespace LinearMap

variable {R M N P M' N' P' M'' N'' P'' : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P] [AddCommGroup M'] [Module R M']
  [AddCommGroup N'] [Module R N'] [AddCommGroup P'] [Module R P']
  [AddCommGroup M''] [Module R M''] [AddCommGroup N''] [Module R N'']
  [AddCommGroup P''] [Module R P'']

/-- The map of native pullbacks induced by the original three-map diagram. -/
def mapPullbackKernel (f : M →ₗ[R] P) (g : N →ₗ[R] P)
    (f' : M' →ₗ[R] P') (g' : N' →ₗ[R] P')
    (a : M →ₗ[R] M') (b : N →ₗ[R] N') (c : P →ₗ[R] P')
    (hf : f'.comp a = c.comp f) (hg : g'.comp b = c.comp g) :
    pullbackKernel f g →ₗ[R] pullbackKernel f' g' :=
  liftPullbackKernel f' g' (a.comp (pullbackKernelFst f g))
    (b.comp (pullbackKernelSnd f g)) (by
      apply LinearMap.ext
      intro x
      have hfx : f' (a x.val.1) = c (f x.val.1) := LinearMap.congr_fun hf x.val.1
      have hgx : g' (b x.val.2) = c (g x.val.2) := LinearMap.congr_fun hg x.val.2
      have hxy : f x.val.1 = g x.val.2 :=
        LinearMap.congr_fun (pullbackKernel_comm f g) x
      change f' (a x.val.1) = g' (b x.val.2)
      rw [hfx, hgx, hxy])

@[simp]
theorem mapPullbackKernel_fst (f : M →ₗ[R] P) (g : N →ₗ[R] P)
    (f' : M' →ₗ[R] P') (g' : N' →ₗ[R] P')
    (a : M →ₗ[R] M') (b : N →ₗ[R] N') (c : P →ₗ[R] P')
    (hf : f'.comp a = c.comp f) (hg : g'.comp b = c.comp g)
    (x : pullbackKernel f g) :
    (mapPullbackKernel f g f' g' a b c hf hg x).val.1 = a x.val.1 := rfl

@[simp]
theorem mapPullbackKernel_snd (f : M →ₗ[R] P) (g : N →ₗ[R] P)
    (f' : M' →ₗ[R] P') (g' : N' →ₗ[R] P')
    (a : M →ₗ[R] M') (b : N →ₗ[R] N') (c : P →ₗ[R] P')
    (hf : f'.comp a = c.comp f) (hg : g'.comp b = c.comp g)
    (x : pullbackKernel f g) :
    (mapPullbackKernel f g f' g' a b c hf hg x).val.2 = b x.val.2 := rfl

@[simp]
theorem mapPullbackKernel_id (f : M →ₗ[R] P) (g : N →ₗ[R] P) :
    mapPullbackKernel f g f g LinearMap.id LinearMap.id LinearMap.id
      (by rfl) (by rfl) = LinearMap.id := by
  apply pullbackKernel_hom_ext f g <;> rfl

/-- Composition is determined by the two original factor maps, independently
of the proofs of the commutative squares. -/
theorem mapPullbackKernel_comp (f : M →ₗ[R] P) (g : N →ₗ[R] P)
    (f' : M' →ₗ[R] P') (g' : N' →ₗ[R] P')
    (f'' : M'' →ₗ[R] P'') (g'' : N'' →ₗ[R] P'')
    (a : M →ₗ[R] M') (b : N →ₗ[R] N') (c : P →ₗ[R] P')
    (a' : M' →ₗ[R] M'') (b' : N' →ₗ[R] N'') (c' : P' →ₗ[R] P'')
    (hf : f'.comp a = c.comp f) (hg : g'.comp b = c.comp g)
    (hf' : f''.comp a' = c'.comp f') (hg' : g''.comp b' = c'.comp g')
    (hf'' : f''.comp (a'.comp a) = (c'.comp c).comp f)
    (hg'' : g''.comp (b'.comp b) = (c'.comp c).comp g) :
    (mapPullbackKernel f' g' f'' g'' a' b' c' hf' hg').comp
      (mapPullbackKernel f g f' g' a b c hf hg) =
    mapPullbackKernel f g f'' g'' (a'.comp a) (b'.comp b) (c'.comp c) hf'' hg'' := by
  apply pullbackKernel_hom_ext f'' g'' <;> rfl

/-- Change the first factor by a specified equivalence, keeping the original
second factor and common target fixed. -/
def pullbackKernelCongrFst (f : M →ₗ[R] P) (f' : M' →ₗ[R] P) (g : N →ₗ[R] P)
    (e : M ≃ₗ[R] M') (h : f'.comp e.toLinearMap = f) :
    pullbackKernel f g ≃ₗ[R] pullbackKernel f' g where
  toFun x := ⟨(e x.val.1, x.val.2), by
    change f' (e x.val.1) + -(g x.val.2) = 0
    have he : f' (e x.val.1) = f x.val.1 := LinearMap.congr_fun h x.val.1
    rw [he]
    exact x.property⟩
  invFun y := ⟨(e.symm y.val.1, y.val.2), by
    change f (e.symm y.val.1) + -(g y.val.2) = 0
    have he : f' y.val.1 = f (e.symm y.val.1) := by
      have hh := LinearMap.congr_fun h (e.symm y.val.1)
      simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] using hh
    rw [← he]
    exact y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext (e.symm_apply_apply _) rfl
  right_inv y := by
    apply Subtype.ext
    exact Prod.ext (e.apply_symm_apply _) rfl
  map_add' x y := by
    apply Subtype.ext
    exact Prod.ext (map_add e _ _) rfl
  map_smul' r x := by
    apply Subtype.ext
    exact Prod.ext (e.map_smul r _) rfl

end LinearMap
