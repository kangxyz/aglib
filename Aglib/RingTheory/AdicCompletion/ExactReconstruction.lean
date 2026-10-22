/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.ExactPair
public import Aglib.RingTheory.AdicCompletion.Ext

/-!
# Reconstruction from an exact diagram

A finite original row and a complete target row identify the completion of
their original middle map. The proof uses actual completion maps and exact
images; it does not use faithful flatness of completion.
-/

@[expose] public noncomputable section

namespace AdicCompletion

universe u
variable {R K L M N C : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
  [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup C] [Module R C]
  [Module.Finite R L] [Module.Finite R N] [Module.Finite R C]
  [IsAdicComplete I K] [IsAdicComplete I M]

/-- In an exact reconstruction diagram, completing the original middle map
and identifying the complete target gives a bijection. The left term must be
complete; no completeness or faithful-completion assumption is made on `R`. -/
theorem completion_bijective_of_exact
    (i : K →ₗ[R] L) (p : L →ₗ[R] N) (k : K →ₗ[R] M)
    (f : M →ₗ[R] AdicCompletion I N) (c : AdicCompletion I N →ₗ[R] C)
    (a : L →ₗ[R] M)
    (hip : Function.Exact i p) (hpq : Function.Exact p (c.comp (of I N)))
    (hk : Function.Injective k) (hkf : Function.Exact k f)
    (hfc : Function.Exact f c)
    (hai : a.comp i = k) (hfa : f.comp a = (of I N).comp p) :
    Function.Bijective ((ofLinearEquiv I M).symm.toLinearMap.comp
      ((map I a).restrictScalars R)) := by
  let e : AdicCompletion I L →ₗ[R] M :=
    (ofLinearEquiv I M).symm.toLinearMap.comp ((map I a).restrictScalars R)
  have he (x : L) : e (of I L x) = a x := by
    change (ofLinearEquiv I M).symm (map I a (of I L x)) = a x
    rw [map_of, ofLinearEquiv_symm_of]
  have hfe : f.comp e = (map I p).restrictScalars R := by
    apply linearMap_ext_of I I.fg_of_isNoetherianRing
    intro x
    change f (e (of I L x)) = map I p (of I L x)
    rw [he, map_of]
    exact LinearMap.congr_fun hfa x
  have hc : (map I (c.comp (of I N))).restrictScalars R = (of I C).comp c := by
    apply linearMap_ext_of I I.fg_of_isNoetherianRing
    intro x
    change map I (c.comp (of I N)) (of I N x) = of I C (c (of I N x))
    rw [map_of]
    rfl
  have hex₁ := map_exact_pair I i p hip
  have hex₂ := map_exact_pair I p (c.comp (of I N)) hpq
  change Function.Bijective e
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hp : map I p x = 0 := by
      have h := LinearMap.congr_fun hfe x
      change f (e x) = map I p x at h
      rw [hx, _root_.map_zero] at h
      exact h.symm
    obtain ⟨y, rfl⟩ := (hex₁ x).mp hp
    obtain ⟨z, rfl⟩ := (of_bijective I K).surjective y
    rw [map_of] at hx ⊢
    have hkz : k z = 0 := by
      rw [he] at hx
      have hz : a (i z) = k z := LinearMap.congr_fun hai z
      rwa [hz] at hx
    have hz : z = 0 := hk (hkz.trans (_root_.map_zero k).symm)
    rw [hz, _root_.map_zero, _root_.map_zero]
  · intro m
    have hfcm : c (f m) = 0 := (hfc (f m)).mpr ⟨m, rfl⟩
    have hqm : map I (c.comp (of I N)) (f m) = 0 := by
      have h := LinearMap.congr_fun hc (f m)
      change map I (c.comp (of I N)) (f m) = of I C (c (f m)) at h
      simpa only [hfcm, _root_.map_zero] using h
    obtain ⟨x, hx⟩ := (hex₂ (f m)).mp hqm
    have hd : f (m - e x) = 0 := by
      have h := LinearMap.congr_fun hfe x
      change f (e x) = map I p x at h
      rw [map_sub, h, hx, sub_self]
    obtain ⟨z, hz⟩ := (hkf (m - e x)).mp hd
    refine ⟨x + of I L (i z), ?_⟩
    rw [map_add, he]
    have hleft : a (i z) = k z := LinearMap.congr_fun hai z
    rw [hleft, hz]
    rw [add_comm, sub_add_cancel]

end AdicCompletion
