/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.PicardGroup

/-!
# Invertible principal ideals

A generator of a principal ideal that is an invertible module is regular
(`Ideal.isSMulRegular_of_invertible_span_singleton`): the surjection `S → (c)`, `r ↦ r c`, is a
surjective map onto an invertible module, hence bijective
(`Module.Invertible.bijective_of_surjective`). This complements
`Ideal.ideal_exists_regular_generator` in `Aglib.RingTheory.Ideal.RegularPrincipal`, which
starts from a rank-one presentation of the ideal. No Noetherian or domain hypothesis is used.
-/

@[expose] public section

namespace Ideal

universe u

/-- A generator of a principal ideal which is an invertible module is regular. -/
theorem isSMulRegular_of_invertible_span_singleton {S : Type u} [CommRing S] (c : S)
    [Module.Invertible S (Ideal.span {c})] : IsSMulRegular S c := by
  let f : S →ₗ[S] Ideal.span {c} :=
    LinearMap.toSpanSingleton S _ ⟨c, Ideal.mem_span_singleton_self c⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    exact ⟨r, Subtype.ext (by simp [f])⟩
  have hinj := (Module.Invertible.bijective_of_surjective hf).injective
  intro x y hxy
  apply hinj
  apply Subtype.ext
  simpa [f, mul_comm] using hxy

end Ideal
