/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.ReesAlgebra.Map

/-!
# Equivalences of the original Rees algebras

The existing coefficientwise Rees map is bijective for a ring equivalence.
The equivalence below promotes that same map; it introduces no second map
or realization of the Rees algebra.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v

namespace reesAlgebra

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- The existing coefficientwise Rees map is bijective for a ring equivalence. -/
theorem map_bijective (e : A ≃+* B) (I : Ideal A) :
    Function.Bijective (map e.toRingHom I) := by
  constructor
  · intro p q h
    apply Subtype.ext
    apply Polynomial.map_injective e.toRingHom e.injective
    exact congrArg (fun x : reesAlgebra (I.map e.toRingHom) => (x : Polynomial B)) h
  · intro q
    let p : Polynomial A := (q : Polynomial B).map e.symm.toRingHom
    have hp : p ∈ reesAlgebra I := by
      intro n
      have hq : (q : Polynomial B).coeff n ∈ (I ^ n).map e.toRingHom := by
        rw [Ideal.map_pow]
        exact q.property n
      obtain ⟨a, ha, he⟩ :=
        (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hq
      dsimp only [p]
      rw [Polynomial.coeff_map]
      change e.symm ((q : Polynomial B).coeff n) ∈ I ^ n
      rw [← he]
      change e.symm (e a) ∈ I ^ n
      rw [e.symm_apply_apply]
      exact ha
    refine ⟨⟨p, hp⟩, ?_⟩
    apply Subtype.ext
    change ((q : Polynomial B).map e.symm.toRingHom).map e.toRingHom = q
    have hcomp : e.toRingHom.comp e.symm.toRingHom = RingHom.id B := by
      ext b
      exact e.apply_symm_apply b
    rw [Polynomial.map_map, hcomp, Polynomial.map_id]

/-- Promote the existing original coefficientwise Rees map to an equivalence. -/
def mapEquiv (e : A ≃+* B) (I : Ideal A) :
    reesAlgebra I ≃+* reesAlgebra (I.map e.toRingHom) :=
  RingEquiv.ofBijective (map e.toRingHom I) (map_bijective e I)

/-- The promoted equivalence is still the original map on every Rees element. -/
theorem mapEquiv_apply (e : A ≃+* B) (I : Ideal A) (p : reesAlgebra I) :
    mapEquiv e I p = map e.toRingHom I p := rfl

/-- The underlying polynomial retains its literal original coefficient map. -/
theorem mapEquiv_coe (e : A ≃+* B) (I : Ideal A) (p : reesAlgebra I) :
    (mapEquiv e I p : Polynomial B) = (p : Polynomial A).map e.toRingHom := rfl

end reesAlgebra
