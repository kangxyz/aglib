/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.Equiv
public import Aglib.KTheory.MilnorK.InfinityResidue

/-!
# The actual finite-extension norm after inversion of the base parameter

The upper field is unchanged. Only its rational-function algebra structure is
pulled back by inversion, so this applies to arbitrary finite extensions, not
just constant extensions.
-/

@[expose] public noncomputable section
namespace MilnorK

open Polynomial PolynomialResidue

variable (k E : Type*) [Field k] [CharZero k] [Field E]
  [Algebra (RatFunc k) E] [FiniteDimensional (RatFunc k) E]

/-- The original upper field with scalar action pulled back by inversion. -/
@[instance_reducible]
def infinityTwistAlgebra : Algebra (RatFunc k) E :=
  ((algebraMap (RatFunc k) E).comp (RatFunc.inversion k).toRingHom).toAlgebra

omit [CharZero k] in
/-- Inversion does not change finiteness of the extension. -/
theorem infinityTwistFinite :
    @FiniteDimensional (RatFunc k) E _ _ (infinityTwistAlgebra k E).toModule := by
  exact RingHom.Finite.comp
    (show (algebraMap (RatFunc k) E).Finite from by
      simpa only [RingHom.finite_algebraMap] using
        (inferInstance : Module.Finite (RatFunc k) E))
    (RingHom.Finite.of_surjective (RatFunc.inversion k).toRingHom
      (RatFunc.inversion k).surjective)

/-- The actual norm for the inverted scalar action, on the original Milnor group. -/
def infinityTwistNorm (n : ℕ) : K E n →ₗ[ℤ] K (RatFunc k) n :=
  let fin := infinityTwistFinite k E
  letI := infinityTwistAlgebra k E
  letI := fin
  finiteExtensionNorm (RatFunc k) E n

/-- Inverting the scalar action inverts the output of the original norm. -/
theorem infinityTwistNorm_eq (n : ℕ) (x : K E n) :
    infinityTwistNorm k E n x =
      map n (RatFunc.inversion k).toRingHom (finiteExtensionNorm (RatFunc k) E n x) := by
  have h := @finiteExtensionNorm_equiv (RatFunc k) (RatFunc k) _ _ E E _ _
    (inferInstance : Algebra (RatFunc k) E) (infinityTwistAlgebra k E)
    _ _ (inferInstance : FiniteDimensional (RatFunc k) E) (infinityTwistFinite k E)
    (RatFunc.inversion k).toRingEquiv (RingEquiv.refl E)
    (fun a => by
      change algebraMap (RatFunc k) E a =
        algebraMap (RatFunc k) E (RatFunc.inversion k (RatFunc.inversion k a))
      rw [RatFunc.inversion_inversion]) n x
  change map n (RatFunc.inversion k).toRingHom
    (finiteExtensionNorm (RatFunc k) E n x) =
    infinityTwistNorm k E n (map n (RingHom.id E) x) at h
  rw [map_id, LinearMap.id_apply] at h
  exact h.symm

local instance : Fact (Irreducible (X : k[X])) := ⟨irreducible_X⟩

/-- Infinity of the original norm is the finite `X` residue of the twisted norm. -/
theorem infinityResidue_finiteExtensionNorm_eq_twist (n : ℕ) (x : K E (n + 1)) :
    InfinityResidue.residue k n (finiteExtensionNorm (RatFunc k) E (n + 1) x) =
      map n (InfinityResidue.rootXEquiv k).toRingHom
        (residueAt (X : k[X]) n (infinityTwistNorm k E (n + 1) x)) := by
  rw [infinityTwistNorm_eq]
  rfl

end MilnorK
