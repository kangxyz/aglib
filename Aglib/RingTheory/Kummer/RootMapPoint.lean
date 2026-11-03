/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.RootMap
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Locality of the original coefficient-induced root map

The closed target ideal contracts to the closed coefficient ideal. The
native integral maximality theorem then makes its contraction to the
original source root algebra maximal. No domain or injectivity is needed.
-/

@[expose] public noncomputable section

namespace Algebra.Kummer

open IsLocalRing

/-- An actual local coefficient map induces a local map between the original
positive-order root algebras whenever those actual root algebras are local. -/
theorem rootMap_isLocalHom
    {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] [IsLocalRing B] [IsLocalRing C]
    (φ : B →ₐ[R] C) [IsLocalHom φ.toRingHom]
    (N : ℕ) (hN : 0 < N) (f : R)
    [IsLocalRing (RootAlgebra N (algebraMap R B f))]
    [IsLocalRing (RootAlgebra N (algebraMap R C f))] :
    IsLocalHom (rootMap φ N f).toRingHom := by
  let U := RootAlgebra N (algebraMap R B f)
  let V := RootAlgebra N (algebraMap R C f)
  let : Module.Finite B U := root_finite N hN _
  let : Module.Finite C V := root_finite N hN _
  let : IsLocalHom (algebraMap C V) :=
    ((local_hom_TFAE (algebraMap C V)).out 5 1).mp
      (eq_maximalIdeal (show ((maximalIdeal V).comap (algebraMap C V)).IsMaximal from
        inferInstance))
  let q : Ideal U := (maximalIdeal V).comap (rootMap φ N f).toRingHom
  have hq : q.under B = maximalIdeal B := by
    change ((maximalIdeal V).comap (rootMap φ N f).toRingHom).comap (algebraMap B U) = _
    rw [Ideal.comap_comap, rootMap_comp_algebraMap, ← Ideal.comap_comap,
      maximalIdeal_comap, maximalIdeal_comap]
  have hm : q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under
    (R := B) q (by rw [hq]; infer_instance)
  exact ((local_hom_TFAE (rootMap φ N f).toRingHom).out 5 1).mp (eq_maximalIdeal hm)

end Algebra.Kummer
