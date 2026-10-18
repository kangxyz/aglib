/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.FiniteExtension.Equiv

/-!
# Actual finite-extension towers with normal-prime lower step

The proved polynomial diamond and tower are consumed on the original finite
fields. Primitive presentations are transported by actual algebra equivalences;
no general tower compatibility is supplied as a premise.
-/

@[expose] public noncomputable section

namespace MilnorK

open Polynomial PolynomialResidue PolynomialNorm

variable {k : Type*} [Field k] [CharZero k]

local instance (p : MonicIrreducible k) : FiniteDimensional k (AdjoinRoot p.val) :=
  p.property.1.finite_adjoinRoot

local instance (p : MonicIrreducible k) : CharZero (AdjoinRoot p.val) :=
  charZero_of_injective_algebraMap (algebraMap k (AdjoinRoot p.val)).injective

/-- The actual finite norm tower when the lower field is the literal normal-prime
root field. All norms are the choice-independent original-field maps. -/
theorem finiteExtensionNorm_tower_prime_root
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (E : Type*) [Field E]
    [Algebra (AdjoinRoot p.val) E] [Algebra k E] [IsScalarTower k (AdjoinRoot p.val) E]
    [FiniteDimensional (AdjoinRoot p.val) E] (n : ℕ) (x : K E n) :
    letI : FiniteDimensional k E := FiniteDimensional.trans k (AdjoinRoot p.val) E
    finiteExtensionNorm k E n x =
      finiteExtensionNorm k (AdjoinRoot p.val) n
        (finiteExtensionNorm (AdjoinRoot p.val) E n x) := by
  let : FiniteDimensional k E := FiniteDimensional.trans k (AdjoinRoot p.val) E
  let h := finiteNormPolynomial k E
  let εh := finiteNormPresentation k E
  let f : AdjoinRoot p.val →ₐ[k] AdjoinRoot h.val :=
    εh.symm.toAlgHom.comp (IsScalarTower.toAlgHom k (AdjoinRoot p.val) E)
  let q := AdjoinRoot.towerBranch p.val h.val f
  let θ := AdjoinRoot.towerBranchRingEquiv p.val h.val f
  let εq : AdjoinRoot q.val.val ≃ₐ[AdjoinRoot p.val] E :=
    { θ.trans εh.toRingEquiv with
      commutes' := by
        intro a
        change εh (θ (algebraMap (AdjoinRoot p.val) _ a)) = _
        rw [AdjoinRoot.towerBranchRingEquiv_algebraMap]
        exact εh.apply_symm_apply _ }
  rw [finiteExtensionNorm_eq_presentation k E n h εh,
    finiteExtensionNorm_eq_presentation (AdjoinRoot p.val) E n q.val εq,
    finiteExtensionNorm_eq_presentation k (AdjoinRoot p.val) n p (AlgEquiv.refl)]
  simp only [LinearMap.comp_apply]
  have hid : (AlgEquiv.refl : AdjoinRoot p.val ≃ₐ[k] AdjoinRoot p.val).symm.toRingHom =
      RingHom.id (AdjoinRoot p.val) := rfl
  rw [hid, map_id, LinearMap.id_apply]
  change polynomialNorm n h (map n εh.symm.toRingHom x) =
    polynomialNorm n p (polynomialNorm n q.val (map n εq.symm.toRingHom x))
  rw [polynomialNorm_prime_tower p hp h f]
  apply congrArg (polynomialNorm n h)
  have he : θ.toRingHom.comp εq.symm.toRingHom = εh.symm.toRingHom := by
    apply RingHom.ext
    intro a
    change θ (θ.symm (εh.symm a)) = εh.symm a
    exact θ.apply_symm_apply _
  rw [← LinearMap.comp_apply (map n θ.toRingHom), ← map_comp, he]

/-- The actual finite-extension tower for an arbitrary normal-prime lower field,
not merely a polynomial root presentation. -/
theorem finiteExtensionNorm_tower_prime
    (L E : Type*) [Field L] [CharZero L] [Field E]
    [Algebra k L] [Algebra L E] [Algebra k E] [IsScalarTower k L E]
    [FiniteDimensional k L] [FiniteDimensional L E] [Normal k L]
    (hp : (Module.finrank k L).Prime) (n : ℕ) (x : K E n) :
    letI : FiniteDimensional k E := FiniteDimensional.trans k L E
    finiteExtensionNorm k E n x = finiteExtensionNorm k L n (finiteExtensionNorm L E n x) := by
  let : FiniteDimensional k E := FiniteDimensional.trans k L E
  let p := finiteNormPolynomial k L
  let ε := finiteNormPresentation k L
  let : Normal k (AdjoinRoot p.val) := Normal.of_algEquiv ε.symm
  have hdegree : p.val.natDegree = Module.finrank k L := by
    have h := ε.toLinearEquiv.finrank_eq
    rw [(AdjoinRoot.powerBasis p.property.2.ne_zero).finrank, AdjoinRoot.powerBasis_dim] at h
    exact h
  let : Algebra (AdjoinRoot p.val) E :=
    ((algebraMap L E).comp ε.toRingHom).toAlgebra
  let : IsScalarTower k (AdjoinRoot p.val) E := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro a
    change algebraMap k E a = algebraMap L E (ε (algebraMap k (AdjoinRoot p.val) a))
    rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply k L E])
  let : FiniteDimensional (AdjoinRoot p.val) E := FiniteDimensional.right k (AdjoinRoot p.val) E
  have hroot := finiteExtensionNorm_tower_prime_root p (hdegree ▸ hp) E n x
  have hbase := finiteExtensionNorm_equiv ε.toRingEquiv (RingEquiv.refl E)
    (show ∀ a : AdjoinRoot p.val,
      (RingEquiv.refl E) (algebraMap (AdjoinRoot p.val) E a) = algebraMap L E (ε a) from
      fun _ => rfl) n x
  change map n ε.toRingHom (finiteExtensionNorm (AdjoinRoot p.val) E n x) =
    finiteExtensionNorm L E n (map n (RingHom.id E) x) at hbase
  rw [map_id, LinearMap.id_apply] at hbase
  rw [hroot, ← finiteExtensionNorm_map_algEquiv ε n, hbase]

/-- The degree-one lower step follows from actual coefficient-isomorphism
naturality and the degree law, not from an assumed tower rule. -/
theorem finiteExtensionNorm_tower_degree_one
    (L E : Type*) [Field L] [CharZero L] [Field E]
    [Algebra k L] [Algebra L E] [Algebra k E] [IsScalarTower k L E]
    [FiniteDimensional k L] [FiniteDimensional L E] [FiniteDimensional k E]
    (hd : Module.finrank k L = 1) (n : ℕ) (x : K E n) :
    finiteExtensionNorm k E n x = finiteExtensionNorm k L n (finiteExtensionNorm L E n x) := by
  let φ : k ≃+* L := RingEquiv.ofBijective (algebraMap k L)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hd)
  have he := finiteExtensionNorm_equiv φ (RingEquiv.refl E)
    (fun a => IsScalarTower.algebraMap_apply k L E a) n x
  change map n (algebraMap k L) (finiteExtensionNorm k E n x) =
    finiteExtensionNorm L E n (map n (RingHom.id E) x) at he
  rw [map_id, LinearMap.id_apply] at he
  have h := congrArg (finiteExtensionNorm k L n) he
  rw [finiteExtensionNorm_map_constants, hd, Nat.cast_one, one_smul] at h
  exact h

end MilnorK
