/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.Uniformizer
public import Aglib.RingTheory.DiscreteValuationRing.SameUniformizer
public import Aglib.RingTheory.LocalRing.FiniteResidueSurjective

/-!
# Recognition of the original uniformizer-root algebra

An actual uniformizer root in a finite extension of DVRs with unchanged
residue field identifies the literal root algebra with that same extension.
The map sends the original adjoined root to the specified uniformizer.
Injectivity comes from preservation of a uniformizer; surjectivity is native
Nakayama. No field-degree equality is assumed.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

namespace Algebra.Kummer

universe u v

variable (R : Type u) (S : Type v)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
  (π : R) (hπ : Irreducible π) (n : ℕ) (hn : 0 < n)
  (t : S) (ht : Irreducible t) (hpow : t ^ n = algebraMap R S π)
  (hκ : Function.Surjective (algebraMap (ResidueField R) (ResidueField S)))

/-- The actual root-evaluation map is an isomorphism onto the same finite DVR
extension when its root is a uniformizer and the residue map is surjective. -/
def uniformizerRootEquiv : RootAlgebra n π ≃ₐ[R] S := by
  let D := RootAlgebra n π
  let θ : D := AdjoinRoot.root (rootPolynomial n π)
  let φ : D →ₐ[R] S := AdjoinRoot.liftAlgHom (rootPolynomial n π)
    (Algebra.ofId R S) t (by simp [rootPolynomial, hpow])
  have hφ : φ θ = t := AdjoinRoot.liftAlgHom_root _ _ _ _
  let := uniformizerRoot_isDomain R π hπ n hn
  let := uniformizerRoot_isDiscreteValuationRing R π hπ n hn
  have hθ : Irreducible θ := uniformizerRoot_irreducible R π hπ n hn
  have hφθ : Irreducible (φ θ) := hφ.symm ▸ ht
  have hinj : Function.Injective φ :=
    IsDiscreteValuationRing.injective_of_map_irreducible φ.toRingHom hθ hφθ
  let : Algebra D S := φ.toRingHom.toAlgebra
  let : IsScalarTower R D S := IsScalarTower.of_algHom φ
  let : Module.Finite D S := Module.Finite.of_restrictScalars_finite R D S
  let : IsLocalHom (algebraMap D S) :=
    IsDiscreteValuationRing.isLocalHom_of_map_irreducible φ.toRingHom hθ hφθ
  have hm : (maximalIdeal D).map (algebraMap D S) = maximalIdeal S :=
    IsDiscreteValuationRing.map_maximalIdeal_of_map_irreducible φ.toRingHom hθ hφθ
  have hres : Function.Surjective
      (algebraMap (ResidueField D) (ResidueField S)) := by
    intro x
    obtain ⟨a, ha⟩ := hκ x
    obtain ⟨a, rfl⟩ := residue_surjective a
    refine ⟨residue D (algebraMap R D a), ?_⟩
    rw [ResidueField.algebraMap_residue, ← IsScalarTower.algebraMap_apply]
    exact ha
  exact AlgEquiv.ofBijective φ ⟨hinj,
    surjective_algebraMap_of_map_maximalIdeal_of_residue D S hm hres⟩

/-- The assembled algebra isomorphism retains the specified original root value. -/
theorem uniformizerRootEquiv_root :
    uniformizerRootEquiv R S π hπ n hn t ht hpow hκ
      (AdjoinRoot.root (rootPolynomial n π)) = t :=
  AdjoinRoot.liftAlgHom_root (rootPolynomial n π) (Algebra.ofId R S) t
    (by simp [rootPolynomial, hpow])

include hπ hn ht hpow hκ in
/-- The original finite extension has exactly the root-algebra rank, as a
consequence of the actual isomorphism rather than an input to it. -/
theorem finrank_eq_of_uniformizer_root : Module.finrank R S = n := by
  rw [← (uniformizerRootEquiv R S π hπ n hn t ht hpow hκ).toLinearEquiv.finrank_eq]
  exact uniformizerRoot_finrank R π n hn

end Algebra.Kummer
