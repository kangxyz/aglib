/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Descent.Basic

/-! Recovery of an algebra from the canonical descent datum on its base change.

## Extraction basis

Transferred from `R5Lab.RingTheory.Descent.AlgebraDescentCanonical` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`4b82b0e617b914b79b77bcf51724e7ec8e489cb8f65511e562f0ceeef565c804`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.TensorProduct

namespace Algebra.Descent

universe u v w
variable (R : Type u) (S : Type v) (A : Type w)
variable [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]

/-- The canonical descent datum on a base-changed algebra inserts a unit in
the middle tensor factor. -/
def canonicalDatum : Datum R S (S ⊗[R] A) where
  coaction := Algebra.TensorProduct.map (AlgHom.id S S)
    (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A)
  counit_coaction := by
    ext a
    simp [counit]
  coassoc := by
    ext a
    simp

/-- The base algebra maps into the actual invariants by `a` to `1 tensor a`. -/
def toCanonicalInvariants : A →ₐ[R] (canonicalDatum R S A).invariants :=
  (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).codRestrict _ (fun a => by
    change Algebra.TensorProduct.map (AlgHom.id S S)
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) (1 ⊗ₜ[R] a) =
        1 ⊗ₜ[R] (1 ⊗ₜ[R] a)
    simp)

@[simp] lemma toCanonicalInvariants_apply (a : A) :
    (toCanonicalInvariants R S A a : S ⊗[R] A) = 1 ⊗ₜ[R] a := rfl

lemma baseChange_toCanonicalInvariants :
    (canonicalDatum R S A).baseChange.comp
      (Algebra.TensorProduct.map (AlgHom.id S S) (toCanonicalInvariants R S A)) =
        AlgHom.id S (S ⊗[R] A) := by
  ext a
  simp

/-- Faithful flatness proves that taking canonical invariants recovers every
base algebra, rather than merely constructing an effective object above S. -/
lemma toCanonicalInvariants_bijective [Module.FaithfullyFlat R S] :
    Function.Bijective (toCanonicalInvariants R S A) := by
  apply (Module.FaithfullyFlat.lTensor_bijective_iff_bijective R S
    (toCanonicalInvariants R S A).toLinearMap).1
  let g := Algebra.TensorProduct.map (AlgHom.id S S) (toCanonicalInvariants R S A)
  let f := (canonicalDatum R S A).baseChange
  have h : ∀ z, f (g z) = z := fun z =>
    congrArg (fun k : S ⊗[R] A →ₐ[S] S ⊗[R] A => k z)
      (baseChange_toCanonicalInvariants R S A)
  change Function.Bijective g
  constructor
  · intro x y hxy
    rw [← h x, ← h y, hxy]
  · intro z
    refine ⟨f z, ?_⟩
    apply (canonicalDatum R S A).baseChange_injective
    exact h (f z)

/-- The canonical equalizer is isomorphic to the original algebra. -/
def canonicalInvariantsEquiv [Module.FaithfullyFlat R S] :
    A ≃ₐ[R] (canonicalDatum R S A).invariants :=
  AlgEquiv.ofBijective (toCanonicalInvariants R S A) (toCanonicalInvariants_bijective R S A)

end Algebra.Descent
