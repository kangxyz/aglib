/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.RootsOfUnity.FieldPullback

/-!
# Independence of the algebraic-closure embedding in field pullback

Every pair of compatible embeddings of algebraic closures differs by an actual
base-field automorphism of the source closure. This is constructed by normal
restriction, rather than assumed. The resulting Galois restrictions are
conjugate and the maps on actual roots of unity intertwine by the same
conjugator. Their induced maps on the genuine continuous first cohomology of
`μₙ ⊗ℤ μₙ` agree because the cocycle difference is explicitly principal.

No naturality of a motivic Bockstein or comparison map is an input here.
-/

@[expose] public section

noncomputable section

namespace Field.absoluteGaloisGroup.RootsOfUnity.FieldPullbackIndependence

open Field.absoluteGaloisGroup.RootsOfUnity
open scoped TensorProduct

universe u v w

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- A compatible embedding of the fixed algebraic closures. -/
abbrev Embedding := AlgebraicClosure K →ₐ[K] AlgebraicClosure L

/-- The genuine continuous restriction homomorphism for this explicit embedding. -/
def restriction (i : Embedding (K := K) (L := L)) :
    Field.absoluteGaloisGroup L →ₜ* Field.absoluteGaloisGroup K :=
  letI := i.toAlgebra
  Field.absoluteGaloisGroup.mapOfAlgebra K L

theorem restriction_commutes (i : Embedding (K := K) (L := L))
    (g : Field.absoluteGaloisGroup L) (x : AlgebraicClosure K) :
    i ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from restriction i g) x) =
      (show AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L from g) (i x) := by
  let := i.toAlgebra
  exact FieldPullback.restriction_commutes K L g x

/-- The actual source-closure automorphism comparing two embeddings. Normality
ensures the second embedding maps into the image of the first. -/
def conjugator (i j : Embedding (K := K) (L := L)) : Field.absoluteGaloisGroup K :=
  letI := i.toAlgebra
  j.restrictNormal' (AlgebraicClosure K)

/-- Thus arbitrary compatible embeddings, without additional hypotheses, differ
by this automorphism of the algebraic closure. -/
theorem conjugator_commutes (i j : Embedding (K := K) (L := L)) (x : AlgebraicClosure K) :
    i ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from conjugator i j) x) = j x := by
  let := i.toAlgebra
  exact j.restrictNormal_commutes (AlgebraicClosure K) x

/-- The two actual restriction maps intertwine with the constructed conjugator. -/
theorem restriction_intertwine (i j : Embedding (K := K) (L := L))
    (g : Field.absoluteGaloisGroup L) :
    conjugator i j * restriction j g = restriction i g * conjugator i j := by
  apply AlgEquiv.ext
  intro x
  apply i.injective
  change i ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from conjugator i j)
      ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from restriction j g) x)) =
    i ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from restriction i g)
      ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from conjugator i j) x))
  rw [conjugator_commutes, restriction_commutes, restriction_commutes, conjugator_commutes]

/-- The actual continuous Galois restrictions are related by inner conjugacy. -/
theorem restriction_conjugate (i j : Embedding (K := K) (L := L))
    (g : Field.absoluteGaloisGroup L) :
    restriction j g = (conjugator i j)⁻¹ * restriction i g * conjugator i j := by
  have h := congrArg (fun a => (conjugator i j)⁻¹ * a) (restriction_intertwine i j g)
  simpa only [← mul_assoc, inv_mul_cancel, one_mul] using h

/-- The actual root-of-unity map for the explicitly selected closure embedding. -/
def muMap (i : Embedding (K := K) (L := L)) (n : ℕ) : Mu K n →ₗ[ℤ] Mu L n :=
  letI := i.toAlgebra
  FieldPullback.muMap K L n

@[simp] theorem muMap_value (i : Embedding (K := K) (L := L)) (n : ℕ) (x : Mu K n) :
    (((muMap i n x).toMul : (AlgebraicClosure L)ˣ) : AlgebraicClosure L) =
      i ((x.toMul : (AlgebraicClosure K)ˣ) : AlgebraicClosure K) := rfl

/-- The two root maps differ by the same actual Galois action. -/
theorem muMap_conjugator (i j : Embedding (K := K) (L := L)) (n : ℕ) (x : Mu K n) :
    muMap j n x = muMap i n (conjugator i j • x) := by
  ext
  exact (conjugator_commutes i j
    ((x.toMul : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)).symm

section ExistingTower
variable [Algebra (AlgebraicClosure K) (AlgebraicClosure L)]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure L)]
/-- Recover the explicit closure embedding from any existing compatible tower. -/
def towerEmbedding : Embedding (K := K) (L := L) :=
  IsScalarTower.toAlgHom K (AlgebraicClosure K) (AlgebraicClosure L)

/-- The explicit-embedding restriction agrees with the pre-existing tower API. -/
theorem restriction_tower : restriction (towerEmbedding (K := K) (L := L)) =
    Field.absoluteGaloisGroup.mapOfAlgebra K L := by
  apply ContinuousMonoidHom.ext
  intro g
  apply AlgEquiv.ext
  intro x
  apply (algebraMap (AlgebraicClosure K) (AlgebraicClosure L)).injective
  exact (restriction_commutes (towerEmbedding (K := K) (L := L)) g x).trans
    (FieldPullback.restriction_commutes K L g x).symm

end ExistingTower
section Composition
variable {M : Type w} [Field M] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
/-- Compose actual compatible algebraic-closure embeddings. -/
def embeddingComp (j : Embedding (K := L) (L := M))
    (i : Embedding (K := K) (L := L)) : Embedding (K := K) (L := M) :=
  (j.restrictScalars K).comp i

/-- Restriction through two actual closure embeddings is their composite
continuous Galois restriction. -/
theorem restriction_comp (j : Embedding (K := L) (L := M))
    (i : Embedding (K := K) (L := L)) :
    restriction (embeddingComp j i) = (restriction i).comp (restriction j) := by
  apply ContinuousMonoidHom.ext
  intro g
  apply AlgEquiv.ext
  intro x
  apply (embeddingComp j i).injective
  change (embeddingComp j i)
      ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from
        restriction (embeddingComp j i) g) x) =
    j (i ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from
      restriction i (restriction j g)) x))
  rw [restriction_commutes]
  change (show AlgebraicClosure M ≃ₐ[M] AlgebraicClosure M from g) (j (i x)) =
    j (i ((show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from
      restriction i (restriction j g)) x))
  rw [restriction_commutes, restriction_commutes]

/-- Composition of actual root maps. -/
theorem muMap_comp (j : Embedding (K := L) (L := M))
    (i : Embedding (K := K) (L := L)) (n : ℕ) (x : Mu K n) :
    muMap (embeddingComp j i) n x = muMap j n (muMap i n x) := rfl

end Composition
/-- The identity closure embedding induces the identity restriction. -/
theorem restriction_id :
    restriction (AlgHom.id K (AlgebraicClosure K)) =
      ContinuousMonoidHom.id (Field.absoluteGaloisGroup K) := by
  apply ContinuousMonoidHom.ext
  intro g
  apply AlgEquiv.ext
  intro x
  exact restriction_commutes (AlgHom.id K (AlgebraicClosure K)) g x

end Field.absoluteGaloisGroup.RootsOfUnity.FieldPullbackIndependence
