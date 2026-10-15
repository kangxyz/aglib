/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Descent.Basic

/-! From normalized tensor-overlap isomorphisms to effective algebra descent.
The two scalar embeddings are exchanged by the overlap map. The braid-shaped
equation below is the cocycle equation after identifying both overlap algebras
with `S tensor B`.

## Extraction basis

Transferred from `R5Lab.RingTheory.Descent.AlgebraOverlapDescent` at source revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`, SHA-256
`d61722f1d3d89f489177dc1396698d417334f5e00c9f9b73575150ba5806b93a`.
The source interface retains its objects, maps and assumptions under native
mathematical declaration namespaces. The scalar-exchange helper
`OverlapDatum.swap_one_tmul` omits the source section instances `[Algebra S B]`
and `[IsScalarTower R S B]`, unused by both its type and proof.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.TensorProduct

namespace Algebra.Descent

universe u v w
variable (R : Type u) (S : Type v) (B : Type w)
variable [CommRing R] [CommRing S] [CommRing B]
variable [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]

/-- Overlap data with explicit scalar compatibility, diagonal identity, and
the cocycle on the triple tensor product. No descended object is a field. -/
structure OverlapDatum where
  /-- The R-algebra equivalence on S ⊗[R] B that exchanges the two scalar actions. -/
  overlap : S ⊗[R] B ≃ₐ[R] S ⊗[R] B
  scalar_left (s : S) : overlap (s ⊗ₜ[R] (1 : B)) = 1 ⊗ₜ[R] algebraMap S B s
  scalar_right (s : S) : overlap (1 ⊗ₜ[R] algebraMap S B s) = s ⊗ₜ[R] (1 : B)
  diagonal : ((counit R S B).restrictScalars R).comp overlap.toAlgHom =
    (counit R S B).restrictScalars R
  cocycle :
    (Algebra.TensorProduct.leftComm R S S B).toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id R S) overlap.toAlgHom).comp
        (Algebra.TensorProduct.leftComm R S S B).toAlgHom) =
    (Algebra.TensorProduct.map (AlgHom.id R S) overlap.toAlgHom).comp
      ((Algebra.TensorProduct.leftComm R S S B).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id R S) overlap.toAlgHom))

variable {R S B}
namespace OverlapDatum
variable (D : OverlapDatum R S B)

/-- Evaluation of the overlap isomorphism on the second tensor embedding. -/
def coaction : B →ₐ[S] S ⊗[R] B :=
  { (D.overlap.toAlgHom.comp Algebra.TensorProduct.includeRight).toRingHom with
    commutes' := fun s => D.scalar_right s }

@[simp] lemma coaction_apply (b : B) : D.coaction b = D.overlap (1 ⊗ₜ[R] b) := rfl

omit [Algebra S B] [IsScalarTower R S B] in
lemma swap_one_tmul (z : S ⊗[R] B) :
    Algebra.TensorProduct.leftComm R S S B (1 ⊗ₜ[R] z) =
      Algebra.TensorProduct.map (AlgHom.id S S)
        (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B) z := by
  induction z using _root_.TensorProduct.inductionOn with
  | tmul s b => simp
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

lemma overlap_swap_one_tmul (z : S ⊗[R] B) :
    Algebra.TensorProduct.map (AlgHom.id R S) D.overlap.toAlgHom
      (Algebra.TensorProduct.leftComm R S S B (1 ⊗ₜ[R] z)) =
      Algebra.TensorProduct.map (AlgHom.id S S) (D.coaction.restrictScalars R) z := by
  induction z using _root_.TensorProduct.inductionOn with
  | tmul s b => simp
  | add x y hx hy => simp only [tmul_add, map_add, hx, hy]

/-- The overlap equations prove the coaction equations required by the
explicit equalizer reconstruction. -/
def toDatum : Datum R S B where
  coaction := D.coaction
  counit_coaction := by
    ext b
    have h := congrArg (fun f : S ⊗[R] B →ₐ[R] B => f (1 ⊗ₜ[R] b)) D.diagonal
    simpa using h
  coassoc := by
    ext b
    have h := congrArg (fun f : S ⊗[R] (S ⊗[R] B) →ₐ[R] S ⊗[R] (S ⊗[R] B) =>
      f (1 ⊗ₜ[R] (1 ⊗ₜ[R] b))) D.cocycle
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      Algebra.TensorProduct.leftComm_tmul, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply] at h
    rw [D.overlap_swap_one_tmul, swap_one_tmul] at h
    exact h.symm

lemma overlap_tmul (s : S) (b : B) :
    D.overlap (s ⊗ₜ[R] b) = (1 ⊗ₜ[R] algebraMap S B s) * D.coaction b := by
  rw [show s ⊗ₜ[R] b = (s ⊗ₜ[R] (1 : B)) * (1 ⊗ₜ[R] b) by simp,
    map_mul, D.scalar_left]
  rfl

/-- On an invariant element, the recovered overlap identification is the
canonical scalar exchange. This verifies compatibility of the reconstruction. -/
lemma overlap_tmul_invariant (s : S) (a : D.toDatum.invariants) :
    D.overlap (s ⊗ₜ[R] (a : B)) = 1 ⊗ₜ[R] (s • (a : B)) := by
  rw [D.overlap_tmul]
  have ha : D.coaction a = 1 ⊗ₜ[R] (a : B) := a.property
  rw [ha]
  simp [Algebra.smul_def]

end OverlapDatum
end Algebra.Descent
