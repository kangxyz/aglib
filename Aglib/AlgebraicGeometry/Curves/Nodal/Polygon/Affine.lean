/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Galois.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.LinearCombination
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.Topology.Sober
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.RingTheory.Localization.Pi
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.Adjoin.Tower
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.Topology.DenseEmbedding
public import Aglib.Algebra.Polynomial.Eval.LinearInterpolation
public import Aglib.Data.Fin.Rotate
public import Aglib.AlgebraicGeometry.Curves.Nodal.Gluing

/-!
# The unmarked polygon curve: Affine

Source: frozen R5 `Curves/Cyclic/Affine.lean`, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`.
The actual ring maps, gluing arrows and component indices are retained.
This leaf does not construct a marked model or assume a model-existence theorem.
-/

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
universe u

section
/-! Actual affine cyclic pinching. No unformalized premise is used. -/
noncomputable section
open Polynomial
open scoped Polynomial TensorProduct

namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k] (n : ℕ)

/-- The product of the polynomial coordinate rings of the `n` normalization components. -/
abbrev NormalizationRing := Fin n → k[X]
/-- The product of the two endpoint fields for each normalization component. -/
abbrev BoundaryRing := Fin n → k × k
/-- The algebra of field-valued functions on the `n` node labels. -/
abbrev NodeValues := Fin n → k

/-- Evaluation at `a` on every polynomial normalization component. -/
def endpoint (a : k) : NormalizationRing k n →ₐ[k] NodeValues k n where
  toFun p i := (p i).eval a
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' := by intros; ext; simp
  map_mul' := by intros; ext; simp
  commutes' := by intros; ext; simp

/-- Evaluation at zero on the cyclic successor of each normalization component. -/
def nextEndpoint : NormalizationRing k n →ₐ[k] NodeValues k n where
  toFun p i := (p (finRotate n i)).eval 0
  map_zero' := by ext; simp
  map_one' := by ext; simp
  map_add' := by intros; ext; simp
  map_mul' := by intros; ext; simp
  commutes' := by intros; ext; simp

/-- The cyclic node equations, valid also for the one-gon loop. -/
def nodeRing : Subalgebra k (NormalizationRing k n) :=
  (endpoint k n 1).equalizer (nextEndpoint k n)

@[simp] theorem mem_nodeRing (p : NormalizationRing k n) :
    p ∈ nodeRing k n ↔ ∀ i, (p i).eval 1 = (p (finRotate n i)).eval 0 := by
  change (fun i => (p i).eval 1) = (fun i => (p (finRotate n i)).eval 0) ↔ _
  exact funext_iff

/-- Both branches of each normalization component. -/
def normalizationBoundary : NormalizationRing k n →ₐ[k] BoundaryRing k n where
  toFun p i := ((p i).eval 0, (p i).eval 1)
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' := by intros; ext <;> simp
  map_mul' := by intros; ext <;> simp
  commutes' := by intros; ext <;> simp

/-- Explicit cyclic permutation of the first endpoint. -/
def nodeBoundary : NodeValues k n →ₐ[k] BoundaryRing k n where
  toFun a i := (a ((finRotate n).symm i), a i)
  map_zero' := rfl
  map_one' := rfl
  map_add' := by intros; rfl
  map_mul' := by intros; rfl
  commutes' := by intros; rfl


theorem normalizationBoundary_surjective : Function.Surjective (normalizationBoundary k n) := by
  intro a
  refine ⟨fun i => Polynomial.linearInterpolate k (a i).1 (a i).2, ?_⟩
  ext i <;> simp [normalizationBoundary]

theorem nodeBoundary_injective : Function.Injective (nodeBoundary k n) := by
  intro a b h
  funext i
  exact congrArg (fun f : BoundaryRing k n => (f i).2) h

/-- The literal affine fibre-product algebra, not a supplied cycle object. -/
def fiberRing : Subalgebra k (NormalizationRing k n × NodeValues k n) :=
  ((normalizationBoundary k n).comp (AlgHom.fst k _ _)).equalizer
    ((nodeBoundary k n).comp (AlgHom.snd k _ _))

@[simp] theorem mem_fiberRing (p : NormalizationRing k n × NodeValues k n) :
    p ∈ fiberRing k n ↔ normalizationBoundary k n p.1 = nodeBoundary k n p.2 := Iff.rfl

/-- Each node takes the value at endpoint 1 of its preceding component. -/
def nodeEvaluation : nodeRing k n →ₐ[k] NodeValues k n :=
  (endpoint k n 1).comp (nodeRing k n).val

@[simp] theorem nodeEvaluation_apply (p : nodeRing k n) (i : Fin n) :
    nodeEvaluation k n p i = ((p : NormalizationRing k n) i).eval 1 := rfl

theorem boundary_square (p : nodeRing k n) :
    normalizationBoundary k n p = nodeBoundary k n (nodeEvaluation k n p) := by
  ext i
  · change ((p : NormalizationRing k n) i).eval 0 =
      ((p : NormalizationRing k n) ((finRotate n).symm i)).eval 1
    simpa only [Equiv.apply_symm_apply] using
      ((mem_nodeRing k n p).mp p.property ((finRotate n).symm i)).symm
  · rfl

/-- The cyclic pinching algebra mapped to its explicit boundary fibre-product presentation. -/
def toFiber : nodeRing k n →ₐ[k] fiberRing k n where
  toFun p := ⟨(p, nodeEvaluation k n p), boundary_square k n p⟩
  map_zero' := by apply Subtype.ext; exact Prod.ext rfl (map_zero _)
  map_one' := by apply Subtype.ext; exact Prod.ext rfl (map_one _)
  map_add' p q := by apply Subtype.ext; exact Prod.ext rfl (map_add _ p q)
  map_mul' p q := by apply Subtype.ext; exact Prod.ext rfl (map_mul _ p q)
  commutes' a := by apply Subtype.ext; exact Prod.ext rfl (AlgHom.commutes _ a)

/-- The polynomial component of a boundary fibre-product element, with its cyclic node equations. -/
def fromFiber : fiberRing k n →ₐ[k] nodeRing k n where
  toFun p := ⟨p.val.1, by
    rw [mem_nodeRing]
    intro i
    have h := p.property
    have h₁ := congrArg (fun f : BoundaryRing k n => (f i).2) h
    have h₂ := congrArg (fun f : BoundaryRing k n => (f (finRotate n i)).1) h
    change (p.val.1 i).eval 1 = p.val.2 i at h₁
    change (p.val.1 (finRotate n i)).eval 0 =
      p.val.2 ((finRotate n).symm (finRotate n i)) at h₂
    simp only [Equiv.symm_apply_apply] at h₂
    exact h₁.trans h₂.symm⟩
  map_zero' := by apply Subtype.ext; rfl
  map_one' := by apply Subtype.ext; rfl
  map_add' := by intros; apply Subtype.ext; rfl
  map_mul' := by intros; apply Subtype.ext; rfl
  commutes' := by intros; apply Subtype.ext; rfl

/-- The cyclic equations are proved equivalent to the explicit fibre product. -/
def fiberEquiv : nodeRing k n ≃ₐ[k] fiberRing k n :=
  AlgEquiv.ofAlgHom (toFiber k n) (fromFiber k n)
    (by apply AlgHom.ext; intro p; apply Subtype.ext; apply Prod.ext
        · rfl
        · funext i
          exact congrArg (fun f : BoundaryRing k n => (f i).2) p.property)
    (by apply AlgHom.ext; intro p; rfl)

/-- Arbitrary node values are realized by actual polynomial sections. -/
theorem nodeEvaluation_surjective : Function.Surjective (nodeEvaluation k n) := by
  intro a
  let p : NormalizationRing k n := fun i => Polynomial.linearInterpolate k (a ((finRotate
    n).symm i)) (a i)
  have hp : p ∈ nodeRing k n := by
    simp only [mem_nodeRing, p, Polynomial.linearInterpolate_one,
      Polynomial.linearInterpolate_zero, Equiv.symm_apply_apply, implies_true]
  refine ⟨⟨p, hp⟩, ?_⟩
  ext i
  simp [nodeEvaluation, endpoint, p]

/-- The diagonal covering map to the one-gon node chart. -/
def baseMap : Polynomial.PinchedPair.nodeRing k →ₐ[k] nodeRing k n where
  toFun p := ⟨fun _ => p.val, by
    rw [mem_nodeRing]
    intro i
    exact p.property.symm⟩
  map_zero' := by apply Subtype.ext; rfl
  map_one' := by apply Subtype.ext; rfl
  map_add' := by intros; apply Subtype.ext; rfl
  map_mul' := by intros; apply Subtype.ext; rfl
  commutes' := by intros; apply Subtype.ext; rfl

/-- The algebra structure on the polygon node ring induced by the pinched-line base map. -/
instance cycleAlgebra : Algebra (Polynomial.PinchedPair.nodeRing k) (nodeRing k n) :=
  (baseMap k n).toRingHom.toAlgebra

/-- The normalization inclusion is linear over the actual base-node ring. -/
def normalizationInclusion : nodeRing k n →ₐ[Polynomial.PinchedPair.nodeRing k]
  NormalizationRing k n where
  toFun := Subtype.val
  map_zero' := rfl
  map_one' := rfl
  map_add' := by intros; rfl
  map_mul' := by intros; rfl
  commutes' := by intros; rfl

/-- The polygon node ring is finite over the pinched-line node ring. -/
instance finiteModule : Module.Finite (Polynomial.PinchedPair.nodeRing k) (nodeRing k n) := by
  have : IsNoetherianRing (Polynomial.PinchedPair.nodeRing k) :=
    Algebra.FiniteType.isNoetherianRing k _
  exact Module.Finite.of_injective (normalizationInclusion k n).toLinearMap Subtype.val_injective

theorem baseMap_injective [NeZero n] : Function.Injective (baseMap k n) := by
  intro p q h
  apply Subtype.ext
  exact congrArg (fun a : nodeRing k n => (a : NormalizationRing k n) 0) h

/-- The surjection defining the base conductor square. -/
def baseBoundary : k[X] →ₐ[k] k × k := (aeval (0 : k)).prod (aeval (1 : k))

theorem baseBoundary_surjective : Function.Surjective (baseBoundary k) := by
  intro a
  refine ⟨Polynomial.linearInterpolate k a.1 a.2, ?_⟩
  ext <;> simp [baseBoundary]

/-- The polynomial action on the two endpoint fields induced by evaluation at zero and one. -/
instance boundaryAlgebra : Algebra k[X] (k × k) := (baseBoundary k).toRingHom.toAlgebra

/-- The endpoint-evaluation algebra structure is compatible with the scalar action of `k`. -/
instance boundaryTower : IsScalarTower k k[X] (k × k) :=
  IsScalarTower.of_algebraMap_eq' (baseBoundary k).comp_algebraMap.symm

/-- The explicit permutation that pairs endpoint 1 of i with endpoint 0 of i+1. -/
def boundaryTwist : BoundaryRing k n ≃ₐ[k × k] BoundaryRing k n where
  toFun a i := ((a ((finRotate n).symm i)).1, (a i).2)
  invFun a i := ((a (finRotate n i)).1, (a i).2)
  left_inv a := by ext <;> simp only [Equiv.symm_apply_apply]
  right_inv a := by ext <;> simp only [Equiv.apply_symm_apply]
  map_mul' := by intros; rfl
  map_add' := by intros; rfl
  commutes' := by intros; rfl

/-- Actual normalization-side tensor base change to the conductor boundary. -/
def normalizationBoundaryTensorEquiv :
    (k × k) ⊗[k[X]] NormalizationRing k n ≃ₐ[k × k] BoundaryRing k n :=
  Algebra.TensorProduct.piScalarRight k[X] (k × k) (k × k) (Fin n)

@[simp] theorem normalizationBoundaryTensorEquiv_one_tmul (p : NormalizationRing k n) :
    normalizationBoundaryTensorEquiv k n (1 ⊗ₜ[k[X]] p) = normalizationBoundary k n p := by
  funext i
  change (p i) • (1 : k × k) = ((p i).eval 0, (p i).eval 1)
  rw [Algebra.smul_def, mul_one]
  rfl

/-- Actual node-side tensor base change, with the explicit cyclic twist. -/
def nodeBoundaryTensorEquiv :
    (k × k) ⊗[k] NodeValues k n ≃ₐ[k × k] BoundaryRing k n :=
  (Algebra.TensorProduct.piScalarRight k (k × k) (k × k) (Fin n)).trans (boundaryTwist k n)

@[simp] theorem nodeBoundaryTensorEquiv_one_tmul (a : NodeValues k n) :
    nodeBoundaryTensorEquiv k n (1 ⊗ₜ[k] a) = nodeBoundary k n a := by
  ext i <;> simp [nodeBoundaryTensorEquiv, boundaryTwist,
    Algebra.TensorProduct.piScalarRight_tmul, Algebra.smul_def, nodeBoundary]

/-- The boundary identification needed for Milnor patching is constructed. -/
def patchingBoundaryEquiv :
    (k × k) ⊗[k] NodeValues k n ≃ₐ[k × k]
      (k × k) ⊗[k[X]] NormalizationRing k n :=
  (nodeBoundaryTensorEquiv k n).trans (normalizationBoundaryTensorEquiv k n).symm

/-- The exact conductor ideal is the kernel of the actual endpoint surjection. -/
def conductorIdeal : Ideal k[X] := RingHom.ker (baseBoundary k).toRingHom

/-- Actual quotient identification, not a certificate that a boundary exists. -/
def baseBoundaryQuotientEquiv : (k[X] ⧸ conductorIdeal k) ≃ₐ[k[X]] (k × k) where
  __ := RingHom.quotientKerEquivOfSurjective (baseBoundary_surjective k)
  commutes' _p := rfl

/-- Quotient of the normalization ring by the extended conductor ideal. -/
def normalizationQuotientBoundaryEquiv :
    (NormalizationRing k n ⧸ (conductorIdeal k).map
      (algebraMap k[X] (NormalizationRing k n))) ≃+* BoundaryRing k n :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
    (NormalizationRing k n) (conductorIdeal k)).toRingEquiv.trans <|
  (Algebra.TensorProduct.congr (AlgEquiv.refl : NormalizationRing k n ≃ₐ[NormalizationRing k n]
    NormalizationRing k n)
    (baseBoundaryQuotientEquiv k)).toRingEquiv.trans <|
  (Algebra.TensorProduct.comm k[X] (NormalizationRing k n) (k × k)).toRingEquiv.trans
    (normalizationBoundaryTensorEquiv k n).toRingEquiv

@[simp] theorem normalizationQuotientBoundaryEquiv_mk (p : NormalizationRing k n) :
    normalizationQuotientBoundaryEquiv k n (Ideal.Quotient.mk _ p) =
      normalizationBoundary k n p := by
  simp [normalizationQuotientBoundaryEquiv,
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]

/-- The product normalization algebra is etale over the polynomial ring. -/
instance normalization_etale : Algebra.Etale k[X] (NormalizationRing k n) := inferInstance
/-- The algebra of node values is etale over `k`. -/
instance nodeValues_etale : Algebra.Etale k (NodeValues k n) := inferInstance

/-- The normalization inclusion respects the tower from the pinched-line ring through the
polygon ring. -/
instance normalizationTower : IsScalarTower (Polynomial.PinchedPair.nodeRing k) (nodeRing k n)
    (NormalizationRing k n) := IsScalarTower.of_algebraMap_eq' rfl

/-- The actual polynomial-product inclusion is finite over the cyclic ring. -/
instance normalizationFinite : Module.Finite (nodeRing k n) (NormalizationRing k n) :=
  Module.Finite.of_restrictScalars_finite (Polynomial.PinchedPair.nodeRing k) (nodeRing k n)
    (NormalizationRing k n)

/-- No nilpotents are introduced by the actual cyclic equations. -/
instance nodeRing_reduced : _root_.IsReduced (nodeRing k n) :=
  isReduced_of_injective (nodeRing k n).val Subtype.val_injective

end AlgebraicGeometry.Scheme.Polygon

end -- noncomputable section
end
section
noncomputable section
open Polynomial
open scoped Polynomial
namespace AlgebraicGeometry.Scheme.Polygon
variable (k : Type u) [Field k]

/-- Idempotent polynomials on adjacent components agree by the actual node
identification; this proves connectedness, rather than assuming a graph count. -/
theorem idempotent_eq_zero_or_one (n : ℕ) [NeZero n] (p : nodeRing k n)
    (hp : IsIdempotentElem p) : p = 0 ∨ p = 1 := by
  have hi (i : Fin n) : IsIdempotentElem ((p : NormalizationRing k n) i) :=
    congrArg (fun a : nodeRing k n => (a : NormalizationRing k n) i) hp
  have hr (i : Fin n) : (p : NormalizationRing k n) (finRotate n i) =
      (p : NormalizationRing k n) i := by
    have hc := (mem_nodeRing k n p).mp p.property i
    rcases (IsIdempotentElem.iff_eq_zero_or_one.mp (hi i)) with h₀ | h₁ <;>
      rcases (IsIdempotentElem.iff_eq_zero_or_one.mp (hi (finRotate n i))) with h₂ | h₃ <;>
      simp_all
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  have he (i : Fin (m + 1)) := Fin.apply_eq_apply_zero_of_rotate_invariant m p.val hr i
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp (hi 0) with h₀ | h₁
  · left
    apply Subtype.ext
    funext i
    exact (he i).trans h₀
  · right
    apply Subtype.ext
    funext i
    exact (he i).trans h₁

/-- The actual affine cyclic scheme has connected underlying spectrum. -/
theorem spectrum_connected (n : ℕ) [NeZero n] : ConnectedSpace (PrimeSpectrum (nodeRing k n)) := by
  apply connectedSpace_iff_clopen.mpr
  refine ⟨inferInstance, ?_⟩
  intro s hs
  obtain ⟨e, he, rfl⟩ := PrimeSpectrum.isClopen_iff.mp hs
  rcases idempotent_eq_zero_or_one k n e he with rfl | rfl <;> simp

end AlgebraicGeometry.Scheme.Polygon

end -- noncomputable section
end
