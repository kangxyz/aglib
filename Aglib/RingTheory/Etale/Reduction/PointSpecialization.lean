/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Valuation.ResidualGalois
public import Aglib.RingTheory.Unramified.Rigidity
public import Mathlib.RingTheory.Etale.Basic

/-!
Extraction source: `R5Lab.Aglib.RingTheory.Etale.Reduction.PointSpecialization`,
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`19e73d67309fab11a8b141203c6c9aba25e11f8a4a293608859f20ca0d0bf924`.
Historical source locators retain their original basis. -/

@[expose] public section

noncomputable section
open scoped TensorProduct
open Algebra.TensorProduct

/-!
# Reduction of points of a finite etale model

Source correspondence: the finite-level specialization slice supporting
`K2-015#lem:k2015-frobenius` in `research/exposes/K2/015/expose.tex`.
The local-target uniqueness lemma also supports normalization torsors.

Residue equality determines maps from an essentially finite-type formally
unramified algebra to any local target ring. For a complete nonarchimedean
field, the construction uses the literal algebraic closure, spectral integer
ring, chosen residue-closure equivalence and `absoluteResidue` map from
`ResidualGalois`. Integral-point reduction is injective and rho-equivariant.

A genuine good group model, its finite etale multiplication kernel and actual
elliptic fibre identifications remain separate geometric inputs.
-/

namespace Algebra.Etale.Reduction

section ActualReduction
open Valuation.ResidualGalois
variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (V : ValuationSubring K) [Fact (∀ x : K, x ∈ V ↔ ‖x‖₊ ≤ 1)]
  (A : Type*) [CommRing A] [Algebra V A] [Module.Finite V A]

/-- The algebra structure over `V` on the algebraic closure of its residue field. -/
local instance residueClosureAlgebra : Algebra V (AlgebraicClosure (IsLocalRing.ResidueField V)) :=
  AlgebraicClosure.instAlgebra _

/-- The factorization of a point of the finite model through the integral elements of the
algebraic closure. -/
def integralPoint (f : A →ₐ[V] AlgebraicClosure K) : A →ₐ[V] ClosureIntegers K :=
  (integralClosureEquiv K V).toAlgHom.comp
    (f.codRestrict (integralClosure V (AlgebraicClosure K))
      (fun a => (Algebra.IsIntegral.isIntegral a).map f))

theorem integralPoint_coe (f : A →ₐ[V] AlgebraicClosure K) (a : A) :
    (integralPoint K V A f a : AlgebraicClosure K) = f a :=
  integralClosureEquiv_coe K V _

/-- The specialization of a model point by reduction through the closure integer ring. -/
def specializePoint (f : A →ₐ[V] AlgebraicClosure K) :
    A →ₐ[V] AlgebraicClosure (IsLocalRing.ResidueField V) where
  __ := (closureReduction K V).comp (integralPoint K V A f).toRingHom
  commutes' a := by
    change closureReduction K V (integralPoint K V A f (algebraMap V A a)) = _
    rw [(integralPoint K V A f).commutes]
    exact closureReduction_algebraMap K V a

theorem specializePoint_injective [Algebra.Etale V A] :
    Function.Injective (specializePoint K V A) := by
  intro f g h
  have hi : integralPoint K V A f = integralPoint K V A g := by
    apply Algebra.FormallyUnramified.eq_of_comp_residue_eq
    intro a
    apply (residueClosureEquiv K V).injective
    exact congrArg (fun q => q a) h
  ext a
  exact (integralPoint_coe K V A f a).symm.trans
    ((congrArg (fun q : A →ₐ[V] ClosureIntegers K => (q a : AlgebraicClosure K)) hi).trans
      (integralPoint_coe K V A g a))

/-- Postcomposition of a model point with an absolute Galois automorphism. -/
def pointGalois (g : Field.absoluteGaloisGroup K) (f : A →ₐ[V] AlgebraicClosure K) :
    A →ₐ[V] AlgebraicClosure K :=
  (g.restrictScalars V).toAlgHom.comp f

theorem integralPoint_galois (g : Field.absoluteGaloisGroup K)
    (f : A →ₐ[V] AlgebraicClosure K) (a : A) :
    integralPoint K V A (pointGalois K V A g f) a =
      integerAut K V g (integralPoint K V A f a) := by
  apply Subtype.ext
  change (integralPoint K V A (pointGalois K V A g f) a : AlgebraicClosure K) =
    AlgEquiv.toAlgHom g (integralPoint K V A f a : AlgebraicClosure K)
  rw [integralPoint_coe, integralPoint_coe]
  rfl

theorem specializePoint_galois (g : Field.absoluteGaloisGroup K)
    (f : A →ₐ[V] AlgebraicClosure K) (a : A) :
    specializePoint K V A (pointGalois K V A g f) a =
      AlgEquiv.toAlgHom (absoluteResidue K V g) (specializePoint K V A f a) := by
  change closureReduction K V (integralPoint K V A (pointGalois K V A g f) a) = _
  rw [integralPoint_galois]
  exact (absoluteResidueHom_residue K V g (integralPoint K V A f a)).symm

/-- The generic fibre points are literal K-algebra maps from K tensor A. -/
abbrev GenericPoints := (K ⊗[V] A) →ₐ[K] AlgebraicClosure K

/-- The special fibre points are literal residue-field algebra maps. -/
abbrev SpecialPoints :=
  (IsLocalRing.ResidueField V ⊗[V] A) →ₐ[IsLocalRing.ResidueField V]
    AlgebraicClosure (IsLocalRing.ResidueField V)

/-- The tensor-product universal equivalence from model points to geometric generic-fibre points. -/
def genericPointEquiv : (A →ₐ[V] AlgebraicClosure K) ≃ GenericPoints K V A :=
  AlgHom.liftEquiv V K A (AlgebraicClosure K)

/-- The tensor-product universal equivalence from reduced model points to geometric
special-fibre points. -/
def specialPointEquiv :
    (A →ₐ[V] AlgebraicClosure (IsLocalRing.ResidueField V)) ≃ SpecialPoints K V A :=
  AlgHom.liftEquiv V (IsLocalRing.ResidueField V) A
    (AlgebraicClosure (IsLocalRing.ResidueField V))

/-- Reduction of actual field points through the integral points of the same
finite model. Neither an injection nor a desired specialization is supplied. -/
def genericPointReduction (f : GenericPoints K V A) : SpecialPoints K V A :=
  specialPointEquiv K V A
    (specializePoint K V A ((genericPointEquiv K V A).symm f))

@[simp] theorem genericPointReduction_one_tmul (f : GenericPoints K V A) (a : A) :
    genericPointReduction K V A f (1 ⊗ₜ[V] a) =
      closureReduction K V
        (integralPoint K V A ((genericPointEquiv K V A).symm f) a) := by
  simp [genericPointReduction, specialPointEquiv, specializePoint]

theorem genericPointReduction_injective [Algebra.Etale V A] :
    Function.Injective (genericPointReduction K V A) := by
  intro f g h
  apply (genericPointEquiv K V A).symm.injective
  apply specializePoint_injective K V A
  exact (specialPointEquiv K V A).injective h

/-- Actual Galois postcomposition on the generic fibre field points. -/
def genericPointGalois (g : Field.absoluteGaloisGroup K) (f : GenericPoints K V A) :
    GenericPoints K V A := g.toAlgHom.comp f

/-- Actual residue Galois postcomposition on special fibre field points. -/
def specialPointGalois (g : Field.absoluteGaloisGroup (IsLocalRing.ResidueField V))
    (f : SpecialPoints K V A) : SpecialPoints K V A := g.toAlgHom.comp f

/-- The square uses the same absoluteResidue rho constructed by restricting
actual automorphisms to ClosureIntegers K and reducing the same elements. -/
theorem genericPointReduction_galois (g : Field.absoluteGaloisGroup K)
    (f : GenericPoints K V A) :
    genericPointReduction K V A (genericPointGalois K V A g f) =
      specialPointGalois K V A (absoluteResidue K V g)
        (genericPointReduction K V A f) := by
  apply Algebra.TensorProduct.ext_ring
  ext a
  change genericPointReduction K V A (genericPointGalois K V A g f) (1 ⊗ₜ[V] a) =
    AlgEquiv.toAlgHom (absoluteResidue K V g)
      (genericPointReduction K V A f (1 ⊗ₜ[V] a))
  rw [genericPointReduction_one_tmul, genericPointReduction_one_tmul]
  exact specializePoint_galois K V A g ((genericPointEquiv K V A).symm f) a

/-- Inertia (the kernel of the same rho) fixes every generic fibre point of
an actual finite etale model, proved by equivariance and diagonal injectivity. -/
theorem genericPointGalois_eq_of_residue_one [Algebra.Etale V A]
    (g : Field.absoluteGaloisGroup K) (hg : absoluteResidue K V g = 1)
    (f : GenericPoints K V A) : genericPointGalois K V A g f = f := by
  apply genericPointReduction_injective K V A
  rw [genericPointReduction_galois, hg]
  rfl

end ActualReduction
end Algebra.Etale.Reduction
