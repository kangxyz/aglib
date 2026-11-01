/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Multiplication.Finite
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Multiplication.Polarization
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Degree
public import Aglib.AlgebraicGeometry.Group.Dimension

/-!
# Numerical rank of positive multiplication over an infinite field

The original projective group has an actual symmetric closed embedding.
The proved cube law gives the n² pullback scaling of its original O(1).
The native Hilbert support degree and top-coefficient rank laws then give
rank n^(2d) for the original multiplication map. All positive integers are
allowed, including inseparable levels. No numerical degree or polarization
law is a premise.

The smooth statement uses the dimension of the actual identity cotangent
space. Extension to arbitrary original fields is a separate rank-base-change
step; no arbitrary-field assertion is made by the infinite-field statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Cohomology

universe u

namespace AlgebraicGeometry.Scheme.Group.Multiplication

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] [Infinite k]

/-- Positive multiplication has native locally free rank n^(2d), with d
the actual topological dimension of the original projective group. -/
theorem multiplication_hasLocallyFreeRank_of_dimension_of_infinite
    (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X]
    [IsHProjective G.X.hom] [GeometricallyIntegral G.X.hom]
    (n : ℕ) (hn : 0 < n) (d : ℕ)
    (hd : topologicalKrullDim G.X.left = (d : WithBot ℕ∞)) :
    Hom.HasLocallyFreeRank ((𝟙 G.X) ^ n).left (n ^ (2 * d)) := by
  let : IsIntegral G.X.left := GeometricallyIntegral.isIntegral_of_subsingleton G.X.hom
  obtain ⟨I, hI, j, hj, hbasej, hsym⟩ := exists_symmetric_projective_embedding G.X
  let : Finite I := hI
  let : IsClosedImmersion j := hj
  let : Nonempty I := ProjectiveSpace.Segre.nonempty_coordinates_of_nonempty_source k j
  let := Fintype.ofFinite I
  let N := Fintype.card I - 1
  have hpos : 0 < Fintype.card I := Fintype.card_pos
  have hcard : Fintype.card I = N + 1 := (Nat.sub_add_cancel hpos).symm
  let e : I ≃ Fin (N + 1) := Fintype.equivFinOfCardEq hcard
  obtain ⟨hfinite, _, hsurjective⟩ := multiplication_finite_flat_surjective_of_isHProjective G n hn
  let f := MultiplicationKernel.multiplicationHom G n
  have hmap : f.hom.hom = (𝟙 G.X) ^ n := by
    simpa only [MultiplicationKernel.multiplication] using
      MultiplicationKernel.multiplicationHom_hom G n
  let : IsFinite f.hom.hom.left := by rw [hmap]; exact hfinite
  let : Surjective f.hom.hom.left := by rw [hmap]; exact hsurjective
  have hfree := Group.finite_surjective_hom_finiteLocallyFree G G f
  rw [hmap] at hfree
  have hbase : ((𝟙 G.X) ^ n).left ≫ (j ≫ ProjectiveSpace.toSpec k I) =
      j ≫ ProjectiveSpace.toSpec k I := by
    calc
      _ = ((𝟙 G.X) ^ n).left ≫ G.X.hom :=
        congrArg (fun p => ((𝟙 G.X) ^ n).left ≫ p) hbasej
      _ = G.X.hom := Over.w ((𝟙 G.X) ^ n)
      _ = _ := hbasej.symm
  have hscale := LineBundleCube.pullbackClass_multiplication_of_symmetric G.X
    (pullbackClass j (classOf _ (ProjectiveSpace.twistingLineBundle k I 1))) hsym n
  have h := hasLocallyFreeRank_pow_of_projective_pullback_scaling
    k I N e j ((𝟙 G.X) ^ n).left hfree hbase (n ^ 2) (pow_pos hn 2) hscale d hd
  simpa only [pow_mul] using h

/-- The dimension exponent is the original identity cotangent dimension
of the connected smooth group. This includes dimension zero and level one. -/
theorem multiplication_hasLocallyFreeRank_of_infinite
    (G : Grp (Over (Spec (.of k)))) [IsCommMonObj G.X]
    [IsHProjective G.X.hom] [GeometricallyIntegral G.X.hom] [Smooth G.X.hom]
    (n : ℕ) (hn : 0 < n) :
    Hom.HasLocallyFreeRank ((𝟙 G.X) ^ n).left
      (n ^ (2 * Module.finrank k (Cotangent.Space η[G.X]))) := by
  let : IsIntegral G.X.left := GeometricallyIntegral.isIntegral_of_subsingleton G.X.hom
  exact multiplication_hasLocallyFreeRank_of_dimension_of_infinite G n hn _
    (Group.topologicalKrullDim_eq_finrank_identityCotangent_of_preconnected G.X)

end AlgebraicGeometry.Scheme.Group.Multiplication
