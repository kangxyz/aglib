/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.AffineCovers
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.Covers
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Connected
public import Mathlib.AlgebraicGeometry.Limits

/-!
# The finite-affine-cover basis for small étale cohomology

Selected finite affine families are genuinely cofinal in covering sieves.
Their intersections are the actual categorical products in the original slice,
whose underlying schemes are affine by the native wide-pullback universal property.
No cohomological vanishing is part of the basis data.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

/-- Original finite intersections of affine étale objects over an affine object are affine. -/
theorem isAffine_finite_product {X : Scheme.{u}} (W : X.Etale) [IsAffine W.left]
    {ι : Type} [Finite ι] (U : ι → Over W) [∀ i, IsAffine (U i).left.left] :
    IsAffine (∏ᶜ U).left.left := by
  let : Fintype ι := Fintype.ofFinite ι
  let F : X.Etale ⥤ Scheme.{u} := Etale.forget X ⋙ Over.forget X
  let D := Over.ConstructProducts.widePullbackDiagramOfDiagramOver W (Discrete.functor U)
  let c : Cone D := (Over.ConstructProducts.conesEquiv W (Discrete.functor U)).inverse.obj
    (limit.cone (Discrete.functor U))
  have hc : IsLimit c := IsLimit.ofRightAdjoint
    (Over.ConstructProducts.conesEquiv W (Discrete.functor U)).toAdjunction
    (limit.isLimit (Discrete.functor U))
  have : ∀ i, IsAffine ((D ⋙ F).obj i) := by
    intro i
    cases i with
    | none => exact inferInstanceAs (IsAffine W.left)
    | some i => exact inferInstanceAs (IsAffine (U i).left.left)
  exact Scheme.isAffine_of_isLimit (F.mapCone c) (isLimitOfPreserves F hc)

/-- The actual affine basis with finite affine covering families, not singleton covers. -/
def affineCoverBasis (X : Scheme.{u}) :
    CategoryTheory.Sheaf.BasisAcyclicity.CoverBasis.{u + 1, u, 0}
      (Scheme.smallEtaleTopology X) where
  objects W := IsAffine W.left
  selected W ι U := IsAffine W.left ∧ Finite ι ∧
    (∀ i, IsAffine (U i).left.left) ∧
      Sieve.ofArrows (fun i => (U i).left) (fun i => (U i).hom) ∈
        Scheme.smallEtaleTopology X W
  covering h := h.2.2.2
  cofinal W hW R hR := by
    let := hW
    obtain ⟨n, V, f, hV, hf, hcover⟩ := exists_finite_affine_family W R hR
    exact ⟨Fin n, fun i => Over.mk (f i), ⟨hW, inferInstance, hV, hcover⟩, hf⟩
  intersections := by
    intro W ι U h n a
    let : IsAffine W.left := h.1
    let : ∀ i, IsAffine (U (a i)).left.left := fun i => h.2.2.1 (a i)
    exact isAffine_finite_product W (fun i => U (a i))

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
