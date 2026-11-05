/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Smooth.NoetherianDescent

/-! # Actual standard-smooth affine models over arbitrary rings

The finite-coefficient standard-smooth model is retained together with the
original tensor comparison and its literal Over pullback reconstruction.
The coefficient ring need not be a field, domain or Noetherian ring.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme
universe u

/-- A standard-smooth affine algebra, in its original relative
 dimension, has an actual finite-base affine model above any prescribed finite
 integer subalgebra. The comparison is the literal over-category pullback. -/
theorem exists_standardSmooth_affine_model_above_over_ring
    {K B : Type u} [CommRing K] [CommRing B] [Algebra K B]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n K B]
    (A : Subalgebra ℤ K) (hA : A.FG) :
    ∃ (S : Subalgebra ℤ K) (D : Type u) (_ : CommRing D) (_ : Algebra S D),
      A ≤ S ∧ S.FG ∧ Algebra.IsStandardSmoothOfRelativeDimension n S D ∧
      SmoothOfRelativeDimension n (Spec.map (CommRingCat.ofHom (algebraMap S D))) ∧
      Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap S K)))).obj
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap S D)))) ≅
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K B)))) := by
  obtain ⟨S₀, D, hD, hSD, hS₀, hsm, ⟨e⟩⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_subalgebra_fg A K B n
  let := hD
  let := hSD
  let := hsm
  let S := S₀.restrictScalars ℤ
  let : Algebra A S := S₀.algebra
  let : Algebra S D := hSD
  let : Algebra.IsStandardSmoothOfRelativeDimension n S D := hsm
  have hle : A ≤ S := fun a ha => S₀.algebraMap_mem (⟨a, ha⟩ : A)
  have hS : S.FG := S.fg_iff_finiteType.mpr
    (Algebra.FiniteType.trans (A.fg_iff_finiteType.mp hA) (S₀.fg_iff_finiteType.mp hS₀))
  have hSpec : SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (algebraMap S D))) := by
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
    apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mpr hsm
  let E : K ⊗[S] D ≃ₐ[K] B := e.symm
  let eSpec : Spec (CommRingCat.of (K ⊗[S] D)) ≅ Spec (CommRingCat.of B) :=
    (Scheme.Spec.mapIso E.toRingEquiv.toCommRingCatIso.op).symm
  have heSpec : eSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[S] D))) := by
    change Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫ _ = _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    ext x
    exact E.symm.commutes x
  let ePullback := pullbackSymmetry
      (Spec.map (CommRingCat.ofHom (algebraMap S D)))
      (Spec.map (CommRingCat.ofHom (algebraMap S K))) ≪≫
    pullbackSpecIso S K D ≪≫ eSpec
  refine ⟨S, D, hD, hSD, hle, hS, hsm, hSpec, ⟨Over.isoMk ePullback ?_⟩⟩
  change ePullback.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) = _
  simp only [ePullback, Iso.trans_hom, Category.assoc, heSpec]
  rw [pullbackSpecIso_hom_fst']
  exact pullbackSymmetry_hom_comp_fst _ _

end AlgebraicGeometry.Scheme
