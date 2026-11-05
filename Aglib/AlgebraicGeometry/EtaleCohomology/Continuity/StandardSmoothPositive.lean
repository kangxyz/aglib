/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.ArithmeticArrowPositive
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.CartesianModelPointedZero
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.StandardSmoothAffineModel
public import Aglib.RingTheory.FiniteType.InvertibleIntegerModel

/-! # Original standard-smooth curve classes over arbitrary coefficient arrows

The source curve is modeled over an actual finitely generated subalgebra
containing the inverse of the modulus. Its original Cartesian family and its
original injective coefficient are retained by the source reconstruction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.FiniteTypeArrowLimit.TargetBaseChange
open EtaleCohomology EtaleCohomology.Continuity EtaleCohomology.Coefficients
universe u
attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- Positive-degree local effacement on an actual standard-smooth affine curve,
for an arbitrary original ring arrow and genuine injective coefficients. -/
theorem exists_standardSmooth_pointed_positive_refinement
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A C] [Algebra.IsStandardSmoothOfRelativeDimension 1 A C]
    (f : A →+* B) {Y : Scheme.{u}}
    (a : Y ⟶ Spec (.of C)) (b : Y ⟶ Spec (.of B))
    (H : IsPullback a b (Spec.algebraMap A C) (Spec.map (CommRingCat.ofHom f)))
    (q : ℕ) (hq : 0 < q) (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : A))
    (I : ModuleSheaf (Spec (.of B)) (ULift.{u + 1} (ZMod n))) [hI : Injective I]
    (c : Sheaf.H.{u + 2} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing (Spec (.of B))
        (ULift.{u + 1} (ZMod n)))).obj I)) q)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ Spec (.of C)) :
    ∃ (U : (Spec (.of C)).Etale) (xU : Spec (.of Ω) ⟶ U.left),
      xU ≫ U.hom = x ∧
      cohomologyPullback.{u, u + 2, u + 2} (pullback.snd U.hom a) _ q c = 0 := by
  let R₀ := Algebra.InvertibleIntegerModel.model n hunit
  have hR₀ : R₀.FG := R₀.fg_iff_finiteType.mpr
    (Algebra.InvertibleIntegerModel.model_finiteType n hunit)
  obtain ⟨R, D, hD, hRD, hle, hR, hsm, hSpec, ⟨Eover⟩⟩ :=
    exists_standardSmooth_affine_model_above_over_ring (K := A) (B := C) 1 R₀ hR₀
  let := hD
  let := hRD
  let : Algebra.FiniteType ℤ R := R.fg_iff_finiteType.mp hR
  let : Algebra R B := (f.comp R.val.toRingHom).toAlgebra
  let α : A →ₐ[R] B := { f with commutes' := fun _ => rfl }
  let p := Spec.algebraMap R D
  let : SmoothOfRelativeDimension 1 p := hSpec
  have hnR : IsUnit (n : R) := by
    simpa only [map_natCast] using
      (Algebra.InvertibleIntegerModel.model_isUnit n hunit).map
        (Subalgebra.inclusion hle).toRingHom
  let E : Spec (.of C) ≅ pullback (Spec.algebraMap R A) p :=
    ((Over.forget _).mapIso Eover).symm ≪≫
      pullbackSymmetry p (Spec.algebraMap R A)
  have hE : E.hom ≫ pullback.fst (Spec.algebraMap R A) p = Spec.algebraMap A C := by
    change (Eover.inv.left ≫ (pullbackSymmetry p (Spec.algebraMap R A)).hom) ≫ _ = _
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact Over.w Eover.inv
  apply exists_pointed_zero_of_cartesian_model
    a b (Spec.algebraMap A C) (Spec.map (CommRingCat.ofHom f)) H
    (familyArrow α p) (pullback.fst (Spec.algebraMap R B) p)
    (pullback.fst (Spec.algebraMap R A) p) (family_isPullback α p)
    E hE _ q c x
  intro d
  exact exists_arbitrary_arrow_pointed_positive_refinement α q hq p n hn hnR I d Ω
    (x ≫ E.hom)

end AlgebraicGeometry.Scheme.FiniteTypeArrowLimit.TargetBaseChange
