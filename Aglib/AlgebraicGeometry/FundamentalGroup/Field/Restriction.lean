/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.ArbitraryGalois
public import Aglib.AlgebraicGeometry.FundamentalGroup.PointedPrecomposition
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange.GroupScheme

/-! # Original fibre-group restriction along a field extension

The equality-aware pointed-scheme map sends the original ambient field
automorphism to its restriction of scalars. The proof retains the same
ambient field, actual pullback fibre equivalence, and positive action
convention. No characteristic-zero or alternate closure assumption is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.EtaleFundamentalGroups Scheme.FiniteEtale.GroupBaseChange
open Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.OverRing

universe u

variable (E M Ω : Type u) [Field E] [Field M] [Field Ω]
  [Algebra E M] [Algebra M Ω] [Algebra E Ω] [IsScalarTower E M Ω]

/-- The original field-valued point is the literal composite through the
intermediate field. -/
theorem basePoint_comp_algebraMap :
    basePoint M Ω ≫ Spec.algebraMap E M = basePoint E Ω := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (IsScalarTower.algebraMap_eq E M Ω).symm

/-- Restriction of scalars retains the literal endomorphism of the ambient
field spectrum. -/
theorem pointEnd_left_restrictScalars (σ : Ω ≃ₐ[M] Ω) :
    (pointEnd M M Ω σ).left = (pointEnd E E Ω (σ.restrictScalars E)).left := rfl

/-- The original field action formulas commute with any actual map of the
indicated pointed field spectra, point by point. -/
theorem pointedFiber_toFibreAut
    (f : Under.mk (basePoint M Ω) ⟶ Under.mk (basePoint E Ω))
    (σ : Ω ≃ₐ[M] Ω) (Y : Scheme.FiniteEtale (Spec (.of E)))
    (p : Fiber (basePoint E Ω) Y) :
    (pointedFiberEquiv f Y).symm
      ((toFibreAut M M Ω σ).hom.app ((baseChange f.right).obj Y)
        (pointedFiberEquiv f Y p)) =
      (toFibreAut E E Ω (σ.restrictScalars E)).hom.app Y p := by
  have h₁ := congrArg (pointedFiberEquiv f Y).symm
    (toFibreAut_apply M M Ω σ ((baseChange f.right).obj Y) (pointedFiberEquiv f Y p))
  have h₂ := pointedFiberEquiv_symm_precomp f
    (pointEnd M M Ω σ) (pointEnd E E Ω (σ.restrictScalars E))
    (pointEnd_left_restrictScalars E M Ω σ) Y p
  have h₃ := toFibreAut_apply E E Ω (σ.restrictScalars E) Y p
  exact h₁.trans (h₂.trans h₃.symm)

/-- Original natural field actions commute with an explicitly supplied
pointed map, retaining that map as a typed parameter in the global equality. -/
theorem pointedMap_toFibreAut_of_map
    (f : Under.mk (basePoint M Ω) ⟶ Under.mk (basePoint E Ω))
    (σ : Ω ≃ₐ[M] Ω) :
    pointedMap f (toFibreAut M M Ω σ) = toFibreAut E E Ω (σ.restrictScalars E) :=
  pointedMap_eq_of_fiber_components (K := Ω)
    (S := Under.mk (basePoint M Ω)) (X := Under.mk (basePoint E Ω)) f
    (toFibreAut M M Ω σ) (toFibreAut E E Ω (σ.restrictScalars E))
    (pointedFiber_toFibreAut E M Ω f σ)

/-- The underlying natural fibre automorphisms commute with the actual
pointed map. This algebraic statement does not elaborate continuity proofs. -/
theorem pointedMap_toFibreAut (σ : Ω ≃ₐ[M] Ω) :
    pointedMap (Under.homMk (Spec.algebraMap E M) (basePoint_comp_algebraMap E M Ω) :
      Under.mk (basePoint M Ω) ⟶ Under.mk (basePoint E Ω))
      (toFibreAut M M Ω σ) = toFibreAut E E Ω (σ.restrictScalars E) :=
  pointedMap_toFibreAut_of_map E M Ω
    (Under.homMk (Spec.algebraMap E M) (basePoint_comp_algebraMap E M Ω)) σ

/-- The actual pointed finite-etale fibre-group map is restriction of the
same ambient field automorphism, with no change of action convention. -/
theorem inducedGroupHomPointed_galoisToFibre
    [Algebra.IsIntegral E Ω] [Algebra.IsIntegral M Ω] (σ : Ω ≃ₐ[M] Ω) :
    inducedGroupHomPointed (Spec.algebraMap E M) (basePoint M Ω) (basePoint E Ω)
      (basePoint_comp_algebraMap E M Ω) (galoisToFibre M M Ω σ) =
        galoisToFibre E E Ω (σ.restrictScalars E) :=
  pointedMap_toFibreAut E M Ω σ

end AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois.OverRing
