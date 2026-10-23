/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.PointSupportedSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.EtaleDimensionOne

/-! # Finite closed support stages for actual curve sections -/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace Set

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

variable {X : Scheme.{u}} [IsNoetherian X]
    (F : AbelianSheaf.{u, u + 1} X) {U : X.Etale} [QuasiCompact U.hom]

/-- Generic local vanishing on an actual etale curve test gives finite support on the base. -/
theorem sectionSupportImage_finite (hdim : topologicalKrullDim X ≤ 1)
    (a : F.obj.obj (op U))
    (ha : genericPoints U.left ⊆ Etale.sectionZeroLocus F.obj a) :
    (sectionSupportImage F a).Finite := by
  let : IsNoetherian U.left := {
    toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
      (X := U.left) (Y := X) U.hom
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
      (X := U.left) (Y := X) U.hom }
  exact (finite_compl_open_of_contains_genericPoints (X := U.left)
    (topologicalKrullDim_le_one_of_etale (U := U.left) (X := X) U.hom hdim)
    (Etale.isOpen_sectionZeroLocus F.obj a) ha).image U.hom

omit [QuasiCompact U.hom] in
/-- Each point in the support image is closed. This uses genuine etale generic-point
lifting, rather than a claim that etale maps preserve arbitrary closed subsets. -/
theorem sectionSupportImage_closed_points (hdim : topologicalKrullDim X ≤ 1)
    (a : F.obj.obj (op U))
    (ha : genericPoints U.left ⊆ Etale.sectionZeroLocus F.obj a)
    (x : X) (hx : x ∈ sectionSupportImage F a) : IsClosed ({x} : Set X) := by
  obtain ⟨y, hy, rfl⟩ := hx
  apply isClosed_singleton_of_not_generic_of_dim_le_one hdim
  intro hg
  exact hy (ha (mem_genericPoints_of_etale_image (V := U.left) (U := X) U.hom y hg))

/-- Every section vanishing locally at generic points lifts to an actual finite closed
support subobject, with the original inclusion giving back that same section. -/
theorem exists_finite_closed_support_section (hdim : topologicalKrullDim X ≤ 1)
    (a : F.obj.obj (op U))
    (ha : genericPoints U.left ⊆ Etale.sectionZeroLocus F.obj a) :
    ∃ Z : Set X, Z.Finite ∧ (∀ x ∈ Z, IsClosed ({x} : Set X)) ∧
      ∃ b : (pointSupportedSubobject F Z : AbelianSheaf.{u, u + 1} X).obj.obj (op U),
        (pointSupportedSubobject F Z).arrow.hom.app (op U) b = a := by
  exact ⟨sectionSupportImage F a, sectionSupportImage_finite F hdim a ha,
    sectionSupportImage_closed_points F hdim a ha, exists_pointSupported_section F a⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
