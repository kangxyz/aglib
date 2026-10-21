/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationTower
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # The ordinary relation diagram and its original levelwise kernels -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem

universe u

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {K : X.IdealSheafData}
  {P F : AdicSystem X K} (φ : P ⟶ F)

/-- The ordinary relation diagram is a kernel in the ambient native diagram
category, not in the full subcategory of cartesian adic systems. -/
abbrev relationDiagram : ℕᵒᵖ ⥤ X.Modules := kernel φ.hom

/-- Pointwise evaluation identifies the ambient relation diagram with the
original ordinary sheaf kernels. -/
def relationDiagramObjIso (n : ℕ) :
    (relationDiagram φ).obj (op n) ≅ relation φ n :=
  PreservesKernel.iso ((CategoryTheory.evaluation ℕᵒᵖ X.Modules).obj (op n)) φ.hom

@[reassoc (attr := simp)]
theorem relationDiagramObjIso_hom_ι (n : ℕ) :
    (relationDiagramObjIso φ n).hom ≫ kernel.ι (φ.hom.app (op n)) =
      (kernel.ι φ.hom).app (op n) := by
  dsimp only [relationDiagramObjIso]
  rw [PreservesKernel.iso_hom]
  exact kernelComparison_comp_ι φ.hom
    ((CategoryTheory.evaluation ℕᵒᵖ X.Modules).obj (op n))

/-- The pointwise comparison preserves the actual ordinary relation reductions. -/
@[reassoc]
theorem relationDiagramObjIso_naturality {n m : ℕ} (h : n ≤ m) :
    (relationDiagram φ).map (homOfLE h).op ≫ (relationDiagramObjIso φ n).hom =
      (relationDiagramObjIso φ m).hom ≫ relationMap φ h := by
  apply (cancel_mono (kernel.ι (φ.hom.app (op n)))).mp
  simp only [Category.assoc, relationDiagramObjIso_hom_ι, relationMap_ι,
    relationDiagramObjIso_hom_ι_assoc]
  exact (kernel.ι φ.hom).naturality (homOfLE h).op

/-- The ordinary ambient relation diagram has surjective transition maps. -/
theorem relationDiagram_map_epi {n m : ℕ} (h : n ≤ m)
    [Epi (φ.hom.app (op m))] : Epi ((relationDiagram φ).map (homOfLE h).op) := by
  have : Epi (relationMap φ h) := relationMap_epi φ h
  have he := relationDiagramObjIso_naturality φ h
  have : Epi ((relationDiagram φ).map (homOfLE h).op ≫
      (relationDiagramObjIso φ n).hom) := by
    rw [he]
    infer_instance
  exact (epi_comp_iff_of_isIso _ (relationDiagramObjIso φ n).hom).mp inferInstance

end AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
