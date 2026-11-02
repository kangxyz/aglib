/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.SectionCompleteness
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.SectionCones
public import Aglib.CategoryTheory.Limits.Shapes.GeneratorCones
public import Aglib.CategoryTheory.Limits.Shapes.UnitMapLifting

/-! # Original formal maps between vector bundles

Original global generators and their actual kernel lift a compatible quotient
map. The quotient-unit epimorphisms prove equality of its original formal
components. Only the original section cone is used; no finite-stage internal
Hom base-change model or new presentation is introduced.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

variable (X : Scheme.{u}) [X.IsQuasiAffine] (K : X.IdealSheafData)
  (M N : X.Modules) [IsFiniteLocallyFree X M]

/-- The unchanged formal cone has the expected Hom universal property for a vector bundle. -/
theorem idealSheafHomCone_isLimit
    (hN : IsLimit (idealSheafSectionCone X K N)) :
    Nonempty (IsLimit ((coyoneda.obj (op M)).mapCone
      (⟨N, idealSheafQuotientTowerUnit X K N⟩ : Cone (idealSheafQuotientTower X K N)))) := by
  let c : Cone (idealSheafQuotientTower X K N) := ⟨N, idealSheafQuotientTowerUnit X K N⟩
  obtain ⟨hO⟩ := unitCoyoneda_isLimit_of_sections X c hN
  have hpdata := QuasiCoherent.quasiAffine_exists_finiteFree_epi X M
    (coherent_of_finiteLocallyFree M)
  obtain ⟨I, hI, p, hp⟩ := hpdata
  let := hI
  let := hp
  let : IsFiniteLocallyFree X (ShortComplex.kernelSequence p).X₂ :=
    inferInstanceAs (IsFiniteLocallyFree X (SheafOfModules.free (R := X.ringCatSheaf) I))
  let : IsFiniteLocallyFree X (ShortComplex.kernelSequence p).X₃ :=
    inferInstanceAs (IsFiniteLocallyFree X M)
  have hpseq := shortExact_kernelSequence p
  let : IsFiniteLocallyFree X (kernel p) := finiteLocallyFree_X₁_of_shortExact hpseq
  have hqdata := QuasiCoherent.quasiAffine_exists_finiteFree_epi X (kernel p)
    (coherent_of_finiteLocallyFree (kernel p))
  obtain ⟨J, hJ, q, hq⟩ := hqdata
  let := hJ
  let := hq
  exact coyoneda_isLimit_of_generators c (SheafOfModules.unit X.ringCatSheaf) hO p q

/-- Compatible original quotient maps uniquely come from an original morphism. -/
theorem idealSheafQuotientTowerHom_bijective_of_sectionCone
    (hN : IsLimit (idealSheafSectionCone X K N)) :
    Function.Bijective (idealSheafQuotientTowerHom X K (F := M) (G := N)) := by
  have hHomData := idealSheafHomCone_isLimit X K M N hN
  obtain ⟨hHom⟩ := hHomData
  let : ∀ n, Epi ((idealSheafQuotientTowerUnit X K M).app n) := fun n =>
    inferInstanceAs (Epi ((idealSheafQuotientUnit X (K ^ n.unop)).app M))
  have hm (a : M ⟶ N) :
      (Functor.const ℕᵒᵖ).map a ≫ idealSheafQuotientTowerUnit X K N =
        idealSheafQuotientTowerUnit X K M ≫ idealSheafQuotientTowerHom X K a := by
    apply NatTrans.ext
    funext n
    exact (idealSheafQuotientUnit X (K ^ n.unop)).naturality a
  exact map_bijective_of_unit_homCone
    (idealSheafQuotientTowerUnit X K M) (idealSheafQuotientTowerUnit X K N)
    (idealSheafQuotientTowerHom X K) hm hHom

/-- Explicit original scalar completeness gives full faithfulness on vector-bundle maps. -/
theorem idealSheafQuotientTowerHom_bijective_of_unit
    (hunit : IsLimit (idealSheafSectionCone X K (SheafOfModules.unit X.ringCatSheaf)))
    [IsFiniteLocallyFree X N] :
    Function.Bijective (idealSheafQuotientTowerHom X K (F := M) (G := N)) := by
  obtain ⟨hN⟩ := idealSheafSectionCone_finiteLocallyFree_isLimit X K hunit N
  exact idealSheafQuotientTowerHom_bijective_of_sectionCone X K M N hN

end AlgebraicGeometry.Scheme.Modules.Coherent
