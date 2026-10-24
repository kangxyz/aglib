/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ConnectedTorsionSections

/-! # Finite value subgroups for original constant torsion sections

On a qcqs scheme an original constant-coefficient section comes from an actual
finitely generated subgroup of the original coefficient. For torsion
coefficients this subgroup is finite. The scheme need not be connected.
This does not assert that the entire group of constant finite-coefficient
sections is finite, nor that a general cohomology edge map is injective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

/-- Every original constant section on a qcqs scheme factors through the
original inclusion of one finitely generated subgroup of its coefficient. -/
theorem exists_finiteSubset_constant_section_factor
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (A : AddCommGrpCat.{u + 1})
    (x : (globalSections X).obj
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)) :
    ∃ s : Finset A, ∃ y : (globalSections X).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          ((AddCommGrpCat.finiteSubsetDiagram A).obj s)),
      (globalSections X).map
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
          ((AddCommGrpCat.finiteSubsetCocone A).ι.app s)) y = x := by
  let C := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let : CompactSpace (etaleTerminal X).left := inferInstanceAs (CompactSpace X)
  let : QuasiSeparatedSpace (etaleTerminal X).left :=
    inferInstanceAs (QuasiSeparatedSpace X)
  let : C.IsLeftAdjoint := (constantAdjunction X).isLeftAdjoint
  let : PreservesColimitsOfShape (Finset A) (globalSections X) :=
    Continuity.qcqsSectionsPreservesFilteredColimits (I := Finset A) (etaleTerminal X)
  let H := (C ⋙ globalSections X) ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}
  let : PreservesColimitsOfShape (Finset A) H := inferInstance
  exact Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves H (AddCommGrpCat.finiteSubsetCoconeIsColimit A)) x

/-- For an arbitrary torsion coefficient, the actual factor subgroup is
finite, and the map remains its original inclusion into the given group.
No connectedness, Noetherianity or finite-component hypothesis is used. -/
theorem exists_finite_constant_torsion_section_factor
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (A : AddCommGrpCat.{u + 1}) (hA : IsAddTorsion A)
    (x : (globalSections X).obj
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)) :
    ∃ s : Finset A, Finite ((AddCommGrpCat.finiteSubsetDiagram A).obj s) ∧
      ∃ y : (globalSections X).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          ((AddCommGrpCat.finiteSubsetDiagram A).obj s)),
        (globalSections X).map
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
            ((AddCommGrpCat.finiteSubsetCocone A).ι.app s)) y = x := by
  obtain ⟨s, y, hy⟩ := exists_finiteSubset_constant_section_factor X A x
  exact ⟨s, AddCommGrpCat.finite_finiteSubsetDiagram_of_isAddTorsion A hA s, y, hy⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
