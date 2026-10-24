/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Grp.FinitelyGeneratedColimit
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ConnectedConstantValues
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.QcqsSections

/-! # Original torsion constant sections on connected qcqs schemes

The coefficient need not be finite. Its actual finite generated subgroups are
finite, and original qcqs sections commute with their filtered colimit. The
comparison remains the native constant-adjunction unit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

/-- The original constant unit is an isomorphism for every torsion value on a
connected qcqs scheme, with no finiteness assumption on that value. -/
theorem constantUnit_isIso_of_isAddTorsion
    (X : Scheme.{u}) [ConnectedSpace X] [CompactSpace X] [QuasiSeparatedSpace X]
    (A : AddCommGrpCat.{u + 1}) (hA : IsAddTorsion A) :
    IsIso ((constantAdjunction X).unit.app A) := by
  classical
  let D := AddCommGrpCat.finiteSubsetDiagram A
  let c := AddCommGrpCat.finiteSubsetCocone A
  let η := (constantAdjunction X).unit
  let : CompactSpace (etaleTerminal X).left := inferInstanceAs (CompactSpace X)
  let : QuasiSeparatedSpace (etaleTerminal X).left :=
    inferInstanceAs (QuasiSeparatedSpace X)
  let : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).IsLeftAdjoint :=
    (constantAdjunction X).isLeftAdjoint
  let : PreservesColimitsOfShape (Finset A) (globalSections X) :=
    Continuity.qcqsSectionsPreservesFilteredColimits (I := Finset A) (etaleTerminal X)
  let : PreservesColimitsOfShape (Finset A)
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙ globalSections X) :=
    inferInstance
  have hstage (s : Finset A) : IsIso (η.app (D.obj s)) := by
    let : Finite (D.obj s) :=
      AddCommGrpCat.finite_finiteSubsetDiagram_of_isAddTorsion A hA s
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      (ConstantFinite.constantUnit_bijective_value_of_connected X (D.obj s))
  let : ∀ s, IsIso ((Functor.whiskerLeft D η).app s) := hstage
  let : IsIso (Functor.whiskerLeft D η) := NatIso.isIso_of_isIso_app _
  exact isIso_app_coconePt_of_preservesColimit D η c
    (AddCommGrpCat.finiteSubsetCoconeIsColimit A)

/-- The bijection retains the actual unit rather than a chosen value equivalence. -/
theorem constantUnit_bijective_of_isAddTorsion
    (X : Scheme.{u}) [ConnectedSpace X] [CompactSpace X] [QuasiSeparatedSpace X]
    (A : AddCommGrpCat.{u + 1}) (hA : IsAddTorsion A) :
    Function.Bijective ((constantAdjunction X).unit.app A) := by
  let := constantUnit_isIso_of_isAddTorsion X A hA
  exact ConcreteCategory.bijective_of_isIso _

end AlgebraicGeometry.Scheme.EtaleCohomology
