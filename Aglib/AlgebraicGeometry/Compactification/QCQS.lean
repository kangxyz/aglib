/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.ActualDiagrams
public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.Absolute

/-!
# Nagata compactification over a qcqs base

A separated finite-type morphism to a quasi-compact quasi-separated scheme
admits a schematically dense compactification. Both actual approximation
diagrams are constructed, rather than supplied as hypotheses, and the
original source, base, and structural morphism are retained exactly.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Nagata compactification over an arbitrary qcqs base, with schematically
dense original source and the exact specified structural morphism. -/
theorem exists_schematicallyDense_compactification_of_qcqs
    {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ C : f.Compactification, IsSchemeTheoreticallyDominant C.j := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨A⟩ := Scheme.FinitePresentationEnvelope.nonempty_system X
  obtain ⟨B⟩ := Scheme.FinitePresentationEnvelope.nonempty_system S
  have (i : A.Index) : LocallyOfFiniteType (Products.toIntegerBase (A.diagram.obj i)) := by
    change LocallyOfFiniteType (specULiftZIsTerminal.from (A.diagram.obj i))
    exact A.finiteType i
  have (i : A.Index) : QuasiCompact (Products.toIntegerBase (A.diagram.obj i)) := by
    let : IsNoetherian (A.diagram.obj i) := ⟨⟩
    infer_instance
  have (i : B.Index) : LocallyOfFiniteType (Products.toIntegerBase (B.diagram.obj i)) := by
    change LocallyOfFiniteType (specULiftZIsTerminal.from (B.diagram.obj i))
    exact B.finiteType i
  have (i : B.Index) : QuasiCompact (Products.toIntegerBase (B.diagram.obj i)) := by
    let : IsNoetherian (B.diagram.obj i) := ⟨⟩
    infer_instance
  exact exists_schematicallyDense_compactification_of_integerFiniteType_isLimits
    A.diagram A.cone A.isLimit B.diagram B.cone B.isLimit f

/-- Every separated finite-type morphism to a qcqs scheme has an actual
open-immersion/proper compactification with the original composite unchanged. -/
theorem exists_compactification_of_qcqs
    {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    Nonempty f.Compactification := by
  obtain ⟨C, _⟩ := exists_schematicallyDense_compactification_of_qcqs f
  exact ⟨C⟩

end AlgebraicGeometry.Scheme.Hom
