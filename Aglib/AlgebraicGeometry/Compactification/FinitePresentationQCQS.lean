/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.Compactification.FinitePresentationLimit
public import Aglib.AlgebraicGeometry.Compactification.QCQS

/-! # Actual finite-presentation compactification over a qcqs base

Only the base approximation system is used. The original finitely presented
morphism is descended directly, avoiding the schematic-closure operation that
can lose finite presentation on a non-Noetherian base.
-/

@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- A separated finitely presented map to a qcqs base has an actual proper
finite-presentation compactification, with the original composite unchanged. -/
theorem exists_finitePresentation_compactification_of_qcqs
    {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [IsSeparated f] [LocallyOfFinitePresentation f] [QuasiCompact f] :
    ∃ C : f.Compactification, LocallyOfFinitePresentation C.p := by
  obtain ⟨B⟩ := Scheme.FinitePresentationEnvelope.nonempty_system S
  have (i : B.Index) : LocallyOfFiniteType (Products.toIntegerBase (B.diagram.obj i)) := by
    change LocallyOfFiniteType (specULiftZIsTerminal.from (B.diagram.obj i))
    exact B.finiteType i
  have (i : B.Index) : QuasiCompact (Products.toIntegerBase (B.diagram.obj i)) := by
    let : IsNoetherian (B.diagram.obj i) := ⟨⟩
    infer_instance
  have (i : B.Index) : IsNoetherian (B.diagram.obj i) :=
    isNoetherian_of_integerFiniteType (B.diagram.obj i)
  let : LocallyOfFinitePresentation (show X ⟶ B.cone.pt from f) :=
    ‹LocallyOfFinitePresentation f›
  let : QuasiCompact (show X ⟶ B.cone.pt from f) := ‹QuasiCompact f›
  let : IsSeparated (show X ⟶ B.cone.pt from f) := ‹IsSeparated f›
  exact exists_finitePresentation_compactification_of_noetherian_isLimit
    B.diagram B.cone B.isLimit f

end AlgebraicGeometry.Scheme.Hom
