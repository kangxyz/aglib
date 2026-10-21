/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationDiagram
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationAnnihilation
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationSections

/-! # Original coherence and annihilation on the ambient relation diagram -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X] {K : X.IdealSheafData}
  {P F : AdicSystem X K} (φ : P ⟶ F)

/-- The ambient relation diagram has coherent original levels. -/
theorem relationDiagram_coherent (n : ℕ) :
    QuasiCoherent.affineLocallyFiniteType X ((relationDiagram φ).obj (op n)) :=
  (QuasiCoherent.affineLocallyFiniteType X).prop_of_iso
    (relationDiagramObjIso φ n).symm (relation_coherent φ n)

instance relationDiagram_isQuasicoherent (n : ℕ) :
    ((relationDiagram φ).obj (op n)).IsQuasicoherent :=
  QuasiCoherent.quasicoherent_of_affineCharts _
    (fun R j _ => (relationDiagram_coherent φ n R j).1)

/-- The original ideal power annihilates the original ambient relation level. -/
theorem relationDiagram_killed (n : ℕ) :
    killedByIdealSheaf (K ^ n) ((relationDiagram φ).obj (op n)) :=
  killedByIdealSheaf_of_iso (K ^ n) (relationDiagramObjIso φ n).symm (relation_killed φ n)

end AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
