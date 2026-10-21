/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationDiagramProperties

/-! # Successive kernels of the native ambient relation diagram -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
namespace AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X] {K : X.IdealSheafData}
  {P F : AdicSystem X K} (φ : P ⟶ F)

/-- The original adjacent relation kernels are coherent. -/
theorem relationGradedPiece_coherent (n : ℕ) :
    affineLocallyFiniteType X (relationGradedPiece φ n) :=
  affineLocallyFiniteType_of_quasicoherent_mono (kernel.ι (relationTransition φ n))
    (relation_coherent φ (n + 1))

/-- The ambient diagram's actual successive kernel identifies with the actual
relation graded piece through the original stage isomorphisms. -/
def relationDiagramGradedIso (n : ℕ) :
    kernel ((relationDiagram φ).map (homOfLE (Nat.le_succ n)).op) ≅ relationGradedPiece φ n :=
  kernel.mapIso _ _ (relationDiagramObjIso φ (n + 1)) (relationDiagramObjIso φ n)
    (relationDiagramObjIso_naturality φ (Nat.le_succ n))

/-- The identification retains the original adjacent inclusion. -/
@[reassoc (attr := simp)]
theorem relationDiagramGradedIso_hom_ι (n : ℕ) :
    (relationDiagramGradedIso φ n).hom ≫ kernel.ι (relationTransition φ n) =
      kernel.ι ((relationDiagram φ).map (homOfLE (Nat.le_succ n)).op) ≫
        (relationDiagramObjIso φ (n + 1)).hom := by
  simp [relationDiagramGradedIso, kernel.mapIso]

end AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
