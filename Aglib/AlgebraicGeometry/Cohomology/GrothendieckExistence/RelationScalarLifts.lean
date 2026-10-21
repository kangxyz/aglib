/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedScalarSections
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.GradedNaturality
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationSections

/-! # Homogeneous relation scalars and their actual finite-stage section lifts -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
open AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A)
  {P F : AdicSystem X (idealThickeningIdealSheaf f I)} (φ : P ⟶ F)

/-- The original inclusion of the successive relation kernel into the
successive coefficient kernel. -/
def relationGradedι (n : ℕ) : relationGradedPiece φ n ⟶ P.gradedPiece n :=
  (relationGradedPieceIso φ n).hom ≫ kernel.ι (P.gradedPieceMap φ n)

@[reassoc (attr := simp)]
theorem relationGradedι_ι (n : ℕ) :
    relationGradedι f I φ n ≫ kernel.ι (P.transition n) =
      kernel.ι (relationTransition φ n) ≫ kernel.ι (φ.hom.app (op (n + 1))) :=
  relationGradedPieceIso_hom_ι_ι φ n

/-- Homogeneous multiplication on the actual relation graded kernel,
inherited through the original naturality square of coefficient maps. -/
def relationGradedScalarMap (r n : ℕ) (a : ↥(I ^ r)) :
    relationGradedPiece φ n ⟶ relationGradedPiece φ (r + n) :=
  (relationGradedPieceIso φ n).hom ≫
    kernel.map (P.gradedPieceMap φ n) (P.gradedPieceMap φ (r + n))
      (formalGradedScalarMap f I P r n a) (formalGradedScalarMap f I F r n a)
      (formalGradedScalarMap_naturality f I φ r n a) ≫
    (relationGradedPieceIso φ (r + n)).inv

@[reassoc (attr := simp)]
theorem relationGradedScalarMap_ι (r n : ℕ) (a : ↥(I ^ r)) :
    relationGradedScalarMap f I φ r n a ≫ relationGradedι f I φ (r + n) =
      relationGradedι f I φ n ≫ formalGradedScalarMap f I P r n a := by
  simp [relationGradedScalarMap, relationGradedι, Category.assoc]

/-- Multiplication of an actual lift in the ordinary relation module computes
the inherited homogeneous relation action. This is the original sectionwise
identity needed to lift positive homogeneous generators in the filtration. -/
theorem relationGradedScalarMap_section_lift (r n m : ℕ) (h : r + n + 1 ≤ m)
    (a : ↥(I ^ r)) (U : X.Opens) (x : Γ(relation φ m, U))
    (y : Γ(relationGradedPiece φ n, U))
    (hy : (relationMap φ ((Nat.add_le_add_right (Nat.le_add_left n r) 1).trans h)).app U x =
      (kernel.ι (relationTransition φ n)).app U y) :
    (kernel.ι (relationTransition φ (r + n))).app U
        ((relationGradedScalarMap f I φ r n a).app U y) =
      (relationMap φ h).app U
        ((globalScalarEndomorphism X (relation φ m) (idealThickeningBaseScalar f a)).app U x) := by
  let hn : n + 1 ≤ m := (Nat.add_le_add_right (Nat.le_add_left n r) 1).trans h
  have hyP : (kernel.ι (P.transition n)).app U ((relationGradedι f I φ n).app U y) =
      (P.obj.map (homOfLE hn).op).app U ((kernel.ι (φ.hom.app (op m))).app U x) := by
    calc
      _ = (kernel.ι (φ.hom.app (op (n + 1)))).app U
          ((kernel.ι (relationTransition φ n)).app U y) :=
        congrArg (fun k => k.app U y) (relationGradedι_ι f I φ n)
      _ = (kernel.ι (φ.hom.app (op (n + 1)))).app U ((relationMap φ hn).app U x) :=
        congrArg (fun z => (kernel.ι (φ.hom.app (op (n + 1)))).app U z) hy.symm
      _ = _ := congrArg (fun k => k.app U x) (relationMap_ι φ hn)
  apply moduleHom_app_injective (kernel.ι (φ.hom.app (op (r + n + 1)))) U
  calc
    _ = (kernel.ι (P.transition (r + n))).app U
        ((relationGradedι f I φ (r + n)).app U
          ((relationGradedScalarMap f I φ r n a).app U y)) :=
      (congrArg (fun k => k.app U ((relationGradedScalarMap f I φ r n a).app U y))
        (relationGradedι_ι f I φ (r + n))).symm
    _ = (kernel.ι (P.transition (r + n))).app U
        ((formalGradedScalarMap f I P r n a).app U
          ((relationGradedι f I φ n).app U y)) :=
      congrArg (fun z => (kernel.ι (P.transition (r + n))).app U z)
        (congrArg (fun k => k.app U y) (relationGradedScalarMap_ι f I φ r n a))
    _ = (P.obj.map (homOfLE h).op).app U
        ((globalScalarEndomorphism X (P.obj.obj (op m))
          (idealThickeningBaseScalar f a)).app U ((kernel.ι (φ.hom.app (op m))).app U x)) :=
      formalGradedScalarMap_section_lift f I P r n m h a U _ _ hyP
    _ = (P.obj.map (homOfLE h).op).app U
        ((kernel.ι (φ.hom.app (op m))).app U
          ((globalScalarEndomorphism X (relation φ m)
            (idealThickeningBaseScalar f a)).app U x)) := by
      apply congrArg ((P.obj.map (homOfLE h).op).app U)
      exact congrArg (fun k => k.app U x)
        ((globalScalarCenter X (idealThickeningBaseScalar f a)).naturality
          (kernel.ι (φ.hom.app (op m))))
    _ = _ := (congrArg (fun k => k.app U
      ((globalScalarEndomorphism X (relation φ m) (idealThickeningBaseScalar f a)).app U x))
      (relationMap_ι φ h)).symm

/-- Every original homogeneous relation product lifts to every sufficiently
high level by multiplying a lift of its lower-degree coefficient. -/
theorem exists_relationGradedScalar_section_lift (r n m : ℕ)
    (h : r + n + 1 ≤ m) [Epi (φ.hom.app (op m))]
    (a : ↥(I ^ r)) (U : X.affineOpens) (y : Γ(relationGradedPiece φ n, U.1)) :
    ∃ x : Γ(relation φ m, U.1),
      (relationMap φ h).app U.1
          ((globalScalarEndomorphism X (relation φ m) (idealThickeningBaseScalar f a)).app U.1 x) =
        (kernel.ι (relationTransition φ (r + n))).app U.1
          ((relationGradedScalarMap f I φ r n a).app U.1 y) := by
  obtain ⟨x, hx, _⟩ := exists_relationGradedPiece_section_lift φ
    ((Nat.add_le_add_right (Nat.le_add_left n r) 1).trans h) U y
  exact ⟨x, (relationGradedScalarMap_section_lift f I φ r n m h a U.1 x y hx).symm⟩

end AlgebraicGeometry.Scheme.Cohomology
