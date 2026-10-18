/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Picard.Comparison.Sheaf

/-! Focused consumer of the separatedness of the relative and rigidified Picard functors (from the
fppf comparison map of Kleiman's Thm 2.5(1), *The Picard scheme*, arXiv:math/0504020v1, p. 18) and
of the gluing statement `RigidifiedGluing p o ho` of Stacks 0B9N. -/

@[expose] public section

noncomputable section
open CategoryTheory Limits Opposite AlgebraicGeometry
open Scheme.RelativePicard

universe u

variable {S X : Scheme.{u}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

example [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] :
    Presieve.IsSeparated (Scheme.fppfTopology.over S)
      (relativePicardFunctor p ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
  isSeparated_relativePicardFunctor_of_isProper_of_flat_of_geometricallyIntegral p

example [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] :
    Presieve.IsSeparated (Scheme.fppfTopology.over S) (rigidifiedPicardFunctor p o ho) :=
  isSeparated_rigidifiedPicardFunctor_of_isProper_of_flat_of_geometricallyIntegral p o ho

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isSeparated_relativePicardFunctor_of_isProper_of_flat_of_geometricallyIntegral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms isSeparated_relativePicardFunctor_of_isProper_of_flat_of_geometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isSeparated_rigidifiedPicardFunctor_of_isProper_of_flat_of_geometricallyIntegral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms isSeparated_rigidifiedPicardFunctor_of_isProper_of_flat_of_geometricallyIntegral
