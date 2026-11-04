/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.Evaluation

/-! The actual evaluation map has the original universal unit, also on unrestricted test schemes. -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open MonoidalCategory
open AlgebraicGeometry.Scheme.OverField (FScheme Base)
open AlgebraicGeometry.Scheme.Group
open CartierDuality
open scoped Module.Dual.FiniteDual

universe u

variable {k : Type u} [Field k] (G : Grp (FScheme k))
  [IsFinite G.X.hom] [IsCommMonObj G.X]

example : G.X ⊗ (dualGroup G).X ⟶ (MultiplicativeGroup.groupScheme (Base k)).X := evaluation G

example : evaluationUnit G = HopfAlgebra.coevaluationUnit k (coordinateHopf G) :=
  evaluationUnit_eq G

example : (coordinateProductIso G).inv ≫ evaluation G =
    specUnitMap (evaluationAlgebra G) (evaluationUnit G) :=
  evaluation_coordinate G
