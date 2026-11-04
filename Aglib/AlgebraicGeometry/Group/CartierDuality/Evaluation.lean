/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.Coordinate
public import Aglib.AlgebraicGeometry.Group.CartierDuality.SpecUnits
public import Aglib.RingTheory.HopfAlgebra.FiniteDualEvaluation

/-!
# The original finite-dual evaluation morphism into the existing multiplicative group

Native coevaluation supplies the unit on the literal tensor coordinate algebra.
The original affine comparison and native Spec tensor comparison put it on the
original product scheme. The existing unit representation gives the actual
morphism into the existing multiplicative-group scheme, on arbitrary tests.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite Module
open MonoidalCategory CartesianMonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj Module.Dual.FiniteDual

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

universe u

open AlgebraicGeometry.Scheme.OverField (FScheme Base)

variable {k : Type u} [Field k]

local instance instBraidedAlgSpecEvaluation :
    (AlgebraicGeometry.algSpec (CommRingCat.of k)).Braided :=
  AlgebraicGeometry.braidedAlgSpec

variable (G : Grp (FScheme k)) [IsFinite G.X.hom] [IsCommMonObj G.X]

/-- The literal native tensor algebra used for evaluation on the original product. -/
abbrev evaluationAlgebra : CommAlgCat.{u} k :=
  CommAlgCat.of k (coordinateHopf G) ⊗ CommAlgCat.of k (Dual k (coordinateHopf G))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The literal universal unit, typed once in the selected tensor coordinate algebra. -/
def evaluationUnit : (evaluationAlgebra G)ˣ :=
  HopfAlgebra.coevaluationUnit k (coordinateHopf G)

/-- The selected coordinate unit is exactly native coevaluation with its native antipode inverse. -/
theorem evaluationUnit_eq :
    evaluationUnit G = HopfAlgebra.coevaluationUnit k (coordinateHopf G) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original product compared with native Spec of its literal tensor coordinates. -/
def coordinateProductIso :
    G.X ⊗ (dualGroup G).X ≅
      (AlgebraicGeometry.algSpec (CommRingCat.of k)).obj (op (evaluationAlgebra G)) :=
  MonoidalCategory.tensorIso
      ((Grp.forget (FScheme k)).mapIso ((coordinateSpecIso G).symm))
      (Iso.refl (dualGroup G).X) ≪≫
    algSpecTensorIso (CommAlgCat.of k (coordinateHopf G))
      (CommAlgCat.of k (Dual k (coordinateHopf G)))

/-- The actual evaluation morphism, represented by the original native coevaluation unit. -/
def evaluation : G.X ⊗ (dualGroup G).X ⟶ MultiplicativeGroup.scheme (Base k) :=
  (coordinateProductIso G).hom ≫
    specUnitMap (evaluationAlgebra G) (evaluationUnit G)

/-- The whole original coordinate equation for the actual evaluation morphism. -/
theorem evaluation_coordinate :
    (coordinateProductIso G).inv ≫ evaluation G =
      specUnitMap (evaluationAlgebra G) (evaluationUnit G) := by
  rw [evaluation, Iso.inv_hom_id_assoc]

end AlgebraicGeometry.Scheme.Group.CartierDuality
