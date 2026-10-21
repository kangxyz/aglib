/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.OrdinaryNodePreparation
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.ProjectiveTranslation
public import Aglib.AlgebraicGeometry.Curves.Nodal.Polygon.FiniteClosedCover
public import Aglib.AlgebraicGeometry.Curves.Models.Components.SubsetCover
public import Aglib.AlgebraicGeometry.Curves.Models.Components.NeighborIntersections
public import Aglib.AlgebraicGeometry.Morphisms.Proper.CurveComponentHelpers
public import Aglib.GroupTheory.Perm.CycleValues
public import Mathlib.Algebra.Field.ZMod

/-! Native clients for the actual split equations, original projective maps,
positive-degree structure cohomology and ordered polygon intersections. -/

@[expose] public noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace NodalComponentsTail

/-- The concrete characteristic-two field uses the actual primality of two. -/
local instance primeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The concrete characteristic-three field uses the actual primality of three. -/
local instance primeThree : Fact (Nat.Prime 3) := ⟨by decide⟩

example :
    WeierstrassCurve.CriticalPoint.criticalHessianDet
      (WeierstrassCurve.SplitNodalNormalForm.equation (0 : ZMod 2)) 0 ≠ 0 := by
  exact WeierstrassCurve.SplitNodalNormalForm.hessian_ne_zero_of_simple_tangent
    (k := ZMod 2) (WeierstrassCurve.SplitNodalNormalForm.equation (0 : ZMod 2))
    (0 : ZMod 2) (0 : ZMod 2) (by norm_num [WeierstrassCurve.SplitNodalNormalForm.equation])
    (by norm_num [WeierstrassCurve.SplitNodalNormalForm.equation])

example {k : Type} [Field k] (W : WeierstrassCurve k) (r t : k) :
    (WeierstrassCurve.Projective.Translation.translatedProjectiveIso W r t).hom ≫
      WeierstrassCurve.Projective.structureMap W =
        WeierstrassCurve.Projective.structureMap (WeierstrassCurve.translate W r t) :=
  WeierstrassCurve.Projective.Translation.translatedProjectiveMap_over W r t

example {k : Type} [Field k] (W : WeierstrassCurve k) (r t : k) :
    WeierstrassCurve.Projective.affineChart (WeierstrassCurve.translate W r t) ≫
      (WeierstrassCurve.Projective.Translation.translatedProjectiveIso W r t).hom =
        (WeierstrassCurve.CriticalCubic.SingularTranslation.translatedAffineIso W r t).hom ≫
          WeierstrassCurve.Projective.affineChart W :=
  WeierstrassCurve.Projective.Translation.translatedProjectiveIso_affine W r t

example : Subsingleton (Sheaf.H (Scheme.structureAddSheaf
    (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ))) 1) :=
  Scheme.OverField.Curve.ProjectiveLine.projectiveSpaceStructureCohomologyVanishing
    ℤ 1 1 (by decide)

example (p : Spec (.of (ZMod 2)) ⟶ Scheme.Polygon.cycleScheme (ZMod 2) 1) :
    ∃ s : Spec (.of (ZMod 2)) ⟶ Scheme.Polygon.normalizedScheme (ZMod 2) 1,
      s ≫ Scheme.Polygon.gluedPolynomialCover (ZMod 2) 1 = p :=
  Scheme.Polygon.gluedPolynomialCover_fieldPoint_lift (ZMod 2) 1 (ZMod 2) p

example : IsPullback (Scheme.Polygon.boundaryLineMap (ZMod 2))
    (Scheme.Polygon.reverseBoundaryLineMap (ZMod 2))
    (Scheme.Polygon.componentTarget (ZMod 2) 2 0)
    (Scheme.Polygon.componentTarget (ZMod 2) 2 1) :=
  Scheme.Polygon.twoPair_isPullback (ZMod 2) 0 1 (by decide)

example : IsPullback (Scheme.Polygon.targetLinePoint (ZMod 3) 1)
    (Scheme.Polygon.targetLinePoint (ZMod 3) 0)
    (Scheme.Polygon.componentTarget (ZMod 3) 3 0)
    (Scheme.Polygon.componentTarget (ZMod 3) 3 (finRotate 3 0)) :=
  Scheme.Polygon.outgoingPair_isPullback (ZMod 3) 3 (by decide) 0

example {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (V : Y.Opens)
    (hV : (V : Set Y).Nonempty) [IsIso (f ∣_ V)] :
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)) :=
  Scheme.Hom.functionField_iso_of_isIso_restrict f V hV

end NodalComponentsTail
