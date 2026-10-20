/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.StalkMap
public import Aglib.AlgebraicGeometry.Points.Closed
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Closed-point maps of actual finite scheme morphisms
-/

@[expose] public section


noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.Scheme
universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (f : X ⟶ Y) [IsDominant f]
variable [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
variable [IsFinite f]

def closedPointMap (x : ClosedPoint X) : ClosedPoint Y :=
  ⟨f x.val, by simpa only [Set.image_singleton] using f.isClosedMap _ x.property⟩


end AlgebraicGeometry.Scheme

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/Morphisms/Finite/ClosedPoints.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 4771433b7e42eaa04fa35c9751f3164241404a6daf04e09f2b5e4834cf6f5a9a.
Native names and imports replace source wrappers; stated conditions and maps are retained. -/
