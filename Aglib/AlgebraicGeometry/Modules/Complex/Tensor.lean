/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Modules.Tensor.Restriction
public import Aglib.AlgebraicGeometry.Modules.Tensor.Symmetry
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Tensor.Exact

/-! # Degreewise left and right tensor on module-sheaf complexes

Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/LineTensor.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`80b4048e0507b829d438c3aa681ba364645f6c93e62146e7013f9e33e04ee98e`.
Selected declarations: tensorByLineComplex, tensorByLineRightComplex, tensorByLineComplexSymmetry,
  tensorByLineComplex_additive, tensorByLineComplex_preservesFiniteLimits,
  tensorByLineComplex_preservesFiniteColimits, tensorByLineComplex_quasiIso.
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/FlasqueCoefficientOperations.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`5f3c26c6e4098e7710135369b9bfa057c833cb1880dea3ef318c4265606bb071`.
Selected declarations: rightLineComplex_additive, rightLineComplex_preservesFiniteLimits,
  rightLineComplex_preservesFiniteColimits, rightLineComplex_quasiIso.
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/P5NativePhiSupport.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`91cab94a8c9ac24cbaaed74cf4fcd39bacea273e378e4a00ba43a9fa26ae76b2`.
Selected declarations: leftTensorRestrictionIso.
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/P5NativeCoefficientsSupport.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`f960093218542cb3dc2e13439cc03be9268b0cb50607f10d119b08f3d24a31dd`.
Selected declarations: rightTensorRestrictionIso.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules.Complex

/-- Degreewise tensor on the left by the specified module sheaf, on ordinary integer complexes. -/
def tensorLeft {X : Scheme.{u}} (L : X.Modules) : CochainComplex X.Modules ℤ ⥤ CochainComplex
  X.Modules ℤ :=
  (moduleTensorLeftFunctor X L).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Degreewise tensor on the right by the specified module sheaf, on ordinary integer complexes. -/
def tensorRight {X : Scheme.{u}} (L : X.Modules) : CochainComplex X.Modules ℤ ⥤ CochainComplex
  X.Modules ℤ :=
  (moduleTensorRightFunctor X L).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The comparison between left and right coefficient tensor induced by the canonical braiding. -/
def tensorLeftRightIso {X : Scheme.{u}} (L : X.Modules) :
    tensorLeft L ≅ tensorRight L :=
  NatIso.mapHomologicalComplex ((moduleTensorRightLeftIso X L).symm) _

instance tensorLeft_additive {X : Scheme.{u}} (L : X.Modules) :
    (tensorLeft L).Additive := by unfold tensorLeft; infer_instance

instance tensorLeft_preservesFiniteLimits {X : Scheme.{u}} (L : X.Modules)
    [IsFiniteLocallyFree X L] : PreservesFiniteLimits (tensorLeft L) := by
  unfold tensorLeft
  let : PreservesFiniteLimits (moduleTensorLeftFunctor X L) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  infer_instance

instance tensorLeft_preservesFiniteColimits {X : Scheme.{u}} (L : X.Modules)
    [IsFiniteLocallyFree X L] : PreservesFiniteColimits (tensorLeft L) := by
  unfold tensorLeft
  let : PreservesFiniteColimits (moduleTensorLeftFunctor X L) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  infer_instance

instance tensorLeft_quasiIso {X : Scheme.{u}} (L : X.Modules)
    [IsFiniteLocallyFree X L] {K M : CochainComplex X.Modules ℤ} (f : K ⟶ M) [QuasiIso f] :
    QuasiIso ((tensorLeft L).map f) := by
  unfold tensorLeft
  infer_instance

instance tensorRight_additive {X : Scheme.{u}} (L : X.Modules) :
    (tensorRight L).Additive := by
  unfold tensorRight
  infer_instance

instance tensorRight_preservesFiniteLimits {X : Scheme.{u}} (L : X.Modules)
    [IsFiniteLocallyFree X L] : PreservesFiniteLimits (tensorRight L) := by
  unfold tensorRight
  let : PreservesFiniteLimits (moduleTensorRightFunctor X L) :=
    Functor.preservesFiniteLimits_of_preservesHomology _
  infer_instance

instance tensorRight_preservesFiniteColimits {X : Scheme.{u}} (L : X.Modules)
    [IsFiniteLocallyFree X L] : PreservesFiniteColimits (tensorRight L) := by
  unfold tensorRight
  let : PreservesFiniteColimits (moduleTensorRightFunctor X L) :=
    Functor.preservesFiniteColimits_of_preservesHomology _
  infer_instance

instance tensorRight_quasiIso {X : Scheme.{u}} (L : X.Modules)
    [IsFiniteLocallyFree X L] {K M : CochainComplex X.Modules ℤ} (f : K ⟶ M) [QuasiIso f] :
    QuasiIso ((tensorRight L).map f) := by
  unfold tensorRight
  infer_instance

/-- Open restriction commutes with degreewise left tensor by the restricted coefficient sheaf. -/
def tensorLeftRestrictionIso {U P : Scheme.{u}} (j : U ⟶ P) [IsOpenImmersion j]
    (L : P.Modules) :
    tensorLeft L ⋙ restrict j ≅ restrict j ⋙ tensorLeft (L.restrict j) :=
  (Functor.mapHomologicalComplexCompIso (tensorRestrictionNatIso j L) _).symm

/-- Open restriction commutes with degreewise right tensor by the restricted coefficient sheaf. -/
def tensorRightRestrictionIso {U P : Scheme.{u}} (j : U ⟶ P) [IsOpenImmersion j]
    (L : P.Modules) :
    tensorRight L ⋙ restrict j ≅
      restrict j ⋙ tensorRight (L.restrict j) :=
  Functor.isoWhiskerRight (tensorLeftRightIso L).symm (restrict j) ≪≫
    (Functor.mapHomologicalComplexCompIso (tensorRestrictionNatIso j L) _).symm ≪≫
    Functor.isoWhiskerLeft (restrict j) (tensorLeftRightIso (L.restrict j))

end AlgebraicGeometry.Scheme.Modules.Complex
