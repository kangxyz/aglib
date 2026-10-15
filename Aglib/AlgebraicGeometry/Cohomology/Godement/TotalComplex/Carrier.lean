/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Godement.Contraction
public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor

/-! # Underlying complex comparisons for Godement total and resolved contractions

Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/FlasqueDiagonalComparisons.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`e0b489185484f1e2d2cdc119bbcc7ee74dfaabbe901be4957c0e14b1301450e2`.
Selected declarations: totalPlusUnderlyingIso.
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/FlasqueThirdSpan.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`ee37f051f2106910d8b4acd0e12d72bec94cd92614e9885905e845a093d6c39e`.
Selected declarations: forgetComposeIso.
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/FlasqueGammaCarrierComparisons.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`6aa2d56a3600756c704c5d04db03d4fe4fd7b0c39496cc9c3143b49774831aff`.
Selected declarations: plusTotalCarrierIso, resolvedPlusCarrierIso, precomposedResolvedCarrierIso.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules.Godement

/-- The actual Plus totalization followed by its ordinary-cochain inclusion, compared with
ordinary totalization. -/
def totalPlusCompιIso (X : Scheme.{u}) :
    godementTotalPlus X ⋙ CochainComplex.Plus.ι X.Modules ≅
      CochainComplex.Plus.ι X.Modules ⋙ godementTotal X := by
  unfold godementTotalPlus
  exact ObjectProperty.liftCompιIso _ _ _

/-- The underlying-complex comparison for precomposed totalization, using the supplied
Plus/cochain carrier isomorphism. -/
def compTotalPlusCarrierIso {C : Type*} [Category C] (X : Scheme.{u})
    (F : C ⥤ CochainComplex.Plus X.Modules) (I : C ⥤ CochainComplex X.Modules ℤ)
    (e : F ⋙ CochainComplex.Plus.ι X.Modules ≅ I) :
    (F ⋙ godementTotalPlus X) ⋙ CochainComplex.Plus.ι X.Modules ≅ I ⋙ godementTotal X :=
  associator F (godementTotalPlus X) (CochainComplex.Plus.ι X.Modules) ≪≫
    isoWhiskerLeft F (totalPlusCompιIso X) ≪≫
    (associator F (CochainComplex.Plus.ι X.Modules) (godementTotal X)).symm ≪≫
    isoWhiskerRight e (godementTotal X)

/-- The underlying cochain comparison for the resolved contraction, preserving the actual
Godement and tensor order. -/
def resolvedContractionCompιIso (X : Scheme.{u}) (F : X.Modules ⥤ X.Modules) [F.Additive]
    (E : X.Modules) :
    godementContractionResolved X F E ⋙ CochainComplex.Plus.ι X.Modules ≅
      CochainComplex.Plus.ι X.Modules ⋙
        (F.mapHomologicalComplex (.up ℤ) ⋙ godementTotal X) ⋙
          (Complex.tensorLeft E ⋙ godementTotal X) := by
  let Q := F.mapCochainComplexPlus
  let L := (moduleTensorLeftFunctor X E).mapCochainComplexPlus
  let T := godementTotalPlus X
  let I := CochainComplex.Plus.ι X.Modules
  let Qr := F.mapHomologicalComplex (.up ℤ)
  let Lr := Complex.tensorLeft E
  let Tr := godementTotal X
  let eQ := associator Q T I ≪≫ isoWhiskerLeft Q (totalPlusCompιIso X) ≪≫
    (associator Q I Tr).symm ≪≫ isoWhiskerRight F.mapCochainComplexPlusCompι Tr ≪≫
      associator I Qr Tr
  let eL := associator L T I ≪≫ isoWhiskerLeft L (totalPlusCompιIso X) ≪≫
    (associator L I Tr).symm ≪≫
      isoWhiskerRight (moduleTensorLeftFunctor X E).mapCochainComplexPlusCompι Tr ≪≫
        associator I Lr Tr
  exact isoWhiskerRight (associator (Q ⋙ T) L T) I ≪≫
    (associator (Q ⋙ T) (L ⋙ T) I ≪≫ isoWhiskerLeft (Q ⋙ T) eL ≪≫
      (associator (Q ⋙ T) I (Lr ⋙ Tr)).symm ≪≫ isoWhiskerRight eQ (Lr ⋙ Tr) ≪≫
        associator I (Qr ⋙ Tr) (Lr ⋙ Tr))

/-- The underlying resolved-contraction comparison after precomposition with the supplied
Plus/cochain carrier isomorphism. -/
def precompResolvedContractionCompιIso {C : Type*} [Category C] (X : Scheme.{u})
    (A : C ⥤ CochainComplex.Plus X.Modules) (I : C ⥤ CochainComplex X.Modules ℤ)
    (e : A ⋙ CochainComplex.Plus.ι X.Modules ≅ I)
    (F : X.Modules ⥤ X.Modules) [F.Additive] (E : X.Modules) :
    (A ⋙ godementContractionResolved X F E) ⋙ CochainComplex.Plus.ι X.Modules ≅
      I ⋙ (F.mapHomologicalComplex (.up ℤ) ⋙ godementTotal X) ⋙
        (Complex.tensorLeft E ⋙ godementTotal X) :=
  associator A (godementContractionResolved X F E) (CochainComplex.Plus.ι X.Modules) ≪≫
    isoWhiskerLeft A (resolvedContractionCompιIso X F E) ≪≫
    (associator A (CochainComplex.Plus.ι X.Modules)
      ((F.mapHomologicalComplex (.up ℤ) ⋙ godementTotal X) ⋙
        (Complex.tensorLeft E ⋙ godementTotal X))).symm ≪≫
    isoWhiskerRight e
      ((F.mapHomologicalComplex (.up ℤ) ⋙ godementTotal X) ⋙
        (Complex.tensorLeft E ⋙ godementTotal X))

end AlgebraicGeometry.Scheme.Modules.Godement
