/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Picard.Comparison.Isomorphism

/-! Focused consumer of Kleiman's Thm 2.5(2) (*The Picard scheme*, arXiv:math/0504020v1, p. 18;
Stacks 0B9N): with a section, the rigidified Picard functor is an fppf sheaf and the comparison map
`P_{X/S} ⟶ Pic_{X/S,(fppf)}` is an isomorphism, for `S` locally Noetherian and `p` proper, flat,
with geometrically integral fibres (the fppf comparison map, with a global section). No gluing
premise remains. -/

@[expose] public section

noncomputable section
open CategoryTheory Limits Opposite AlgebraicGeometry
open Scheme.RelativePicard Pseudofunctor

universe u

variable {S X : Scheme.{u}} (p : X ⟶ S) (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

example [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] :
    RigidifiedGluing p o ho :=
  rigidifiedGluing_of_isProper_of_flat_of_geometricallyIntegral p o ho

example [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] :
    Presieve.IsSheaf (Scheme.fppfTopology.over S) (rigidifiedPicardFunctor p o ho) :=
  isSheaf_rigidifiedPicardFunctor_of_isProper_of_flat_of_geometricallyIntegral p o ho

example [IsSplitEpi p] [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] :
    IsIso (toFppfPicardSheaf p) :=
  isIso_toFppfPicardSheaf_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral p

example [IsSplitEpi p] [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] :
    (relativeFppfIsoOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral p).hom =
      toFppfPicardSheaf p :=
  relativeFppfIsoOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral_hom p

example [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] :
    normalizedPicardFunctor p o ho ≅ (fppfPicardSheaf p).obj :=
  normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho

example [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] :
    (rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral p o ho).hom =
      (rigidifiedRelativeIso p o ho).hom ≫
        Functor.whiskerRight (toFppfPicardSheaf p) (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
  rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral_hom p o ho

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.rigidifiedGluing_of_isIso_c' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rigidifiedGluing_of_isIso_c

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.rigidifiedGluing_of_isProper_of_flat_of_geometricallyIntegral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rigidifiedGluing_of_isProper_of_flat_of_geometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isSheaf_rigidifiedPicardFunctor_of_isProper_of_flat_of_geometricallyIntegral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms isSheaf_rigidifiedPicardFunctor_of_isProper_of_flat_of_geometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isSheaf_relativePicardFunctor_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms isSheaf_relativePicardFunctor_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isIso_toFppfPicardSheaf_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms isIso_toFppfPicardSheaf_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.relativeFppfIsoOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms relativeFppfIsoOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms normalizedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms rigidifiedFppfIsoOfIsProperOfFlatOfGeometricallyIntegral_eq
