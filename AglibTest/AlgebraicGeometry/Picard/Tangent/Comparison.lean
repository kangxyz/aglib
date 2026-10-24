/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Tangent.Comparison

/-! Focused consumer of the vertical maps of Kleiman's Square (5.11.4) (arXiv:math/0504020v1,
proof of Thm 5.11, pp. 43–44): the closed point and the scaling as morphisms of `k`-schemes and
the maps of fibres they induce, the commuting square and its naturality in `µ_a`, injectivity
(Thm 2.5(1), p. 18) and, with a section, the equivalence of kernels (Thm 2.5(2), p. 18) with its
value on classes and its compatibility with `µ_a`. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.DualNumbers
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local

universe u

section Ring

variable (k : Type u) [CommRing k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

example (a : k) : closedPointOver k ≫ scaleOver k a = closedPointOver k :=
  closedPointOver_scaleOver k a

example : familyClosedPoint sX = pullback.fst sX (𝟙 (Spec (.of k))) ≫ inclusion k sX :=
  familyClosedPoint_eq sX

example : inv (pullback.fst sX (𝟙 (Spec (.of k)))) ≫ familyClosedPoint sX = inclusion k sX :=
  inv_pullback_fst_familyClosedPoint sX

example (a : k) : familyScale sX a = dualScale k sX a :=
  familyScale_eq sX a

end Ring

section Field

variable {k : Type u} [Field k] (X : FScheme k)

/-- Square (5.11.4) commutes. -/
example (c : PicardGroup (dualScheme k X.hom)) :
    ((fppfPicardSheaf X.hom).obj.map (closedPointOver k).op).hom (toFppfDualNumbers X c) =
      toFppfClosedFibre X (pullbackHom (inclusion k X.hom) c) :=
  fppfPicardSheaf_map_closedPointOver_toFppfDualNumbers X c

example (a : k) (c : PicardGroup (dualScheme k X.hom)) :
    ((fppfPicardSheaf X.hom).obj.map (scaleOver k a).op).hom (toFppfDualNumbers X c) =
      toFppfDualNumbers X (pullbackHom (dualScale k X.hom a) c) :=
  fppfPicardSheaf_map_scaleOver_toFppfDualNumbers X a c

example (c : (pullbackHom (inclusion k X.hom)).ker) :
    (picardKerToFppf X c : (fppfPicardSheaf X.hom).obj.obj (op (Over.mk (dualMap k)))) =
      toFppfDualNumbers X c :=
  coe_picardKerToFppf X c

section Injective

variable [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom]

example : Function.Injective (toFppfDualNumbers X) :=
  toFppfDualNumbers_injective_of_isProper_of_flat_of_geometricallyIntegral X

example : Function.Injective (toFppfClosedFibre X) :=
  toFppfClosedFibre_injective_of_isProper_of_flat_of_geometricallyIntegral X

example : Function.Injective (picardKerToFppf X) :=
  picardKerToFppf_injective_of_isProper_of_flat_of_geometricallyIntegral X

end Injective

section Section

variable [IsSplitEpi X.hom] [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom]

example : Function.Bijective (toFppfDualNumbers X) :=
  toFppfDualNumbers_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral X

example : Function.Bijective (toFppfClosedFibre X) :=
  toFppfClosedFibre_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral X

/-- The equivalence of kernels with a section. -/
example : ((fppfPicardSheaf X.hom).obj.map (closedPointOver k).op).hom.ker ≃+
    (pullbackHom (inclusion k X.hom)).ker :=
  fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral X

/-- Its inverse is the map of horizontal kernels; on a class it is the image in `P_{X/k}(k[ε])`
followed by the unit. -/
example (c : (pullbackHom (inclusion k X.hom)).ker) :
    (fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral X).symm c =
      picardKerToFppf X c :=
  fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral_symm_apply X c

example (c : (pullbackHom (inclusion k X.hom)).ker) :
    ((fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral X).symm c :
        (fppfPicardSheaf X.hom).obj.obj (op (Over.mk (dualMap k)))) =
      ((toFppfPicardSheaf X.hom).app (op (Over.mk (dualMap k)))).hom
        (((quotientProjection X.hom).app (op (Over.mk (dualMap k)))).hom
          (c : PicardGroup (dualScheme k X.hom))) :=
  coe_fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral_symm_apply X c

/-- The equivalence carries `F(µ_a)` to pullback along `dualScale a`. -/
example (a : k) (t : ((fppfPicardSheaf X.hom).obj.map (closedPointOver k).op).hom.ker)
    (h : ((fppfPicardSheaf X.hom).obj.map (scaleOver k a).op).hom t ∈
      ((fppfPicardSheaf X.hom).obj.map (closedPointOver k).op).hom.ker) :
    fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral X ⟨_, h⟩ =
      dualScaleKer k X.hom a
        (fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral X t) :=
  fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral_map_scaleOver X a t h

example (a : k) (c : (pullbackHom (inclusion k X.hom)).ker) :
    ((fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral X).symm
        (dualScaleKer k X.hom a c) :
        (fppfPicardSheaf X.hom).obj.obj (op (Over.mk (dualMap k)))) =
      ((fppfPicardSheaf X.hom).obj.map (scaleOver k a).op).hom
        ((fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral X).symm c) :=
  fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral_symm_dualScaleKer X a c

end Section

end Field

/--
info: 'AlgebraicGeometry.Scheme.DualNumbers.fppfPicardSheaf_map_closedPointOver_toFppfDualNumbers' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fppfPicardSheaf_map_closedPointOver_toFppfDualNumbers

/--
info: 'AlgebraicGeometry.Scheme.DualNumbers.picardKerToFppf_injective_of_isProper_of_flat_of_geometricallyIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms picardKerToFppf_injective_of_isProper_of_flat_of_geometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.DualNumbers.fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.DualNumbers.fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral_map_scaleOver' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral_map_scaleOver
