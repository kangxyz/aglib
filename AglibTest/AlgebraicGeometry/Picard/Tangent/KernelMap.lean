/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Tangent.KernelMap

/-! Focused consumer of Kleiman's map `v : H^1(X, 𝒪_X) → ker(Pic_{X/k,(fppf)}(k[ε]) →
Pic_{X/k,(fppf)}(k))` (arXiv:math/0504020v1, proof of Thm 5.11, p. 43): its value, additivity,
linearity for `µ_a`, injectivity (Thm 2.5(1), p. 18) and, with a section, its description through
the kernel comparison of Thm 2.5(2), p. 18. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.DualNumbers
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local

universe u

example (k : Type u) [CommRing k] (a : k) :
    scaleRingHom k a = (TrivSqZeroExt.map (a • LinearMap.id : k →ₗ[k] k)).toRingHom :=
  scaleRingHom_eq_map k a

example (k : Type u) [CommRing k] (a : k) :
    scaleRingHom k a =
      ((TrivSqZeroExt.map (a • LinearMap.id : k →ₗ[k] k)).restrictScalars k).toRingHom :=
  scaleRingHom_eq_restrictScalars_map k a

variable {k : Type u} [Field k] (X : FScheme k) [X.left.IsSeparated] {ι : Type u}
  (U : ι → X.left.Opens) (hU : iSup U = ⊤) (hU₁ : ∀ j, IsAffineOpen (U j))

/-- `v` lands in the kernel of `F(ρ)`. -/
example (c : structureCohomology k X 1) :
    ((fppfPicardSheaf X.hom).obj.map (closedPointOver k).op).hom
      (cohomologyToFppfPicardKer X U hU hU₁ c) = 0 :=
  (cohomologyToFppfPicardKer X U hU hU₁ c).2

example (c : structureCohomology k X 1) :
    (cohomologyToFppfPicardKer X U hU hU₁ c :
        (fppfPicardSheaf X.hom).obj.obj (op (Over.mk (dualMap k)))) =
      toFppfDualNumbers X ((picardKerEquivCech X U hU hU₁).symm c) :=
  coe_cohomologyToFppfPicardKer X U hU hU₁ c

/-- `v` is additive. -/
example (c d : structureCohomology k X 1) :
    cohomologyToFppfPicardKer X U hU hU₁ (c + d) =
      cohomologyToFppfPicardKer X U hU hU₁ c + cohomologyToFppfPicardKer X U hU hU₁ d :=
  map_add _ c d

/-- `v` is linear for `a • t = F(µ_a) t`. -/
example (a : k) (c : structureCohomology k X 1) :
    (cohomologyToFppfPicardKer X U hU hU₁ (a • c) :
        (fppfPicardSheaf X.hom).obj.obj (op (Over.mk (dualMap k)))) =
      ((fppfPicardSheaf X.hom).obj.map (scaleOver k a).op).hom
        (cohomologyToFppfPicardKer X U hU hU₁ c) :=
  cohomologyToFppfPicardKer_smul X U hU hU₁ a c

example [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom] :
    Function.Injective (cohomologyToFppfPicardKer X U hU hU₁) :=
  cohomologyToFppfPicardKer_injective_of_isProper_of_flat_of_geometricallyIntegral X U hU hU₁

example [IsSplitEpi X.hom] [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom]
    (c : structureCohomology k X 1) :
    cohomologyToFppfPicardKer X U hU hU₁ c =
      (fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral X).symm
        ((picardKerEquivCech X U hU hU₁).symm c) :=
  cohomologyToFppfPicardKer_eq_symm_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral X U
    hU hU₁ c

example [IsSplitEpi X.hom] [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom] :
    Function.Bijective (cohomologyToFppfPicardKer X U hU hU₁) :=
  cohomologyToFppfPicardKer_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral X
    U hU hU₁

/--
info: 'AlgebraicGeometry.Scheme.DualNumbers.cohomologyToFppfPicardKer' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cohomologyToFppfPicardKer

/--
info: 'AlgebraicGeometry.Scheme.DualNumbers.cohomologyToFppfPicardKer_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cohomologyToFppfPicardKer_smul

/--
info: 'AlgebraicGeometry.Scheme.DualNumbers.cohomologyToFppfPicardKer_injective_of_isProper_of_flat_of_geometricallyIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cohomologyToFppfPicardKer_injective_of_isProper_of_flat_of_geometricallyIntegral
