/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AffineCenter.Stalk
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.StalkKernel
public import Aglib.AlgebraicGeometry.FunctionField.StalkInjection

/-!
# The exact kernel of an original affine ideal on a dominant integral model

An actual nonzero element of the original ideal gives a nonzero original
base-stalk germ. The genuine dominant stalk map keeps it nonzero. This
supplies the regular-image hypothesis of the existing actual-stalk theorem,
without any Noetherianity, normality, properness or dimension premise.
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Blowup

variable {A : Type u} [CommRing A] [IsDomain A] (J : Ideal A) (hJ : J ≠ ⊥)
  {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ Spec (.of A)) [IsDominant f] (y : Y)

include hJ in
private theorem exists_regular_image_affineIdealStalk :
    ∃ c : (affineCenter A J).subschemeι.ker.stalkIdeal (f y),
      IsRegular ((f.stalkMap y).hom (c : (Spec (.of A)).presheaf.stalk (f y))) := by
  obtain ⟨c, hc, hne⟩ := (Submodule.ne_bot_iff J).mp hJ
  have hmem : (StructureSheaf.toStalk A (f y)).hom c ∈
      (affineCenter A J).subschemeι.ker.stalkIdeal (f y) := by
    rw [(affineCenter A J).ker_subschemeι, affineCenter_stalkIdeal]
    exact Ideal.mem_map_of_mem (StructureSheaf.toStalk A (f y)).hom hc
  let : (f y).asIdeal.IsPrime := (f y).isPrime
  let : Algebra A ((Spec (.of A)).presheaf.stalk (f y)) :=
    StructureSheaf.stalkAlgebra A (f y)
  let : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk (f y)) (f y).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A (f y)
  have hinj : Function.Injective (StructureSheaf.toStalk A (f y)).hom :=
    IsLocalization.injective ((Spec (.of A)).presheaf.stalk (f y))
      (f y).asIdeal.primeCompl_le_nonZeroDivisors
  refine ⟨⟨(StructureSheaf.toStalk A (f y)).hom c, hmem⟩, IsRegular.of_ne_zero ?_⟩
  intro hz
  apply hne
  have hz' : (StructureSheaf.toStalk A (f y)).hom c = 0 :=
    f.stalkMap_injective_of_isDominant y
      (hz.trans ((f.stalkMap y).hom.map_zero).symm)
  exact hinj (hz'.trans ((StructureSheaf.toStalk A (f y)).hom.map_zero).symm)

include hJ in
/-- The existing affine-ideal pullback-to-unit map has exactly its original
source stalk's torsion kernel on an arbitrary dominant integral model. -/
theorem affineCenter_pullbackToUnit_stalk_ker_eq_torsion :
    LinearMap.ker ((moduleStalk Y y).map ((affineCenter A J).pullbackIdealToUnit f)).hom =
      Submodule.torsion (Y.presheaf.stalk y)
        ((moduleStalk Y y).obj
          ((Modules.pullback f).obj (idealModule (affineCenter A J).subschemeι))) := by
  obtain ⟨c, hc⟩ := exists_regular_image_affineIdealStalk J hJ f y
  exact (affineCenter A J).pullbackIdealToUnit_stalk_ker_eq_torsion f y c hc

include hJ in
/-- The SAME original image-factorization epi has precisely that torsion
kernel. Its image is not asserted invertible by this theorem. -/
theorem affineCenter_pullbackImage_stalk_ker_eq_torsion :
    LinearMap.ker
        ((moduleStalk Y y).map ((affineCenter A J).pullbackIdealMonoFactorisation f).e).hom =
      Submodule.torsion (Y.presheaf.stalk y)
        ((moduleStalk Y y).obj
          ((Modules.pullback f).obj (idealModule (affineCenter A J).subschemeι))) := by
  obtain ⟨c, hc⟩ := exists_regular_image_affineIdealStalk J hJ f y
  exact (affineCenter A J).pullbackIdealImage_stalk_ker_eq_torsion f y c hc

end AlgebraicGeometry.Scheme.Blowup
