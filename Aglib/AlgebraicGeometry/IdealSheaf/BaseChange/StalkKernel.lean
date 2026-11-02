/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.QuotientModule
public import Aglib.AlgebraicGeometry.IdealSheaf.Modules.Stalk
public import Aglib.AlgebraicGeometry.Modules.Pullback.StalkUnit
public import Aglib.RingTheory.Ideal.ScalarExtensionKernel

/-!
# The exact torsion kernel on the original pulled-back ideal stalk

The native pullback/stalk comparison and the original ideal-stalk equivalence
identify the existing pullback-to-unit map with the existing tensor inclusion.
Its exact kernel is torsion when one actual ideal-stalk element has regular
image under the original stalk map. No flatness, domain, finite-type,
Noetherianity, normality, dimension or canonical-module premise is added.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open TensorProduct
open scoped ChangeOfRings nonZeroDivisors
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X) (y : Y)

local instance : Algebra (X.presheaf.stalk (f y)) (Y.presheaf.stalk y) :=
  (f.stalkMap y).hom.toAlgebra

/-- The original pullback stalk, through the native scalar extension and the
original ideal-stalk comparison, is the tensor of the actual stalk ideal. -/
def pullbackIdealStalkTensorIso :
    (moduleStalk Y y).obj ((Modules.pullback f).obj (idealModule I.subschemeι)) ≅
      ModuleCat.of (Y.presheaf.stalk y)
        ((Y.presheaf.stalk y) ⊗[X.presheaf.stalk (f y)]
          I.subschemeι.ker.stalkIdeal (f y)) :=
  (pullbackModuleStalkIso f y).app (idealModule I.subschemeι) ≪≫
    (ModuleCat.extendScalars (f.stalkMap y).hom).mapIso
      (idealModuleStalkEquiv I.subschemeι (f y)).toModuleIso ≪≫
    ModuleCat.extendScalarsAlgebraIso (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)
      (ModuleCat.of (X.presheaf.stalk (f y)) (I.subschemeι.ker.stalkIdeal (f y)))

private theorem pullbackIdealToUnit_unit_apply
    (U : X.Opens) (s : Γ(idealModule I.subschemeι, U)) :
    (I.pullbackIdealToUnit f).app (f ⁻¹ᵁ U)
      (((pullbackPushforwardAdjunction f).unit.app (idealModule I.subschemeι)).app U s) =
        f.app U ((idealInclusion I.subschemeι).app U s) := by
  let a := subschemeMap (I.comap f) I f (I.le_map_comap f)
  let h := subschemeMap_subschemeι (I.comap f) I f (I.le_map_comap f)
  have hv := idealInclusion_idealPullbackMap_unit_apply I.subschemeι
    (I.comap f).subschemeι f a h U s
  have hf := idealPullbackMap_inclusion I.subschemeι (I.comap f).subschemeι f a h
  change _ ≫ _ = I.pullbackIdealToUnit f at hf
  have he := congrArg (fun q => q.app (f ⁻¹ᵁ U)
    (((pullbackPushforwardAdjunction f).unit.app (idealModule I.subschemeι)).app U s)) hf
  exact he.symm.trans hv

/-- The square concerns the ORIGINAL pullback-to-unit arrow, not an assumed
compatibility or a replacement image map. -/
theorem pullbackIdealToUnit_stalk_square :
    (moduleStalk Y y).map (I.pullbackIdealToUnit f) ≫
        (unitModuleStalkEquiv Y y).toModuleIso.hom =
      (I.pullbackIdealStalkTensorIso f y).hom ≫
        ModuleCat.ofHom (Algebra.extendedIdealInclusion
          (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)
          (I.subschemeι.ker.stalkIdeal (f y))) := by
  let E := (pullbackModuleStalkIso f y).app (idealModule I.subschemeι)
  apply (cancel_epi E.inv).mp
  simp only [E, pullbackIdealStalkTensorIso, Iso.trans_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  obtain ⟨U, hy, s, rfl⟩ := (idealModule I.subschemeι).presheaf.exists_germ_eq m
  have hu := pullbackModuleStalkIso_unit_germ f y (idealModule I.subschemeι) U hy s
  have hi : E.inv ((1 : Y.presheaf.stalk y) ⊗ₜ[X.presheaf.stalk (f y),
      (f.stalkMap y).hom] (idealModule I.subschemeι).presheaf.germ U (f y) hy s) =
      ((Modules.pullback f).obj (idealModule I.subschemeι)).presheaf.germ (f ⁻¹ᵁ U) y hy
        (((pullbackPushforwardAdjunction f).unit.app (idealModule I.subschemeι)).app U s) :=
    E.toLinearEquiv.symm_apply_eq.mpr hu.symm
  simp only [ConcreteCategory.comp_apply, Functor.mapIso_hom]
  have hleft := congrArg (fun z => unitModuleStalkEquiv Y y
    (((moduleStalk Y y).map (I.pullbackIdealToUnit f)) z)) hi
  have hmap := TopCat.Presheaf.stalkFunctor_map_germ_apply (f ⁻¹ᵁ U) y hy
    (I.pullbackIdealToUnit f).mapPresheaf
    (((pullbackPushforwardAdjunction f).unit.app (idealModule I.subschemeι)).app U s)
  have hgerm := unitModuleStalkEquiv_germ Y y (f ⁻¹ᵁ U) hy
    ((I.pullbackIdealToUnit f).app (f ⁻¹ᵁ U)
      (((pullbackPushforwardAdjunction f).unit.app (idealModule I.subschemeι)).app U s))
  have hvalue := congrArg (Y.presheaf.germ (f ⁻¹ᵁ U) y hy)
    (I.pullbackIdealToUnit_unit_apply f U s)
  have hscalar := f.germ_stalkMap_apply U y hy ((idealInclusion I.subschemeι).app U s)
  have hright : Algebra.extendedIdealInclusion
      (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)
      (I.subschemeι.ker.stalkIdeal (f y))
      ((ModuleCat.extendScalarsAlgebraIso (X.presheaf.stalk (f y))
        (Y.presheaf.stalk y)
        (ModuleCat.of (X.presheaf.stalk (f y))
          (I.subschemeι.ker.stalkIdeal (f y)))).hom
        (((ModuleCat.extendScalars (f.stalkMap y).hom).map
          (idealModuleStalkEquiv I.subschemeι (f y)).toModuleIso.hom)
          ((1 : Y.presheaf.stalk y) ⊗ₜ[X.presheaf.stalk (f y), (f.stalkMap y).hom]
            (idealModule I.subschemeι).presheaf.germ U (f y) hy s))) =
      (f.stalkMap y).hom (idealModuleStalkEquiv I.subschemeι (f y)
        ((idealModule I.subschemeι).presheaf.germ U (f y) hy s) :
          X.presheaf.stalk (f y)) := by
    rw [ModuleCat.ExtendScalars.map_tmul, ModuleCat.extendScalarsAlgebraIso_tmul,
      Algebra.extendedIdealInclusion_tmul, Algebra.smul_def, mul_one]
    rfl
  have hideal := idealModuleStalkEquiv_germ_val I.subschemeι (f y) U hy s
  exact hleft.trans ((congrArg (unitModuleStalkEquiv Y y) hmap).trans
    (hgerm.trans (hvalue.trans (hscalar.symm.trans
      (hright.trans (congrArg (f.stalkMap y).hom hideal)).symm))))

/-- A regular image of an actual ideal-stalk element gives the exact torsion
kernel of the original pulled-back ideal inclusion on that same stalk. -/
theorem pullbackIdealToUnit_stalk_ker_eq_torsion
    (c : I.subschemeι.ker.stalkIdeal (f y))
    (hc : IsRegular ((f.stalkMap y).hom (c : X.presheaf.stalk (f y)))) :
    LinearMap.ker ((moduleStalk Y y).map (I.pullbackIdealToUnit f)).hom =
      Submodule.torsion (Y.presheaf.stalk y)
        ((moduleStalk Y y).obj ((Modules.pullback f).obj (idealModule I.subschemeι))) := by
  let E := (I.pullbackIdealStalkTensorIso f y).toLinearEquiv
  have hs := I.pullbackIdealToUnit_stalk_square f y
  have hk := Algebra.extendedIdealInclusion_ker_eq_torsion
    (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)
    (I.subschemeι.ker.stalkIdeal (f y)) c hc
  ext z
  change ((moduleStalk Y y).map (I.pullbackIdealToUnit f)) z = 0 ↔ _
  have hz : ((moduleStalk Y y).map (I.pullbackIdealToUnit f)) z = 0 ↔
      Algebra.extendedIdealInclusion (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)
        (I.subschemeι.ker.stalkIdeal (f y)) (E z) = 0 := by
    have hv := ConcreteCategory.congr_hom hs z
    change unitModuleStalkEquiv Y y
      (((moduleStalk Y y).map (I.pullbackIdealToUnit f)) z) =
        Algebra.extendedIdealInclusion (X.presheaf.stalk (f y)) (Y.presheaf.stalk y)
          (I.subschemeι.ker.stalkIdeal (f y)) (E z) at hv
    rw [← hv]
    exact (unitModuleStalkEquiv Y y).map_eq_zero_iff.symm
  rw [hz, ← LinearMap.mem_ker, hk]
  constructor
  · intro hz
    obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff (E z)).mp hz
    refine (Submodule.mem_torsion_iff z).mpr ⟨r, ?_⟩
    apply E.injective
    exact (E.map_smul (r : Y.presheaf.stalk y) z).trans (hr.trans E.map_zero.symm)
  · intro hz
    obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff z).mp hz
    refine (Submodule.mem_torsion_iff (E z)).mpr ⟨r, ?_⟩
    exact (E.map_smul (r : Y.presheaf.stalk y) z).symm.trans
      ((congrArg E hr).trans E.map_zero)

/-- The existing epi part of the original image factorization has the same
exact torsion kernel; no monicity of the full pullback is asserted. -/
theorem pullbackIdealImage_stalk_ker_eq_torsion
    (c : I.subschemeι.ker.stalkIdeal (f y))
    (hc : IsRegular ((f.stalkMap y).hom (c : X.presheaf.stalk (f y)))) :
    LinearMap.ker ((moduleStalk Y y).map (I.pullbackIdealMonoFactorisation f).e).hom =
      Submodule.torsion (Y.presheaf.stalk y)
        ((moduleStalk Y y).obj ((Modules.pullback f).obj (idealModule I.subschemeι))) := by
  rw [← I.pullbackIdealToUnit_stalk_ker_eq_torsion f y c hc]
  ext z
  change ((moduleStalk Y y).map (I.pullbackIdealMonoFactorisation f).e) z = 0 ↔
    ((moduleStalk Y y).map (I.pullbackIdealToUnit f)) z = 0
  have hi := (ModuleCat.mono_iff_injective
    ((moduleStalk Y y).map (I.pullbackIdealMonoFactorisation f).m)).mp inferInstance
  have hf := congrArg (fun q => (moduleStalk Y y).map q)
    (I.pullbackIdealMonoFactorisation f).fac
  rw [Functor.map_comp] at hf
  rw [← hf, ConcreteCategory.comp_apply]
  exact (map_eq_zero_iff _ hi).symm

end AlgebraicGeometry.Scheme.IdealSheafData
