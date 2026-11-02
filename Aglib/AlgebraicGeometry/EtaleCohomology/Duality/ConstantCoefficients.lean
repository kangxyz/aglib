/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ModuleUnitUnderlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.ZMod
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.HenselianConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootsOfUnity
public import Aglib.AlgebraicGeometry.EtaleCohomology.H0.ConnectedConstantValues
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.ZModLinear
public import Aglib.Algebra.Category.Grp.ZModEndomorphisms
public import Aglib.Algebra.Homology.DerivedCategory.Ext.PairingZero
public import Aglib.CategoryTheory.Adjunction.Unit
public import Mathlib.CategoryTheory.HomCongr

/-!
# Original constant coefficients for curve duality

The existing constant-root isomorphism lifts through the existing full scalar
forgetting functor to an isomorphism of the original unit and roots module sheaves.
On a connected scheme, the original constant-adjunction unit identifies every
unit endomorphism with a unique ZMod scalar. This requires no properness and
makes no assertion that regular functions on an open curve are constant.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u w w'

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients GroupCohomology.Kummer.Coefficients

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard moduleSheafExtZModModule

section Roots

variable (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ) (hn : 0 < n)
  (hunit : IsUnit (n : k)) {U : Scheme.{u}} (p : U ⟶ Spec (.of k))

/-- The existing constant-root isomorphism, lifted to the original module sheaves. -/
def moduleUnitRootsIso :
    moduleUnit U (ULift.{u + 1} (ZMod n)) ≅ moduleRootsOfUnity U n :=
  haveI : IsSepClosed (IsLocalRing.ResidueField k) :=
    Algebra.IsAlgebraic.isSepClosed (F := k) (E := IsLocalRing.ResidueField k)
  letI := moduleSheaf_uLiftZMod_toSheaf_full U n
  (SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).preimageIso
    ((moduleUnitCoefficientIso U n).symm ≪≫
      Kummer.HenselianConstant.constantRootIsoOver k n hn
        (by simpa only [map_natCast] using hunit.map (Scheme.ΓSpecIso (.of k)).inv.hom) p ≪≫
      (moduleRootsOfUnityUnderlyingIso U n).symm)

/-- The full coefficient comparison retains exactly the original constant-root map underneath. -/
theorem moduleUnitRootsIso_underlying :
    (SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))).map
        (moduleUnitRootsIso k n hn hunit p).hom ≫
      (moduleRootsOfUnityUnderlyingIso U n).hom =
      (moduleUnitCoefficientIso U n).inv ≫
        (by
          haveI : IsSepClosed (IsLocalRing.ResidueField k) :=
            Algebra.IsAlgebraic.isSepClosed (F := k) (E := IsLocalRing.ResidueField k)
          exact (Kummer.HenselianConstant.constantRootIsoOver k n hn
            (by simpa only [map_natCast] using
              hunit.map (Scheme.ΓSpecIso (.of k)).inv.hom) p).hom) := by
  let := moduleSheaf_uLiftZMod_toSheaf_full U n
  simp only [moduleUnitRootsIso, Functor.preimageIso_hom, Functor.map_preimage,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Roots

section ScalarUnit

variable (U : Scheme.{u}) (n : ℕ) [NeZero n]

/-- Every original endomorphism of the constant unit is a unique cyclic scalar. -/
theorem moduleUnit_nsmul_id_bijective [ConnectedSpace U] :
    Function.Bijective (fun a : ZMod n =>
      a.val • 𝟙 (moduleUnit U (ULift.{u + 1} (ZMod n)))) := by
  let A := AddCommGrpCat.of (ULift.{u + 1} (ZMod n))
  let S := constantSheaf (Scheme.smallEtaleTopology U) AddCommGrpCat.{u + 1}
  let Q := SheafOfModules.toSheaf (constantRing U (ULift.{u + 1} (ZMod n)))
  let e : S.obj A ≅ Q.obj (moduleUnit U (ULift.{u + 1} (ZMod n))) :=
    moduleUnitUnderlyingIso U (ULift.{u + 1} (ZMod n))
  let := moduleSheaf_uLiftZMod_toSheaf_full U n
  let : IsIso ((constantAdjunction U).unit.app A) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (ConstantFinite.constantUnit_bijective_value_of_connected U A)
  have hS : Function.Bijective (S.map : (A ⟶ A) → (S.obj A ⟶ S.obj A)) :=
    (constantAdjunction U).bijective_map_of_isIso_unit_app A A
  have hQ : Function.Bijective
      (Q.map : (moduleUnit U (ULift.{u + 1} (ZMod n)) ⟶
          moduleUnit U (ULift.{u + 1} (ZMod n))) → _) :=
    ⟨Q.map_injective, Q.map_surjective⟩
  have hE := (Iso.homCongr e.symm e.symm).bijective.comp hQ
  apply (Function.Bijective.of_comp_iff' hE _).mp
  convert hS.comp (AddCommGrpCat.uLiftZMod_nsmul_id_bijective.{u + 1} n) using 1
  funext a
  change e.hom ≫ Q.map (a.val • 𝟙 (moduleUnit U (ULift.{u + 1} (ZMod n)))) ≫ e.inv =
    S.map (a.val • 𝟙 A)
  rw [Q.map_nsmul, S.map_nsmul, Q.map_id, S.map_id]
  simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp, Category.id_comp, e.hom_inv_id]

variable [HasExt.{w} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]

/-- Scalars act on the original degree-zero identity through the canonical Ext action. -/
def moduleUnitScalarLinearMap :
    ZMod n →ₗ[ZMod n]
      Ext.{w} (moduleUnit U (ULift.{u + 1} (ZMod n)))
        (moduleUnit U (ULift.{u + 1} (ZMod n))) 0 :=
  LinearMap.smulRight LinearMap.id (Ext.mk₀ (𝟙 _))

omit [NeZero n] in
/-- The scalar-unit map retains the literal identity morphism in Ext degree zero. -/
@[simp]
theorem moduleUnitScalarLinearMap_apply (a : ZMod n) :
    moduleUnitScalarLinearMap U n a = a • Ext.mk₀ (𝟙 _) := rfl

/-- The canonical scalar action agrees with the original multiple of the identity morphism. -/
theorem moduleUnitScalarLinearMap_apply_eq_mk₀_nsmul (a : ZMod n) :
    moduleUnitScalarLinearMap U n a =
      Ext.mk₀ (a.val • 𝟙 (moduleUnit U (ULift.{u + 1} (ZMod n)))) := by
  rw [moduleUnitScalarLinearMap_apply, Ext.mk₀_nsmul]
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  rw [Nat.cast_smul_eq_nsmul]

/-- On a connected scheme the original scalar-unit map is bijective. -/
theorem moduleUnitScalarLinearMap_bijective [ConnectedSpace U] :
    Function.Bijective (moduleUnitScalarLinearMap U n) := by
  have h := (Ext.mk₀_bijective (moduleUnit U (ULift.{u + 1} (ZMod n)))
    (moduleUnit U (ULift.{u + 1} (ZMod n)))).comp (moduleUnit_nsmul_id_bijective U n)
  have he : ⇑(moduleUnitScalarLinearMap U n) = fun a =>
      Ext.mk₀ (a.val • 𝟙 (moduleUnit U (ULift.{u + 1} (ZMod n)))) :=
    funext (moduleUnitScalarLinearMap_apply_eq_mk₀_nsmul U n)
  rw [he]
  exact h

/-- An original coefficient isomorphism transports the unique scalar identity generator. -/
theorem moduleUnitIsoScalarMap_bijective [ConnectedSpace U]
    {G : ModuleSheaf U (ULift.{u + 1} (ZMod n))}
    (e : moduleUnit U (ULift.{u + 1} (ZMod n)) ≅ G) :
    Function.Bijective (fun a : ZMod n => a • Ext.mk₀ e.hom) := by
  let E : Ext.{w} (moduleUnit U (ULift.{u + 1} (ZMod n)))
      (moduleUnit U (ULift.{u + 1} (ZMod n))) 0 ≃+
        Ext.{w} (moduleUnit U (ULift.{u + 1} (ZMod n))) G 0 :=
    ((extFunctorObj (moduleUnit U (ULift.{u + 1} (ZMod n))) 0).mapIso
      e).addCommGroupIsoToAddEquiv
  have h := E.bijective.comp (moduleUnitScalarLinearMap_bijective U n)
  have he : (fun a : ZMod n => a • Ext.mk₀ e.hom) = E ∘ moduleUnitScalarLinearMap U n := by
    funext a
    change a • Ext.mk₀ e.hom =
      E (a • Ext.mk₀ (𝟙 (moduleUnit U (ULift.{u + 1} (ZMod n)))))
    rw [ZMod.map_smul E]
    change a • Ext.mk₀ e.hom =
      a • (Ext.mk₀ (𝟙 (moduleUnit U (ULift.{u + 1} (ZMod n))))).comp
        (Ext.mk₀ e.hom) (add_zero 0)
    rw [Ext.mk₀_id_comp]
  rw [he]
  exact h

/-- The whole original module/cohomology comparison sends scalar identities to
the same multiples of the original integer-to-unit map. -/
theorem moduleUnitScalarLinearMap_cohomology
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} U)] :
    (etaleModuleExtCohomologyAddEquivLargeScalars U
      (constantRing U (ULift.{u + 1} (ZMod n)))
      (moduleUnit U (ULift.{u + 1} (ZMod n))) 0) ∘ moduleUnitScalarLinearMap U n =
      fun a : ZMod n => a.val • (Ext.mk₀
        (Sheaf.ModuleCoefficients.liftedUnitIntegerMap terminalIsTerminal
          (constantRing U (ULift.{u + 1} (ZMod n)))) :
        Sheaf.H.{w'} ((SheafOfModules.toSheaf
          (constantRing U (ULift.{u + 1} (ZMod n)))).obj
            (moduleUnit U (ULift.{u + 1} (ZMod n)))) 0) := by
  funext a
  erw [Function.comp_apply, moduleUnitScalarLinearMap_apply_eq_mk₀_nsmul,
    moduleUnitExtAddEquiv_mk₀]
  erw [Functor.map_nsmul, CategoryTheory.Functor.map_id,
    Preadditive.comp_nsmul, Category.comp_id, Ext.mk₀_nsmul]

end ScalarUnit

end AlgebraicGeometry.Scheme.EtaleCohomology
