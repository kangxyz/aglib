/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.CechAcyclic
public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.LiftedUnit
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.Comparison

/-!
# Original lifted-unit Ext acyclicity for injective internal-Hom targets

The proved Cech acyclicity of the underlying internal Hom is transferred through
the one existing module-unit/sheaf-cohomology comparison. This gives the actual
injective-image Ext premise of the left-exact comparison, for arbitrary source
module sheaves. The same original Hom and unit maps give the unconditional
degree-zero Ext/cohomology comparison. Neither local Ext vanishing nor an
all-degree comparison for a noninjective target is assumed or asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe c h eM eA

namespace SheafOfModules.InternalHom

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c h} RingCat.{max c h})]
  (R : Sheaf J CommRingCat.{max c h}) [HasSheafify J AddCommGrpCat.{max c h}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c h}]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max c h})]
  [∀ W : C, HasFiniteProducts (Over W)]
  [HasExt.{eM} (SheafOfModulesOfCommRing R)]
  [HasExt.{eA} (Sheaf J AddCommGrpCat.{max c h})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max c h})]
  {T : C} (hT : IsTerminal T)

include hT in
/-- Lifted-unit Ext of internal Hom into an injective vanishes in positive degree. -/
theorem ext_subsingleton_of_injective (M I : SheafOfModulesOfCommRing R)
    [Injective I] (q : ℕ) :
    Subsingleton (Ext.{eM}
      (SheafOfModules.liftedUnit.{c, h, max c h, max c h}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) (sheaf R M I) (q + 1)) := by
  let := cohomology_subsingleton_of_injective R M I hT q
  exact (CategoryTheory.Sheaf.ModuleCoefficients.moduleExtCohomologyAddEquivLargeScalars
    hT ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
    (sheaf R M I) (q + 1)).injective.subsingleton

/-- Degree-zero original Ext is original cohomology of the same internal-Hom coefficient. -/
def extZeroCohomologyAddEquiv (M N : SheafOfModulesOfCommRing R) :
    Ext.{eM} M N 0 ≃+
      CategoryTheory.Sheaf.H.{eA}
        ((SheafOfModules.toSheaf ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)).obj
          (sheaf R M N)) 0 :=
  Ext.addEquiv₀.trans
    ((((liftedUnitCoyonedaIso.{c, h, 0} R M).symm.app N).addCommGroupIsoToAddEquiv.trans
      Ext.addEquiv₀.symm).trans
      (CategoryTheory.Sheaf.ModuleCoefficients.moduleExtCohomologyAddEquivLargeScalars
        hT ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (sheaf R M N) 0))

/-- The degree-zero comparison retains the original lifted-unit Hom arrow and forgetting map. -/
theorem extZeroCohomologyAddEquiv_mk₀ (M N : SheafOfModulesOfCommRing R) (f : M ⟶ N) :
    extZeroCohomologyAddEquiv R hT M N (Ext.mk₀ f) =
      CategoryTheory.Sheaf.ModuleCoefficients.cohomologyMap hT
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (sheaf R M N) 0
        (Ext.mk₀ ((liftedUnitCoyonedaIso.{c, h, 0} R M).inv.app N f)) := by
  change CategoryTheory.Sheaf.ModuleCoefficients.cohomologyMap hT _ _ 0
    (Ext.mk₀ ((liftedUnitCoyonedaIso.{c, h, 0} R M).inv.app N (Ext.addEquiv₀ (Ext.mk₀ f)))) = _
  rw [show Ext.addEquiv₀ (Ext.mk₀ f) = f from
    (Ext.addEquiv₀ (X := M) (Y := N)).apply_symm_apply f]
  rfl

end SheafOfModules.InternalHom
