/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ConstantModuleCoefficientFunctor
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ModuleValuedHigherUnderlying
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantActionNatIso
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ConstantModuleScalarSheafification
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ModuleValuedHigherScalar

/-! # Original constant-module cohomology and native higher direct images

The existing native-to-valued comparison and original underlying comparison
identify the original module-valued higher direct image. Scalar naturality
then lifts the existing abelian sheafification comparison to the unchanged
module structures. The original coefficient equivalence returns this whole
natural isomorphism to native ringed modules. No scalar structure is installed
on the native ringed-module category, and no cohomology or derived model is
replaced. All supplied Ext and derived-category universes remain independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w s e wMX wMS wAX wAS

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyRingStandard
  CategoryTheory.TorsionZMod.Ringed.hasSheafifyAbStandard
  CategoryTheory.TorsionZMod.Ringed.ringWEqualsLocallyBijectiveStandard
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

open Coefficients

variable {X S : Scheme.{u}} (f : X ⟶ S) (Λ : Type (u + 1)) [Ring Λ]

attribute [local instance] constantRingModuleSheaf_enoughInjectives
  valuedSheaf_enoughInjectives valuedDirectImage_additive

variable [HasDerivedCategory.{wMX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wMS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wAX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wAS} (AbelianSheaf.{u, u + 1} S)]

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]

/-- The two original abelian comparisons give the precise underlying coefficient map. -/
def constantModuleCohomologyHigherDirectImageUnderlyingIso (q : ℕ) :
    constantModuleCohomologySheafificationFunctor.{u, u + 1, w, s, e} f Λ q ⋙
        ModuleCat.Sheaf.underlying Λ S.smallEtaleTopology ≅
      constantModuleValuedHigherDirectImage f Λ q ⋙
        ModuleCat.Sheaf.underlying Λ S.smallEtaleTopology :=
  constantModuleCohomologySheafificationUnderlyingIso.{u, u + 1, w, s, e} f Λ q ≪≫
    (constantModuleValuedHigherDirectImageUnderlyingIso.{u, wMX, wMS, wAX, wAS} f Λ q).symm

/-- The two original scalar-compatible comparisons give the true relative scalar square. -/
theorem constantModuleCohomologyHigherDirectImageUnderlyingIso_scalar
    (q : ℕ) (M : ModuleCat.{u + 1} Λ) (a : Λ) :
    (ModuleCat.Sheaf.underlyingScalar S.smallEtaleTopology Λ a).app
        ((constantModuleCohomologySheafificationFunctor f Λ q).obj M) ≫
      (constantModuleCohomologyHigherDirectImageUnderlyingIso f Λ q).hom.app M =
    (constantModuleCohomologyHigherDirectImageUnderlyingIso f Λ q).hom.app M ≫
      (ModuleCat.Sheaf.underlyingScalar S.smallEtaleTopology Λ a).app
        ((constantModuleValuedHigherDirectImage f Λ q).obj M) := by
  let E := (constantModuleValuedHigherDirectImageUnderlyingIso f Λ q).app M
  let p := (constantModuleCohomologySheafificationUnderlyingIso f Λ q).hom.app M
  let σ := ModuleCat.Sheaf.underlyingScalar S.smallEtaleTopology Λ a
  have hp := constantModuleCohomologySheafificationUnderlyingIso_scalar f Λ q M a
  have hq := constantModuleValuedHigherDirectImageUnderlyingIso_scalar f Λ q M a
  change σ.app ((constantModuleCohomologySheafificationFunctor f Λ q).obj M) ≫
      (p ≫ E.inv) =
    (p ≫ E.inv) ≫ σ.app ((constantModuleValuedHigherDirectImage f Λ q).obj M)
  apply (cancel_mono E.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change σ.app ((constantModuleValuedHigherDirectImage f Λ q).obj M) ≫ E.hom =
    E.hom ≫ (higherDirectImage f q).map
      ((constantModuleUnderlyingScalar (X := X) Λ a).app M) at hq
  rw [hq, ← Category.assoc E.inv E.hom, Iso.inv_hom_id, Category.id_comp]
  exact hp

/-- Scalar naturality lifts the original underlying isomorphism to the original module actions. -/
def constantModuleCohomologyHigherDirectImageIso (q : ℕ) :
    constantModuleCohomologySheafificationFunctor.{u, u + 1, w, s, e} f Λ q ≅
      constantModuleValuedHigherDirectImage f Λ q :=
  ModuleCat.Sheaf.natIsoOfUnderlyingAction Λ S.smallEtaleTopology _ _
    (constantModuleCohomologyHigherDirectImageUnderlyingIso.{u, w, s, e, wMX, wMS, wAX, wAS}
      f Λ q)
    (constantModuleCohomologyHigherDirectImageUnderlyingIso_scalar f Λ q)

/-- Forgetting the lifted map recovers the original entire abelian comparison. -/
@[simp]
theorem constantModuleCohomologyHigherDirectImageIso_hom_underlying
    (q : ℕ) (M : ModuleCat.{u + 1} Λ) :
    (ModuleCat.Sheaf.underlying Λ S.smallEtaleTopology).map
        ((constantModuleCohomologyHigherDirectImageIso.{u, w, s, e, wMX, wMS, wAX, wAS}
            f Λ q).hom.app M) =
      (constantModuleCohomologyHigherDirectImageUnderlyingIso.{u, w, s, e, wMX, wMS, wAX, wAS}
          f Λ q).hom.app M :=
  rfl

/-- Forgetting the lifted inverse recovers the original inverse abelian comparison. -/
@[simp]
theorem constantModuleCohomologyHigherDirectImageIso_inv_underlying
    (q : ℕ) (M : ModuleCat.{u + 1} Λ) :
    (ModuleCat.Sheaf.underlying Λ S.smallEtaleTopology).map
        ((constantModuleCohomologyHigherDirectImageIso.{u, w, s, e, wMX, wMS, wAX, wAS}
            f Λ q).inv.app M) =
      (constantModuleCohomologyHigherDirectImageUnderlyingIso.{u, w, s, e, wMX, wMS, wAX, wAS}
          f Λ q).inv.app M :=
  rfl

/-- The original sheafification comparison in genuine native constant-ring modules. -/
def constantModuleCohomologyNativeHigherDirectImageIso (q : ℕ) :
    constantModuleCohomologySheafificationFunctor.{u, u + 1, w, s, e} f Λ q ⋙
        (moduleSheafEquivalence S Λ).functor ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        (moduleSheafEquivalence X Λ).functor) ⋙ (moduleDirectImage f Λ).rightDerived q :=
  Functor.isoWhiskerRight
      (constantModuleCohomologyHigherDirectImageIso.{u, w, s, e, wMX, wMS, wAX, wAS} f Λ q)
      (moduleSheafEquivalence S Λ).functor ≪≫
    Functor.associator (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      ((moduleValuedDirectImage f Λ).rightDerived q) (moduleSheafEquivalence S Λ).functor ≪≫
    Functor.isoWhiskerLeft (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (moduleHigherDirectImageNativeComparison f Λ q) ≪≫
    (Functor.associator (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (moduleSheafEquivalence X Λ).functor ((moduleDirectImage f Λ).rightDerived q)).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
