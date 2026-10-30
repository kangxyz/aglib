/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.RepresentedTransfer.Module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.EtaleRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.EtaleRepresentedTransfer

/-! # Scalar-linear represented sheaf transfers

Coefficient naturality of the original abelian trace, applied to scalar
multiplication, proves linearity on the original module sections. The native
module restriction comparison returns this trace to the original module
inverse image with its original adjunction unit. No second trace or module
sheaf model is constructed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf.Hypercohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R] {X : Scheme.{u}} (U : X.Etale)
  (a : freeAbelianSheaf.{u + 1} (Scheme.smallEtaleTopology X) (etaleTerminal X) ⟶
    freeAbelianSheaf.{u + 1} (Scheme.smallEtaleTopology X) U)

/-- The original module restriction followed by original direct image. -/
abbrev etaleModuleProductSheaf : ModuleSheaf R X ⥤ ModuleSheaf R X :=
  moduleEtaleRestriction R (X := X) (S := U.left) U.hom ⋙
    moduleDirectImage R (X := X) (S := U.left) U.hom

instance etaleModuleProductSheaf_linear : (etaleModuleProductSheaf R U).Linear R where
  map_smul _ _ := rfl

/-- The existing native direct-image comparisons identify the original
underlying module product coefficient with the original abelian one. -/
def etaleModuleProductUnderlyingIso :
    etaleModuleProductSheaf R U ⋙ moduleUnderlying R X ≅
      moduleUnderlying R X ⋙ etaleProductSheaf U :=
  ModuleCat.Sheaf.continuousCompositeUnderlyingIso.{u + 1, u, r} R X.smallEtaleTopology
    U.left.smallEtaleTopology (siteEtalePostcompose (X := X) (S := U.left) U.hom)
    (siteBaseChange (X := X) (S := U.left) U.hom)

/-- The actual abelian represented trace is linear for every constant scalar ring. -/
def etaleRepresentedModuleRestrictionTrace :
    etaleModuleProductSheaf R U ⟶ 𝟭 (ModuleSheaf R X) :=
  ModuleCat.Sheaf.traceOfUnderlying.{u + 1, u, r} R X.smallEtaleTopology
    (etaleModuleProductSheaf R U) (etaleProductSheaf U)
    (etaleModuleProductUnderlyingIso R U) (etaleRepresentedRestrictionTrace U a)

/-- Forgetting the linear trace gives exactly the original abelian trace after
its native source comparison. -/
@[simp]
theorem etaleRepresentedModuleRestrictionTrace_underlying (F : ModuleSheaf R X) :
    (moduleUnderlying R X).map ((etaleRepresentedModuleRestrictionTrace R U a).app F) =
      (etaleModuleProductUnderlyingIso R U).hom.app F ≫
        (etaleRepresentedRestrictionTrace U a).app ((moduleUnderlying R X).obj F) := by
  rfl

/-- The native coefficient comparison preserves the exact original
restriction-adjunction unit. -/
theorem etaleModuleProductUnderlyingIso_unit (F : ModuleSheaf R X) :
    (moduleUnderlying R X).map
        (((siteEtalePostcomposeAdj (X := X) (S := U.left) U.hom).sheafPushforwardContinuous
          (E := ModuleCat.{u + 1} R) U.left.smallEtaleTopology
          X.smallEtaleTopology).unit.app F) ≫
      (etaleModuleProductUnderlyingIso R U).hom.app F =
    ((siteEtalePostcomposeAdj (X := X) (S := U.left) U.hom).sheafPushforwardContinuous
      (E := AddCommGrpCat.{u + 1}) U.left.smallEtaleTopology
      X.smallEtaleTopology).unit.app ((moduleUnderlying R X).obj F) := by
  exact ModuleCat.Sheaf.continuousCompositeUnderlyingIso_unit.{u + 1, u, r}
    R X.smallEtaleTopology
    U.left.smallEtaleTopology (siteEtalePostcompose (X := X) (S := U.left) U.hom)
    (siteBaseChange (X := X) (S := U.left) U.hom)
    (siteEtalePostcomposeAdj (X := X) (S := U.left) U.hom) F

/-- The linear restriction trace retains the represented rank and actual unit. -/
theorem etaleRepresentedModuleRestrictionTrace_rank (n : ℕ)
    (ha : a ≫ (freeAbelianSheafFunctor.{u + 1} (Scheme.smallEtaleTopology X)).map
      ((etaleTerminalIsTerminal X).from U) = n • 𝟙 _)
    (F : ModuleSheaf R X) :
    ((siteEtalePostcomposeAdj (X := X) (S := U.left) U.hom).sheafPushforwardContinuous
      (E := ModuleCat.{u + 1} R) (Scheme.smallEtaleTopology U.left)
      (Scheme.smallEtaleTopology X)).unit.app F ≫
        (etaleRepresentedModuleRestrictionTrace R U a).app F = n • 𝟙 F := by
  exact ModuleCat.Sheaf.traceOfUnderlying_rank.{u + 1, u, r} R X.smallEtaleTopology
    (etaleModuleProductSheaf R U) (etaleProductSheaf U)
    (etaleModuleProductUnderlyingIso R U) (etaleRepresentedRestrictionTrace U a)
    ((siteEtalePostcomposeAdj (X := X) (S := U.left) U.hom).sheafPushforwardContinuous
      (E := ModuleCat.{u + 1} R) U.left.smallEtaleTopology X.smallEtaleTopology).unit
    ((siteEtalePostcomposeAdj (X := X) (S := U.left) U.hom).sheafPushforwardContinuous
      (E := AddCommGrpCat.{u + 1}) U.left.smallEtaleTopology X.smallEtaleTopology).unit
    n F (etaleModuleProductUnderlyingIso_unit R U F)
    (etaleRepresentedRestrictionTrace_rank U a n ha ((moduleUnderlying R X).obj F))

/-- The scalar-linear trace on the original native module inverse image. -/
def etaleRepresentedModuleTrace :
    moduleInverseImage R (X := X) (S := U.left) U.hom ⋙
      moduleDirectImage R (X := X) (S := U.left) U.hom ⟶ 𝟭 (ModuleSheaf R X) :=
  Adjunction.traceThroughLeftAdjointUniq (moduleImageAdjunction R (X := X) (S := U.left) U.hom)
    ((siteEtalePostcomposeAdj (X := X) (S := U.left) U.hom).sheafPushforwardContinuous
      (E := ModuleCat.{u + 1} R) U.left.smallEtaleTopology X.smallEtaleTopology)
    (etaleRepresentedModuleRestrictionTrace R U a)

/-- The exact original module adjunction unit has composite equal to the represented rank. -/
theorem etaleRepresentedModuleTrace_rank (n : ℕ)
    (ha : a ≫ (freeAbelianSheafFunctor.{u + 1} (Scheme.smallEtaleTopology X)).map
      ((etaleTerminalIsTerminal X).from U) = n • 𝟙 _)
    (F : ModuleSheaf R X) :
    (moduleImageAdjunction R (X := X) (S := U.left) U.hom).unit.app F ≫
      (etaleRepresentedModuleTrace R U a).app F = n • 𝟙 F := by
  exact Adjunction.traceThroughLeftAdjointUniq_rank
    (moduleImageAdjunction R (X := X) (S := U.left) U.hom)
    ((siteEtalePostcomposeAdj (X := X) (S := U.left) U.hom).sheafPushforwardContinuous
      (E := ModuleCat.{u + 1} R) U.left.smallEtaleTopology X.smallEtaleTopology)
    (etaleRepresentedModuleRestrictionTrace R U a) n F
    (etaleRepresentedModuleRestrictionTrace_rank R U a n ha F)

end AlgebraicGeometry.Scheme.EtaleCohomology
