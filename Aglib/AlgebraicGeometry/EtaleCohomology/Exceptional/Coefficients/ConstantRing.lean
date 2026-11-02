/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.Basic
public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Basic
public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Ringed.Equivalence

/-!
# Arbitrary constant-ring modules on the small étale site

The coefficient ring and section modules live in the standard value universe
`u + 1` for a scheme in universe `u`. No torsion, finiteness, or Noetherian
hypothesis is imposed. In particular, every commutative ring at this size is
allowed; the constructions only require a ring.

The equivalence is the composite of the existing constant-presheaf module
conversion and native module sheafification. Its underlying comparison is the
original abelian sheafification counit, not a new scalar-forgetting functor.
The arbitrary-ring implementations live in the general constant-ring owner.
The historical names remain available for compatibility with existing clients.
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits
open CategoryTheory.TorsionZMod.Ringed

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

attribute [local instance] hasSheafifyRingStandard hasSheafifyAbStandard
  ringWEqualsLocallyBijectiveStandard abWEqualsLocallyBijectiveStandard

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]

/-- The actual associated constant ring sheaf on the small étale site. -/
def constantRing : Sheaf (Scheme.smallEtaleTopology X) RingCat.{u + 1} :=
  ModuleCat.Sheaf.ConstantRing.constantRing (Scheme.smallEtaleTopology X) Λ

/-- The original unit from the constant ring presheaf to its associated sheaf. -/
abbrev constantRingUnit :
    (Functor.const X.Etaleᵒᵖ).obj (RingCat.of Λ) ⟶ (constantRing X Λ).obj :=
  ModuleCat.Sheaf.ConstantRing.constantRingUnit (Scheme.smallEtaleTopology X) Λ

instance constantRingUnit_isLocallyInjective :
    Presheaf.IsLocallyInjective
    (Scheme.smallEtaleTopology X) (constantRingUnit X Λ) := by
  exact ModuleCat.Sheaf.ConstantRing.constantRingUnit_isLocallyInjective
    (Scheme.smallEtaleTopology X) Λ

instance constantRingUnit_isLocallySurjective :
    Presheaf.IsLocallySurjective
    (Scheme.smallEtaleTopology X) (constantRingUnit X Λ) := by
  exact ModuleCat.Sheaf.ConstantRing.constantRingUnit_isLocallySurjective
    (Scheme.smallEtaleTopology X) Λ

/-- Genuine native modules over the actual constant ring sheaf. -/
abbrev ModuleSheaf := SheafOfModules.{u + 1} (constantRing X Λ)

/-- Module-valued sheaves, used only through their canonical ringed equivalence. -/
abbrev ModuleValuedSheaf := Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ)

/-- Native module sheafification over the original constant-ring unit. -/
def constantModuleSheafificationEquivalence :
    (moduleSheafProperty.{u + 1, u, u + 1, u + 1} (Scheme.smallEtaleTopology X)
      ((Functor.const X.Etaleᵒᵖ).obj (RingCat.of Λ))).FullSubcategory ≌ ModuleSheaf X Λ :=
  ModuleCat.Sheaf.ConstantRing.constantModuleSheafificationEquivalence.{
    u + 1, u, u + 1, u + 1}
    (Scheme.smallEtaleTopology X) Λ

/-- The actual equivalence between module-valued and genuine constant-ring module sheaves. -/
def moduleSheafEquivalence : ModuleValuedSheaf X Λ ≌ ModuleSheaf X Λ :=
  ModuleCat.Sheaf.ConstantRing.moduleSheafEquivalence.{
    u + 1, u, u + 1, u + 1} (Scheme.smallEtaleTopology X) Λ

/-- The native abelian-sheafification counit in the ringed-module bridge. -/
def constantModuleSheafificationUnderlyingIso :
    (constantModuleSheafificationEquivalence X Λ).functor ⋙
      SheafOfModules.toSheaf (constantRing X Λ) ≅
    moduleUnderlyingSheaf.{u + 1, u, u + 1, u + 1} (Scheme.smallEtaleTopology X)
      ((Functor.const X.Etaleᵒᵖ).obj (RingCat.of Λ)) :=
  ModuleCat.Sheaf.ConstantRing.constantModuleSheafificationUnderlyingIso.{
    u + 1, u, u + 1, u + 1}
    (Scheme.smallEtaleTopology X) Λ

/-- The equivalence retains the original underlying abelian sheaf naturally. -/
def moduleSheafUnderlyingIso :
    (moduleSheafEquivalence X Λ).functor ⋙ SheafOfModules.toSheaf (constantRing X Λ) ≅
      sheafCompose (Scheme.smallEtaleTopology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  ModuleCat.Sheaf.ConstantRing.moduleSheafUnderlyingIso.{
    u + 1, u, u + 1, u + 1} (Scheme.smallEtaleTopology X) Λ

/-- The original native module unit is normalized by the actual underlying comparison. -/
@[reassoc]
theorem constantModuleUnit_underlying_comparison
    (M : (moduleSheafProperty.{u + 1, u, u + 1, u + 1} (Scheme.smallEtaleTopology X)
      ((Functor.const X.Etaleᵒᵖ).obj (RingCat.of Λ))).FullSubcategory) :
    (PresheafOfModules.toPresheaf _).map
        ((PresheafOfModules.sheafificationAdjunction (constantRingUnit X Λ)).unit.app M.obj) ≫
      ((constantModuleSheafificationUnderlyingIso X Λ).hom.app M).hom =
        𝟙 M.obj.presheaf :=
  ModuleCat.Sheaf.ConstantRing.constantModuleUnit_underlying_comparison.{
    u + 1, u, u + 1, u + 1}
    (Scheme.smallEtaleTopology X) Λ M

/-- Every coefficient morphism commutes with the original underlying comparison. -/
@[reassoc]
theorem moduleSheafUnderlyingIso_naturality
    {F G : ModuleValuedSheaf X Λ} (f : F ⟶ G) :
    (SheafOfModules.toSheaf (constantRing X Λ)).map
        ((moduleSheafEquivalence X Λ).functor.map f) ≫
      (moduleSheafUnderlyingIso X Λ).hom.app G =
    (moduleSheafUnderlyingIso X Λ).hom.app F ≫
      (sheafCompose (Scheme.smallEtaleTopology X)
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map f :=
  ModuleCat.Sheaf.ConstantRing.moduleSheafUnderlyingIso_naturality.{
    u + 1, u, u + 1, u + 1}
    (Scheme.smallEtaleTopology X) Λ f

/-- The thin realization retains the original associated constant ring sheaf. -/
theorem constantRing_eq_original :
    constantRing X Λ =
      (constantSheaf (Scheme.smallEtaleTopology X) RingCat.{u + 1}).obj (RingCat.of Λ) := rfl

/-- The thin realization retains the original ring sheafification unit. -/
theorem constantRingUnit_eq_original :
    constantRingUnit X Λ = CategoryTheory.toSheafify (Scheme.smallEtaleTopology X)
      ((Functor.const X.Etaleᵒᵖ).obj (RingCat.of Λ)) := rfl

/-- The actual coefficient equivalence retains its original two factors. -/
theorem moduleSheafEquivalence_eq_original :
    moduleSheafEquivalence X Λ =
      (constantSheafEquivalence.{u + 1, u, u + 1, u + 1}
        (Scheme.smallEtaleTopology X) Λ).trans
      (constantModuleSheafificationEquivalence X Λ) := rfl

/-- The original underlying comparison remains the same three-factor isomorphism. -/
theorem moduleSheafUnderlyingIso_eq_original :
    moduleSheafUnderlyingIso X Λ = Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        (constantSheafEquivalence.{u + 1, u, u + 1, u + 1}
          (Scheme.smallEtaleTopology X) Λ).functor
        (constantModuleSheafificationUnderlyingIso X Λ) ≪≫
      constantSheafUnderlyingIso.{u + 1, u, u + 1, u + 1}
        (Scheme.smallEtaleTopology X) Λ := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
