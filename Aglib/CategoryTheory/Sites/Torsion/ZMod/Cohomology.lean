/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Ringed
public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Injectives
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleCoefficients.InjectiveAcyclic
public import Aglib.CategoryTheory.Sites.SheafCohomology.Large.Injectives
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Exact forgetting and original cohomological acyclicity for ZMod sheaves

The actual native module-to-abelian `sheafCompose` functor is exact through
its concrete ringed-module equivalence and original underlying natural
isomorphism. Injective genuine module sheaves therefore have acyclic
original underlying abelian sheaves in the original positive `Sheaf.H`
groups. The latter assertion uses native ringed-module acyclicity and
does not assert preservation of injective objects by scalar forgetting.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TorsionZMod

universe u v e a b

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (n : ℕ)

attribute [local instance] Ringed.hasSheafifyRingStandard Ringed.hasSheafifyAbStandard
  Ringed.abWEqualsLocallyBijectiveStandard

/-- The original genuine-module underlying functor preserves finite limits. -/
theorem underlying_preservesFiniteLimits :
    PreservesFiniteLimits (sheafCompose J
      (forget₂ (ModuleCat.{max u v} (ZMod n)) AddCommGrpCat.{max u v})) := by
  exact preservesFiniteLimits_of_natIso (Ringed.forwardUnderlyingIsoStandard J n)

/-- The same original underlying functor preserves finite colimits. -/
theorem underlying_preservesFiniteColimits :
    PreservesFiniteColimits (sheafCompose J
      (forget₂ (ModuleCat.{max u v} (ZMod n)) AddCommGrpCat.{max u v})) := by
  exact preservesFiniteColimits_of_natIso (Ringed.forwardUnderlyingIsoStandard J n)

variable [HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})]

/-- An actual additive-group isomorphism transports triviality without unfolding
any particular coefficient or cohomology functor. -/
theorem subsingleton_of_additiveIso {A B : AddCommGrpCat.{e}}
    (ι : A ≅ B) (hA : Subsingleton A) : Subsingleton B := by
  refine ⟨fun x y => ?_⟩
  have hxy : ι.inv x = ι.inv y := hA.allEq _ _
  calc
    x = ι.hom (ι.inv x) := (ConcreteCategory.congr_hom ι.inv_hom_id x).symm
    _ = ι.hom (ι.inv y) := congrArg ι.hom hxy
    _ = y := ConcreteCategory.congr_hom ι.inv_hom_id y

/-- The original native cohomology functor transports triviality through
its actual coefficient-isomorphism map. -/
theorem cohomology_subsingleton_of_iso {F G : Sheaf J AddCommGrpCat.{max u v}}
    (ι : F ≅ G) (k : ℕ) (hF : Subsingleton (Sheaf.H.{e} F k)) :
    Subsingleton (Sheaf.H.{e} G k) := by
  let ιH : AddCommGrpCat.of (Sheaf.H.{e} F k) ≅
      AddCommGrpCat.of (Sheaf.H.{e} G k) :=
    (Sheaf.functorH.{e} J k).mapIso ι
  exact subsingleton_of_additiveIso ιH hF

variable [∀ W : C, HasFiniteProducts (Over W)]

/-- The native large-scalar acyclicity supplier with its exact original coefficients. -/
theorem ringed_injective_cohomology_subsingleton
    (R : Sheaf J RingCat.{max u v}) (I : SheafOfModules.{max u v} R) [Injective I]
    {T : C} (hT : IsTerminal T) (k : ℕ) :
    Subsingleton (Sheaf.H.{e} ((SheafOfModules.toSheaf R).obj I) (k + 1)) := by
  let : EnoughInjectives (Sheaf J AddCommGrpCat.{max u v}) :=
    Sheaf.LargeCohomology.enoughInjectivesLarge J
  exact Sheaf.ModuleCoefficients.toSheaf_injective_cohomology_subsingleton_largeScalars
    R I hT k

/-- Transport the native ringed-module acyclicity theorem through an actual
coefficient equivalence and its specified original underlying natural isomorphism. -/
theorem cohomology_subsingleton_of_ringedEquivalence
    {D : Type a} [Category.{b} D] (R : Sheaf J RingCat.{max u v})
    (E : D ≌ SheafOfModules.{max u v} R) (U : D ⥤ Sheaf J AddCommGrpCat.{max u v})
    (η : E.functor ⋙ SheafOfModules.toSheaf R ≅ U)
    (I : D) [Injective I] {T : C} (hT : IsTerminal T) (k : ℕ) :
    Subsingleton (Sheaf.H.{e} (U.obj I) (k + 1)) := by
  let : Injective (E.functor.obj I) :=
    E.functor.injective_obj_of_injective (inferInstance : Injective I)
  exact cohomology_subsingleton_of_iso J (η.app I) (k + 1)
    (ringed_injective_cohomology_subsingleton J R (E.functor.obj I) hT k)

/-- Every injective genuine module sheaf has acyclic original underlying abelian
coefficients, with the independent original Ext universe retained. -/
theorem underlying_injective_cohomology_subsingleton
    (I : Sheaf J (ModuleCat.{max u v} (ZMod n))) [Injective I]
    {T : C} (hT : IsTerminal T) (k : ℕ) :
    Subsingleton (Sheaf.H.{e} ((sheafCompose J
      (forget₂ (ModuleCat.{max u v} (ZMod n)) AddCommGrpCat.{max u v})).obj I) (k + 1)) :=
  cohomology_subsingleton_of_ringedEquivalence J (Ringed.constantRingSheaf J n)
    (Ringed.equivalenceStandard J n)
    (sheafCompose J (forget₂ (ModuleCat.{max u v} (ZMod n)) AddCommGrpCat.{max u v}))
    (Ringed.forwardUnderlyingIsoStandard J n) I hT k

/-- Every element of positive original cohomology of these original coefficients is zero. -/
theorem underlying_injective_cohomology_eq_zero
    (I : Sheaf J (ModuleCat.{max u v} (ZMod n))) [Injective I]
    {T : C} (hT : IsTerminal T) (q : ℕ) (hq : 0 < q)
    (x : Sheaf.H.{e} ((sheafCompose J
      (forget₂ (ModuleCat.{max u v} (ZMod n)) AddCommGrpCat.{max u v})).obj I) q) : x = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  let := underlying_injective_cohomology_subsingleton J n I hT k
  exact Subsingleton.elim _ _

end CategoryTheory.TorsionZMod
