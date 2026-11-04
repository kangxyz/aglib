/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.GlobalSectionsUnderlying
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteEtalePresentation
public import Mathlib.CategoryTheory.Adjunction.Additive

/-! The original unit represents original terminal module sections, additively. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

attribute [local instance] hasSheafifyLarge hasSheafifyModules ModuleCat.Sheaf.hasSheafify

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]

private def unitPrecompAddEquiv (M : ModuleSheaf X Λ) :
    (moduleUnit X Λ ⟶ M) ≃+
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        (moduleSheafEquivalence X Λ).functor).obj (ModuleCat.of Λ Λ) ⟶ M) :=
  { Iso.homCongr (moduleUnitConstantIso X Λ).symm (Iso.refl M) with
    map_add' := by
      intro f g
      let e := (moduleUnitConstantIso X Λ).hom
      change e ≫ (f + g) ≫ 𝟙 M = (e ≫ f ≫ 𝟙 M) + (e ≫ g ≫ 𝟙 M)
      simp only [Category.comp_id, Preadditive.comp_add] }

/-- The original coefficient unit represents the original global sections functor. -/
@[no_expose]
def moduleUnitSectionsAddEquiv (M : ModuleSheaf X Λ) :
    (moduleUnit X Λ ⟶ M) ≃+ (moduleGlobalSections X Λ).obj M := by
  let F := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
    (moduleSheafEquivalence X Λ).functor
  let a := moduleGlobalSectionsAdjunction X Λ
  let : F.Additive := a.left_adjoint_additive
  exact (unitPrecompAddEquiv X Λ M).trans
    ((a.homAddEquiv (ModuleCat.of Λ Λ) M).trans
      (ModuleCat.homLinearEquiv (S := Λ).trans (LinearMap.ringLmapEquivSelf Λ Λ _)).toAddEquiv)

/-- Evaluate the original adjoint of the unit map at one. -/
theorem moduleUnitSectionsAddEquiv_apply (M : ModuleSheaf X Λ) (s : moduleUnit X Λ ⟶ M) :
    moduleUnitSectionsAddEquiv X Λ M s =
      ((moduleGlobalSectionsAdjunction X Λ).homEquiv (ModuleCat.of Λ Λ) M
        ((moduleUnitConstantIso X Λ).hom ≫ s)).hom (1 : Λ) := by
  change ((moduleGlobalSectionsAdjunction X Λ).homEquiv (ModuleCat.of Λ Λ) M
    ((moduleUnitConstantIso X Λ).hom ≫ s ≫ 𝟙 M)).hom (1 : Λ) = _
  rw [Category.comp_id]

/-- The unit comparison carries postcomposition to the original section map. -/
theorem moduleUnitSectionsAddEquiv_comp {M N : ModuleSheaf X Λ}
    (s : moduleUnit X Λ ⟶ M) (f : M ⟶ N) :
    moduleUnitSectionsAddEquiv X Λ N (s ≫ f) =
      (moduleGlobalSections X Λ).map f (moduleUnitSectionsAddEquiv X Λ M s) := by
  let e := (moduleUnitConstantIso X Λ).hom
  let a := moduleGlobalSectionsAdjunction X Λ
  change (a.homEquiv (ModuleCat.of Λ Λ) N (e ≫ (s ≫ f) ≫ 𝟙 N)).hom 1 =
    ((moduleGlobalSections X Λ).map f).hom
      ((a.homEquiv (ModuleCat.of Λ Λ) M (e ≫ s ≫ 𝟙 M)).hom 1)
  rw [Category.comp_id, Category.comp_id, ← Category.assoc, a.homEquiv_naturality_right]
  rfl

/-- The unit's identity represents the original constant generator evaluated at one. -/
theorem moduleUnitSectionsAddEquiv_id :
    moduleUnitSectionsAddEquiv X Λ (moduleUnit X Λ) (𝟙 _) =
      ((moduleGlobalSections X Λ).map (moduleUnitConstantIso X Λ).hom).hom
        (((moduleGlobalSectionsAdjunction X Λ).unit.app (ModuleCat.of Λ Λ)).hom (1 : Λ)) := by
  let e := (moduleUnitConstantIso X Λ).hom
  let a := moduleGlobalSectionsAdjunction X Λ
  change (a.homEquiv (ModuleCat.of Λ Λ) (moduleUnit X Λ) (e ≫ 𝟙 _ ≫ 𝟙 _)).hom (1 : Λ) = _
  simp only [Category.comp_id]
  rw [Adjunction.homEquiv_unit]
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
