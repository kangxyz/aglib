/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Native scalar coinduction and its composition

The original coinduction functors compose through uniqueness of right
adjoints, using the native scalar-restriction composition comparison.
The unit and counit equations keep those same original adjunctions.
Coinduction preserves injectives because scalar restriction preserves
monomorphisms. No commutativity, flatness or finiteness is assumed, and the
ring universes remain independent. Derived composition and geometric
purity consume these ordinary functors and their normalized maps.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

universe u v w z
namespace ModuleCat

/-- Native scalar coinduction is additive on the original coefficient morphisms. -/
instance coextendScalars_additive {A : Type u} {B : Type v} [Ring A] [Ring B]
    (φ : A →+* B) : (coextendScalars.{u, v, z} φ).Additive where
  map_add {X Y f g} := by
    ext x t
    rfl

variable {R : Type u} {S : Type v} {T : Type w} [Ring R] [Ring S] [Ring T]
  (σ : R →+* S) (τ : S →+* T)

/-- Coinduction for a composite is the composite of the original right adjoints. -/
def coextendScalarsComp :
    (coextendScalars (τ.comp σ) :
      ModuleCat.{max v w z} R ⥤ ModuleCat.{max v w z} T) ≅
        (coextendScalars σ : ModuleCat.{max v w z} R ⥤ ModuleCat.{max v w z} S) ⋙
          coextendScalars τ :=
  (restrictCoextendScalarsAdj.{max v w z, u, w} (τ.comp σ)).rightAdjointUniq
    (((restrictCoextendScalarsAdj.{max v w z, v, w} τ).comp
      (restrictCoextendScalarsAdj.{max v w z, u, v} σ)).ofNatIsoLeft
      (restrictScalarsComp.{max v w z, u, v, w} σ τ).symm)

/-- Native coinduction preserves injectives because its genuine left adjoint is exact. -/
theorem coextendScalars_preservesInjectiveObjects :
    (coextendScalars σ :
      ModuleCat.{max v z} R ⥤ ModuleCat.{max v z} S).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (restrictCoextendScalarsAdj.{z, u, v} σ)

/-- The composition comparison retains the original scalar-coinduction counits. -/
@[reassoc]
theorem coextendScalarsComp_counit (M : ModuleCat.{max v w z} R) :
    (restrictScalars (τ.comp σ)).map ((coextendScalarsComp σ τ).hom.app M) ≫
        (restrictScalarsComp.{max v w z, u, v, w} σ τ).hom.app _ ≫
          (restrictScalars σ).map
            ((restrictCoextendScalarsAdj.{max v w z, v, w} τ).counit.app _) ≫
            (restrictCoextendScalarsAdj.{max v w z, u, v} σ).counit.app M =
      (restrictCoextendScalarsAdj.{max v w z, u, w} (τ.comp σ)).counit.app M := by
  exact (restrictCoextendScalarsAdj.{max v w z, u, w} (τ.comp σ)).rightAdjointUniq_hom_app_counit
    (((restrictCoextendScalarsAdj.{max v w z, v, w} τ).comp
      (restrictCoextendScalarsAdj.{max v w z, u, v} σ)).ofNatIsoLeft
      (restrictScalarsComp.{max v w z, u, v, w} σ τ).symm) M

/-- The composition comparison retains both original scalar-coinduction units. -/
@[reassoc]
theorem coextendScalarsComp_unit (M : ModuleCat.{max v w z} T) :
    (restrictCoextendScalarsAdj.{max v w z, u, w} (τ.comp σ)).unit.app M ≫
        (coextendScalarsComp σ τ).hom.app ((restrictScalars (τ.comp σ)).obj M) =
      (restrictCoextendScalarsAdj.{max v w z, v, w} τ).unit.app M ≫
        (coextendScalars τ).map
          ((restrictCoextendScalarsAdj.{max v w z, u, v} σ).unit.app
            ((restrictScalars τ).obj M)) ≫
        (coextendScalars σ ⋙ coextendScalars τ).map
          ((restrictScalarsComp.{max v w z, u, v, w} σ τ).inv.app M) := by
  exact (restrictCoextendScalarsAdj.{max v w z, u, w} (τ.comp σ)).unit_rightAdjointUniq_hom_app
    (((restrictCoextendScalarsAdj.{max v w z, v, w} τ).comp
      (restrictCoextendScalarsAdj.{max v w z, u, v} σ)).ofNatIsoLeft
        (restrictScalarsComp.{max v w z, u, v, w} σ τ).symm) M

end ModuleCat
