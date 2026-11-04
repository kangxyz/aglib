/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.FieldSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FieldSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.ModuleFieldConservative

/-! The original constant and sections functors over a separably closed field are inverse. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u

attribute [local instance] hasSheafifyLarge hasSheafifyModules ModuleCat.Sheaf.hasSheafify

/-- The original constant adjunction unit is an isomorphism over a separably closed field. -/
theorem moduleFieldGlobalSectionsAdjunction_unit_isIso
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (Λ : Type (u + 1)) [CommRing Λ]
    (N : ModuleCat.{u + 1} Λ) :
    IsIso ((moduleGlobalSectionsAdjunction (Spec (.of Ω)) Λ).unit.app N) := by
  let X := Spec (.of Ω)
  let E := moduleSheafEquivalence X Λ
  let c := Constructible.Modules.moduleConstantAdjunction Λ X
  let : IsIso (c.unit.app N) :=
    Constructible.Modules.moduleConstantUnit_isIso_of_isSepClosed Λ Ω N
  let C := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  rw [moduleGlobalSectionsAdjunction, Adjunction.comp_unit_app]
  exact ((asIso (c.unit.app N)) ≪≫
    (Constructible.Modules.moduleGlobalSections Λ X).mapIso
      (E.unitIso.app (C.obj N))).isIso_hom

/-- The original constant and sections adjunction over a separably closed
field is an equivalence for arbitrary modules over the coefficient ring. -/
@[no_expose]
def moduleFieldSectionsEquivalence
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (Λ : Type (u + 1)) [CommRing Λ] :
    ModuleCat.{u + 1} Λ ≌ ModuleSheaf (Spec (.of Ω)) Λ := by
  let X := Spec (.of Ω)
  let E := moduleSheafEquivalence X Λ
  let a := moduleGlobalSectionsAdjunction X Λ
  letI (N : ModuleCat.{u + 1} Λ) : IsIso (a.unit.app N) :=
    moduleFieldGlobalSectionsAdjunction_unit_isIso Ω Λ N
  letI (M : ModuleSheaf X Λ) : IsIso (a.counit.app M) := by
    let e := a.counit.app M
    have h : IsIso (a.unit.app ((moduleGlobalSections X Λ).obj M) ≫
        (moduleGlobalSections X Λ).map e) := by
      change IsIso (a.unit.app _ ≫ (moduleGlobalSections X Λ).map (a.counit.app M))
      rw [a.right_triangle_components M]
      infer_instance
    let : IsIso ((moduleGlobalSections X Λ).map e) := (isIso_comp_left_iff _ _).mp h
    let : IsIso ((pointSmallEtale (𝟙 X)).sheafFiber.map (E.inverse.map e)) :=
      (NatIso.isIso_map_iff (moduleFieldSectionsFiberIso Ω Λ) e).mp inferInstance
    let : IsIso (E.inverse.map e) :=
      isIso_of_field_moduleGeometricStalk Λ Ω (𝟙 X) (E.inverse.map e)
    exact isIso_of_reflects_iso e E.inverse
  exact a.toEquivalence

/-- The equivalence uses the original constant coefficient functor. -/
@[simp] theorem moduleFieldSectionsEquivalence_functor
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (Λ : Type (u + 1)) [CommRing Λ] :
    (moduleFieldSectionsEquivalence Ω Λ).functor =
      constantSheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        (moduleSheafEquivalence (Spec (.of Ω)) Λ).functor := by
  unfold moduleFieldSectionsEquivalence
  rfl

/-- The inverse equivalence is the original module sections functor. -/
@[simp] theorem moduleFieldSectionsEquivalence_inverse
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (Λ : Type (u + 1)) [CommRing Λ] :
    (moduleFieldSectionsEquivalence Ω Λ).inverse = moduleGlobalSections (Spec (.of Ω)) Λ := by
  unfold moduleFieldSectionsEquivalence
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
