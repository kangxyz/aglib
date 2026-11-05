/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage.Module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionColimit.ConstructibleTorsion
public import Aglib.CategoryTheory.Sites.Point.Constant

/-! # Finite generation of original constructible module stalks

Actual local trivializations and the original module-valued point comparison
transport finite generation to each geometric stalk. No additive finiteness
or commutativity of the coefficient ring is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

variable (R : Type r) [Ring R]

attribute [local instance] ModuleCat.Sheaf.hasSheafify hasSheafifyLarge

/-- Finite generation transports through the original module stalk comparison. -/
theorem finite_geometricStalk_of_inverseImage {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : ModuleSheaf R X) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (η : Spec (.of Ω) ⟶ Y)
    (h : Module.Finite R (((pointSmallEtale η).sheafFiber (A := ModuleCat.{u + 1} R)).obj
      ((moduleInverseImage R f).obj F))) :
    Module.Finite R (((pointSmallEtale (η ≫ f)).sheafFiber (A := ModuleCat.{u + 1} R)).obj F) := by
  let : Module.Finite R (((siteBaseChange f).sheafPullback (ModuleCat.{u + 1} R)
      X.smallEtaleTopology Y.smallEtaleTopology ⋙
        (pointSmallEtale η).sheafFiber).obj F) := h
  let e := (geometricModuleStalkInverseImageIso f η R).app F
  exact Module.Finite.of_surjective e.inv.hom
    (ConcreteCategory.bijective_of_isIso e.inv).surjective

/-- Original constant module germs identify the geometric stalk with its value. -/
theorem finite_geometricStalk_constant {X : Scheme.{u}}
    (M : ModuleCat.{u + 1} R) [Module.Finite R M]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ X) :
    Module.Finite R (((pointSmallEtale η).sheafFiber (A := ModuleCat.{u + 1} R)).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)) := by
  let : HasProducts.{u} (ModuleCat.{u + 1} R) :=
    fun I => ModuleCat.hasLimitsOfShape.{u, u, u + 1, r} (J := Discrete I)
  let Φ := pointSmallEtale η
  let U := Scheme.Etale.mk (𝟙 X)
  let x : Φ.fiber.obj U := Over.homMk η (by change η ≫ 𝟙 X = η; simp)
  let a : M ⟶ ((pointSmallEtale η).sheafFiber (A := ModuleCat.{u + 1} R)).obj
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :=
    (CategoryTheory.toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj M)).app (op U) ≫
    Φ.toPresheafFiber U x ((constantSheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} R)).obj M).obj
  have : IsIso a := Φ.constantSheafGerm_isIso U x M
  exact Module.Finite.of_surjective a.hom
    (ConcreteCategory.bijective_of_isIso a).surjective

/-- Finite-type locally constant native module coefficients have finite-type
geometric stalks, even when their additive groups are infinite. -/
theorem finite_geometricStalk_of_isFiniteTypeLocallyConstant {X : Scheme.{u}}
    (F : ModuleSheaf R X) (hF : IsFiniteTypeLocallyConstant F)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ X) :
    Module.Finite R (((pointSmallEtale η).sheafFiber (A := ModuleCat.{u + 1} R)).obj F) := by
  obtain ⟨t⟩ := hF
  obtain ⟨i, y, hy⟩ := t.covers (η default)
  obtain ⟨ζ, hζ, _⟩ := exists_fac_of_etale_of_isSepClosed (t.chart i).hom η y hy
  rw [← hζ]
  apply finite_geometricStalk_of_inverseImage R (t.chart i).hom F ζ
  let : Module.Finite R (t.value i) := t.finite_value i
  let : Module.Finite R (((pointSmallEtale ζ).sheafFiber
      (A := ModuleCat.{u + 1} R)).obj
        ((constantSheaf (t.chart i).left.smallEtaleTopology
          (ModuleCat.{u + 1} R)).obj (t.value i))) :=
    finite_geometricStalk_constant R (t.value i) ζ
  let e := ((pointSmallEtale ζ).sheafFiber (A := ModuleCat.{u + 1} R)).mapIso (t.trivialization i)
  exact Module.Finite.of_surjective e.inv.hom
    (ConcreteCategory.bijective_of_isIso e.inv).surjective

/-- The stratum through the original geometric point controls its module stalk. -/
theorem finite_geometricStalk_of_partition {X : Scheme.{u}}
    (F : ModuleSheaf R X) (t : ConstructiblePartition F)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ X) :
    Module.Finite R (((pointSmallEtale η).sheafFiber (A := ModuleCat.{u + 1} R)).obj F) := by
  obtain ⟨i, y, hy⟩ := t.covers (η default)
  have : IsImmersion (t.inclusion i) := t.immersion i
  obtain ⟨ζ, hζ⟩ := exists_fieldPoint_lift_of_mem_range (t.inclusion i) η ⟨y, hy⟩
  rw [← hζ]
  exact finite_geometricStalk_of_inverseImage R (t.inclusion i) F ζ
    (finite_geometricStalk_of_isFiniteTypeLocallyConstant R _ (t.locally_constant i) ζ)

/-- Every original constructible module sheaf has finitely generated geometric stalks. -/
theorem moduleGeometricStalk_finite_of_isConstructible
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (η : Spec (.of Ω) ⟶ X) {F : ModuleSheaf R X} (hF : IsConstructible F) :
    Module.Finite R (((pointSmallEtale η).sheafFiber (A := ModuleCat.{u + 1} R)).obj F) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show η default ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨t⟩ := hF ⟨U, hU⟩
  obtain ⟨ζ, hζ⟩ := exists_fieldPoint_lift_of_mem_range U.ι η
    ⟨⟨η default, hxU⟩, rfl⟩
  rw [← hζ]
  exact finite_geometricStalk_of_inverseImage R U.ι F ζ
    (finite_geometricStalk_of_partition R _ t ζ)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
