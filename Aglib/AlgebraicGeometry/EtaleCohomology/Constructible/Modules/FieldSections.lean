/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureLocality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ConnectedTorsionSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.PullbackLocality
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.FieldTerminal
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Original constructible module sections over separably closed fields

The actual terminal-point germ and native sheafification prove that the original
constant-adjunction unit is invertible for every module value. Constructibility
on a field gives an actual constant finite module. Neither torsion nor a finite
underlying additive group is required, and the coefficient ring is arbitrary.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (R : Type r) [CommRing R]

/-- Identity comparison for the original chosen module inverse image. -/
def moduleInverseImageId (X : Scheme.{u}) :
    moduleInverseImage R (𝟙 X) ≅ 𝟭 (ModuleSheaf R X) := by
  let e := Functor.sheafPushforwardContinuousId' (siteBaseChangeId X)
    (ModuleCat.{u + 1} R) X.smallEtaleTopology
  exact ((moduleImageAdjunction R (𝟙 X)).ofNatIsoRight e).leftAdjointUniq Adjunction.id

/-- The actual terminal germ is invertible for arbitrary module presheaves. -/
instance moduleFieldTerminalGerm_isIso
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (P : (Spec (.of Ω)).Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R) :
    IsIso ((pointSmallEtale (𝟙 (Spec (.of Ω)))).toPresheafFiber
      (etaleTerminal (Spec (.of Ω))) (fieldTerminalPoint Ω) P) :=
  isIso_ι_of_isTerminal (fieldTerminalPointIsInitial Ω).op
    ((Functor.Elements.π (pointSmallEtale (𝟙 (Spec (.of Ω)))).fiber).op ⋙ P)

/-- Sheafification does not change original terminal sections over a separably
closed field, for arbitrary module presheaves. -/
theorem moduleToSheafify_terminal_isIso
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (P : (Spec (.of Ω)).Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R) :
    IsIso ((toSheafify (Spec (.of Ω)).smallEtaleTopology P).app
      (op (etaleTerminal (Spec (.of Ω))))) := by
  let : HasProducts.{u} (ModuleCat.{u + 1} R) :=
    fun I => ModuleCat.hasLimitsOfShape.{u, u, u + 1, r} (J := Discrete I)
  let Φ := pointSmallEtale (𝟙 (Spec (.of Ω)))
  let Q : (Spec (.of Ω)).Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R :=
    sheafify (Spec (.of Ω)).smallEtaleTopology P
  let η : P ⟶ Q := toSheafify (Spec (.of Ω)).smallEtaleTopology P
  let T := etaleTerminal (Spec (.of Ω))
  let t := fieldTerminalPoint Ω
  let : IsIso (Φ.toPresheafFiber T t P) := moduleFieldTerminalGerm_isIso R Ω P
  let : IsIso (Φ.toPresheafFiber T t Q) := moduleFieldTerminalGerm_isIso R Ω Q
  let : IsIso ((Φ.presheafFiber (A := ModuleCat.{u + 1} R)).map η) := by
    change IsIso ((Φ.presheafFiber (A := ModuleCat.{u + 1} R)).map
      (toSheafify (Spec (.of Ω)).smallEtaleTopology P))
    infer_instance
  have h : IsIso (η.app (op T) ≫ Φ.toPresheafFiber T t Q) := by
    rw [← Φ.toPresheafFiber_naturality (A := ModuleCat.{u + 1} R) η T t]
    infer_instance
  exact IsIso.of_isIso_comp_right (η.app (op T)) (Φ.toPresheafFiber T t Q)

/-- The original constant-adjunction unit is invertible without any torsion or
finiteness assumption on its value. -/
theorem moduleConstantUnit_isIso_of_isSepClosed
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (M : ModuleCat.{u + 1} R) :
    IsIso ((moduleConstantAdjunction R (Spec (.of Ω))).unit.app M) := by
  simp only [moduleConstantAdjunction, constantSheafAdj, Adjunction.comp_unit_app,
    constantPresheafAdj_unit_app, Category.id_comp]
  exact moduleToSheafify_terminal_isIso R Ω ((Functor.const _).obj M)

/-- The literal constant value and its original global sections agree over a
separably closed field. -/
def moduleFieldConstantSectionsIso
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (M : ModuleCat.{u + 1} R) :
    M ≅ (moduleGlobalSections R (Spec (.of Ω))).obj
      ((constantSheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) := by
  let := moduleConstantUnit_isIso_of_isSepClosed R Ω M
  exact asIso ((moduleConstantAdjunction R (Spec (.of Ω))).unit.app M)

variable {R}

/-- A constructible coefficient on a field is genuinely finite-type locally
constant: its nonempty actual stratum is the whole field spectrum. -/
theorem isFiniteTypeLocallyConstant_of_isConstructible_field
    (K : Type u) [Field K] {F : ModuleSheaf R (Spec (.of K))}
    (hF : IsConstructible F) : IsFiniteTypeLocallyConstant F := by
  obtain ⟨t⟩ := nonempty_constructiblePartition hF
  obtain ⟨i, y, hy⟩ := t.covers (default : Spec (.of K))
  let j := t.inclusion i
  let : IsImmersion j := t.immersion i
  let hj : Surjective j := ⟨fun x => ⟨y, hy.trans (Subsingleton.elim _ x)⟩⟩
  let : IsClosedImmersion j := IsClosedImmersion.of_isPreimmersion j (by
    rw [Set.range_eq_univ.mpr hj.surj]
    exact isClosed_univ)
  let : IsIso j := isIso_of_isClosedImmersion_of_surjective j
  exact isFiniteTypeLocallyConstant_of_etaleCover
    (fun _ : PUnit.{u + 1} => Scheme.Etale.mk j)
    (fun x => ⟨PUnit.unit, y, hy.trans (Subsingleton.elim _ x)⟩)
    F (fun _ => t.locally_constant i)

/-- Over a separably closed field, the given actual local trivialization
produces a global constant finite module by splitting one etale chart. -/
theorem exists_finite_constant_iso_of_isFiniteTypeLocallyConstant_field
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    {F : ModuleSheaf R (Spec (.of Ω))} (hF : IsFiniteTypeLocallyConstant F) :
    ∃ M : ModuleCat.{u + 1} R, Module.Finite R M ∧
      Nonempty (F ≅ (constantSheaf (Spec (.of Ω)).smallEtaleTopology
        (ModuleCat.{u + 1} R)).obj M) := by
  obtain ⟨t⟩ := hF
  obtain ⟨i, y, hy⟩ := t.covers (default : Spec (.of Ω))
  obtain ⟨s, hs, -⟩ := exists_fac_of_etale_of_isSepClosed (t.chart i).hom
    (𝟙 (Spec (.of Ω))) y hy
  refine ⟨t.value i, t.finite_value i, ⟨?_⟩⟩
  exact ((moduleInverseImageId R _).app F).symm ≪≫
    eqToIso (congrArg (fun f => (moduleInverseImage R f).obj F) hs.symm) ≪≫
    (moduleInverseImageComp R (t.chart i).hom s).app F ≪≫
    (moduleInverseImage R s).mapIso (t.trivialization i) ≪≫
    (moduleInverseImageConstantIso R s).app (t.value i)

/-- Original sections of every constructible module coefficient over a
separably closed field are finite over the original arbitrary ring. -/
theorem moduleGlobalSections_finite_of_isConstructible_field
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    {F : ModuleSheaf R (Spec (.of Ω))} (hF : IsConstructible F) :
    Module.Finite R ((moduleGlobalSections R (Spec (.of Ω))).obj F) := by
  obtain ⟨M, hM, ⟨e⟩⟩ :=
    exists_finite_constant_iso_of_isFiniteTypeLocallyConstant_field Ω
      (isFiniteTypeLocallyConstant_of_isConstructible_field Ω hF)
  let := hM
  exact Module.Finite.equiv
    ((moduleFieldConstantSectionsIso R Ω M) ≪≫
      (moduleGlobalSections R (Spec (.of Ω))).mapIso e.symm).toLinearEquiv

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
