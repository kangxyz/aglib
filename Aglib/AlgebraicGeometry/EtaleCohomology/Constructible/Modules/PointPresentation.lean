/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FieldSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.SigmaSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.CoverConservativity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ClosureConstructible
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FiniteEtalePresentation
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.FiniteClosedSupport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Original finite unit presentations on the actual point scheme

Field and coproduct sections retain their original coefficient actions. The
original constant-adjunction counit is epi on the finite point scheme; finite
global generators then give an epi from the same native finite unit power.
No scalar-forgetting fullness or globally constant coefficient is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

open scoped ZeroObject

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable (Λ : Type (u + 1)) [CommRing Λ]

local instance pointPresentationHasFiniteLimits : HasFiniteLimits (ModuleCat.{u + 1} Λ) where
  out _ _ _ := ModuleCat.hasLimitsOfShape.{0, 0, u + 1, u + 1}

local instance pointPullback_isLeftAdjoint {S X : Scheme.{u}} (f : S ⟶ X) :
    (moduleInverseImage Λ f).IsLeftAdjoint := (moduleImageAdjunction Λ f).isLeftAdjoint

local instance pointPullback_additive {S X : Scheme.{u}} (f : S ⟶ X) :
    (moduleInverseImage Λ f).Additive := Functor.additive_of_preserves_binary_products _

local instance pointConstant_isLeftAdjoint (X : Scheme.{u}) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).IsLeftAdjoint :=
  (moduleConstantAdjunction Λ X).isLeftAdjoint

private theorem counit_image_isIso
    {A B : Type*} [Category* A] [Category* B] {L : A ⥤ B} {R : B ⥤ A}
    (adj : L ⊣ R) (M : A) [IsIso (adj.unit.app M)] :
    IsIso (adj.counit.app (L.obj M)) := by
  have h : IsIso (L.map (adj.unit.app M) ≫ adj.counit.app (L.obj M)) := by
    rw [adj.left_triangle_components M]
    exact ⟨⟨𝟙 _, by simp, by simp⟩⟩
  exact (isIso_comp_left_iff _ _).mp h

/-- The ORIGINAL constant/sections counit is invertible on every constructible
module coefficient over an actual separably closed residue field. -/
theorem moduleConstantCounit_field_isIso
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    {F : ModuleSheaf Λ (Spec (.of Ω))} (hF : IsConstructible F) :
    IsIso ((moduleConstantAdjunction Λ (Spec (.of Ω))).counit.app F) := by
  obtain ⟨M, _, ⟨e⟩⟩ :=
    exists_finite_constant_iso_of_isFiniteTypeLocallyConstant_field Ω
      (isFiniteTypeLocallyConstant_of_isConstructible_field Ω hF)
  let adj := moduleConstantAdjunction Λ (Spec (.of Ω))
  let : IsIso (adj.unit.app M) := moduleConstantUnit_isIso_of_isSepClosed Λ Ω M
  let : IsIso (adj.counit.app
      ((constantSheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :=
    counit_image_isIso adj M
  have hn := adj.counit.naturality e.hom
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  have hc : IsIso (adj.counit.app F ≫ e.hom) := by
    rw [← hn]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hc

/-- Pulling the original constant counit to an actual chart is constant of
original section restriction followed by the original chart counit. -/
theorem moduleConstantCounit_pullback
    {S X : Scheme.{u}} (f : S ⟶ X) (F : ModuleSheaf Λ X) :
    (moduleInverseImageConstantIso Λ f).inv.app ((moduleGlobalSections Λ X).obj F) ≫
        (moduleInverseImage Λ f).map ((moduleConstantAdjunction Λ X).counit.app F) =
      (constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
          (moduleGlobalSectionsPullback Λ f F) ≫
        (moduleConstantAdjunction Λ S).counit.app ((moduleInverseImage Λ f).obj F) := by
  let a := moduleConstantAdjunction Λ X
  let b := moduleConstantAdjunction Λ S
  have h := moduleConstantTransport_homEquiv Λ f
    ((moduleGlobalSections Λ X).obj F) ((moduleConstantAdjunction Λ X).counit.app F)
  have hε : a.homEquiv _ _ (a.counit.app F) = 𝟙 _ := by
    rw [Adjunction.homEquiv_unit, a.right_triangle_components F]
  dsimp only [a] at hε
  rw [hε, Category.id_comp] at h
  apply (b.homEquiv _ _).injective
  exact h.trans
    ((b.homEquiv _ _).apply_symm_apply (moduleGlobalSectionsPullback Λ f F)).symm

private theorem epi_of_module_etale_inverseImages
    {X : Scheme.{u}} {ι : Type u} (Y : ι → X.Etale)
    (hcover : ∀ x : X, ∃ (i : ι) (y : (Y i).left), (Y i).hom y = x)
    {F G : ModuleSheaf Λ X} (a : F ⟶ G)
    (ha : ∀ i, Epi ((moduleInverseImage Λ (Y i).hom).map a)) : Epi a := by
  apply Preadditive.epi_of_isZero_cokernel
  let z : cokernel a ⟶ (0 : ModuleSheaf Λ X) := 0
  have hz (i : ι) : IsZero ((moduleInverseImage Λ (Y i).hom).obj (cokernel a)) := by
    let : Epi ((moduleInverseImage Λ (Y i).hom).map a) := ha i
    exact (isZero_cokernel_of_epi ((moduleInverseImage Λ (Y i).hom).map a)).of_iso
      (PreservesCokernel.iso (moduleInverseImage Λ (Y i).hom) a)
  have hi : IsIso z := by
    apply isIso_of_module_etale_inverseImages Λ Y hcover
    intro i
    let P := moduleInverseImage Λ (Y i).hom
    have h0 : IsZero (P.obj (0 : ModuleSheaf Λ X)) := P.map_isZero (isZero_zero _)
    let e := (hz i).isoZero ≪≫ h0.isoZero.symm
    have he : P.map z = e.hom := (hz i).eq_of_src _ _
    rw [he]
    infer_instance
  let := hi
  exact (isZero_zero (ModuleSheaf Λ X)).of_iso (asIso z)

open Curves.FiniteClosedSupport

variable (X : Scheme.{u}) (D : Set X) [Finite D]

omit [Finite D] in
/-- Restriction of original sections to any actual point component is
surjective, through the original coproduct sections comparison. -/
theorem modulePointSectionsPullback_surjective
    (F : ModuleSheaf Λ (pointScheme X D)) (x : D) :
    Function.Surjective (moduleGlobalSectionsPullback Λ
      (Sigma.ι (fun y : D => Spec (X.residueField y.val)) x) F) := by
  classical
  let Y := fun y : D => Spec (X.residueField y.val)
  let U := Scheme.Etale.sigmaChart Y x
  let c := moduleEtaleChartSectionsIso Λ F U
  let e := moduleSigmaSectionsLinearEquiv Λ Y F
  intro y
  let v : ∀ i : D, F.obj.obj (op (Scheme.Etale.sigmaChart Y i)) :=
    Function.update 0 x (c.hom y)
  let s := e.symm v
  refine ⟨s, ?_⟩
  apply c.toLinearEquiv.injective
  have h := ConcreteCategory.congr_hom (moduleEtaleChartSectionsIso_restriction Λ F U) s
  change c.hom (moduleGlobalSectionsPullback Λ (Sigma.ι Y x) F s) = _ at h
  change c.hom (moduleGlobalSectionsPullback Λ (Sigma.ι Y x) F s) = c.hom y
  rw [h]
  have hi : (etaleTerminalIsTerminal (∐ Y)).from U =
      Scheme.Etale.sigmaChartInclusion Y x :=
    (etaleTerminalIsTerminal (∐ Y)).hom_ext _ _
  rw [hi]
  have he := congrFun (e.apply_symm_apply v) x
  change moduleSigmaSectionsLinearEquiv Λ Y F s x = v x at he
  rw [moduleSigmaSectionsLinearEquiv_apply] at he
  exact he.trans (by simp [v])

omit [Finite D] in
/-- The ORIGINAL constant/sections counit is epi on a constructible coefficient
on the actual finite point scheme, including the empty coproduct. -/
theorem modulePointConstantCounit_epi
    (hsep : ∀ x : D, IsSepClosed (X.residueField x.val))
    (F : ModuleSheaf Λ (pointScheme X D)) (hF : IsConstructible F) :
    Epi ((moduleConstantAdjunction Λ (pointScheme X D)).counit.app F) := by
  let Y := fun x : D => Spec (X.residueField x.val)
  let a := fun x : D => Sigma.ι Y x
  apply epi_of_module_etale_inverseImages Λ (fun x => Scheme.Etale.mk (a x))
    (fun z => by
      obtain ⟨⟨x, y⟩, rfl⟩ := (sigmaMk Y).surjective z
      refine ⟨x, y, ?_⟩
      rw [sigmaMk_mk]
      dsimp only [Scheme.Etale.mk, MorphismProperty.Over.mk]
      rfl)
  intro x
  let : IsSepClosed (X.residueField x.val) := hsep x
  let P := moduleInverseImage Λ (a x)
  let C := constantSheaf (Y x).smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let : Epi (moduleGlobalSectionsPullback Λ (a x) F) :=
    (ModuleCat.epi_iff_surjective _).mpr (modulePointSectionsPullback_surjective Λ X D F x)
  let : IsIso ((moduleConstantAdjunction Λ (Y x)).counit.app (P.obj F)) :=
    moduleConstantCounit_field_isIso Λ (X.residueField x.val)
      (isConstructible_pullback (a x) hF)
  have he : Epi ((moduleInverseImageConstantIso Λ (a x)).inv.app
      ((moduleGlobalSections Λ (pointScheme X D)).obj F) ≫
        P.map ((moduleConstantAdjunction Λ (pointScheme X D)).counit.app F)) := by
    rw [moduleConstantCounit_pullback]
    infer_instance
  let := he
  change Epi (P.map ((moduleConstantAdjunction Λ (pointScheme X D)).counit.app F))
  exact epi_of_epi
    ((moduleInverseImageConstantIso Λ (a x)).inv.app
      ((moduleGlobalSections Λ (pointScheme X D)).obj F))
    (P.map ((moduleConstantAdjunction Λ (pointScheme X D)).counit.app F))

/-- Original sections of a constructible actual finite-point coefficient
are finitely generated over the original arbitrary commutative coefficient ring. -/
theorem modulePointGlobalSections_finite
    (hsep : ∀ x : D, IsSepClosed (X.residueField x.val))
    (F : ModuleSheaf Λ (pointScheme X D)) (hF : IsConstructible F) :
    Module.Finite Λ ((moduleGlobalSections Λ (pointScheme X D)).obj F) := by
  let Y := fun x : D => Spec (X.residueField x.val)
  apply moduleGlobalSections_finite_of_finite_components Λ Y F
  intro x
  let : IsSepClosed (X.residueField x.val) := hsep x
  exact moduleGlobalSections_finite_of_isConstructible_field (X.residueField x.val)
    (isConstructible_pullback (Sigma.ι Y x) hF)

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients Curves.FiniteClosedSupport

attribute [local instance] hasSheafifyLarge hasSheafifyModules
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

attribute [local instance] moduleSheaf_hasFiniteBiproducts

variable (X : Scheme.{u}) (D : Set X) [Finite D]
  (Λ : Type (u + 1)) [CommRing Λ]

/-- A constructible actual point-scheme coefficient receives an epimorphism
from an actual finite biproduct of the SAME original native unit. -/
theorem exists_modulePointUnitBiproduct_epi
    (hsep : ∀ x : D, IsSepClosed (X.residueField x.val))
    (M : ModuleSheaf (pointScheme X D) Λ)
    (hM : Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence (pointScheme X D) Λ).inverse.obj M)) :
    ∃ (m : ℕ) (a : (⨁ fun _ : Fin m => moduleUnit (pointScheme X D) Λ) ⟶ M), Epi a := by
  let Z := pointScheme X D
  let E := moduleSheafEquivalence Z Λ
  let F := E.inverse.obj M
  let C := constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let N : ModuleCat.{u + 1} Λ := (Constructible.Modules.moduleGlobalSections Λ Z).obj F
  let : Module.Finite Λ N :=
    Constructible.Modules.modulePointGlobalSections_finite Λ X D hsep F hM
  obtain ⟨m, q, hq⟩ := Module.Finite.exists_fin' Λ N
  let qM := ModuleCat.ofHom q
  let : Epi qM := (ModuleCat.epi_iff_surjective qM).mpr (by
    change Function.Surjective q
    exact hq)
  let : C.IsLeftAdjoint := (Constructible.Modules.moduleConstantAdjunction Λ Z).isLeftAdjoint
  let : Epi ((Constructible.Modules.moduleConstantAdjunction Λ Z).counit.app F) :=
    Constructible.Modules.modulePointConstantCounit_epi Λ X D hsep F hM
  let a : (⨁ fun _ : Fin m => moduleUnit Z Λ) ⟶ M :=
    (moduleFiniteFreeConstantIso Z Λ m).hom ≫
      E.functor.map (C.map qM ≫ (Constructible.Modules.moduleConstantAdjunction Λ Z).counit.app F) ≫
        E.counitIso.hom.app M
  refine ⟨m, a, ?_⟩
  dsimp only [a]
  infer_instance

/-- The actual kernel of the original finite-unit epi remains constructible
when the coefficient ring is Noetherian. No arbitrary-subobject closure is used. -/
theorem exists_modulePointUnitBiproduct_epi_constructible_kernel [IsNoetherianRing Λ]
    (hsep : ∀ x : D, IsSepClosed (X.residueField x.val))
    (M : ModuleSheaf (pointScheme X D) Λ)
    (hM : Constructible.Modules.IsConstructible
      ((moduleSheafEquivalence (pointScheme X D) Λ).inverse.obj M)) :
    ∃ (m : ℕ) (a : (⨁ fun _ : Fin m => moduleUnit (pointScheme X D) Λ) ⟶ M),
      Epi a ∧ Constructible.Modules.IsConstructible
        ((moduleSheafEquivalence (pointScheme X D) Λ).inverse.obj (kernel a)) := by
  obtain ⟨m, a, ha⟩ := exists_modulePointUnitBiproduct_epi X D Λ hsep M hM
  let E := (moduleSheafEquivalence (pointScheme X D) Λ).inverse
  have hB : Constructible.Modules.IsConstructible
      (E.obj (⨁ fun _ : Fin m => moduleUnit (pointScheme X D) Λ)) :=
    Constructible.Modules.isConstructible_of_isFiniteTypeLocallyConstant
      (moduleUnitBiproduct_isFiniteTypeLocallyConstant (pointScheme X D) Λ m)
  exact ⟨m, a, ha, (Constructible.Modules.isConstructible_iff_of_iso
    (PreservesKernel.iso E a)).mpr
      (Constructible.Modules.isConstructible_kernel (E.map a) hB hM)⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
