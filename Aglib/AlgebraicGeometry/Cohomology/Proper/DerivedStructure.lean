/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.DerivedStructure.Basic
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Unit
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.FirstHomology
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Derived
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.GlobalSectionsComposition
public import Aglib.AlgebraicGeometry.Cohomology.Proper.BirationalStructureSheaf
public import Aglib.AlgebraicGeometry.Cohomology.Proper.FibreDimension
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Coefficient
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Derived.Connecting
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.GlobalSectionsComposition.SingleUnit
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Composition

/-!
# The original structural derived unit and surface cohomology triangles

The structural map on sections, the installed native derived single unit,
and the original scalar action define the actual map from the base ring
single to derived global sections. Its H0 equation uses the native
left-exact comparison. Proper birational normality identifies that same H0
map with an isomorphism. Complete-base fibre-dimensional vanishing supplies
the actual upper bound and hence a unit-preserving Postnikov triangle.

The analogous original structure-module unit for a proper birational map
gives the raw Leray triangle. Its degree-one short exact sequence follows
from lower t-exactness and the same complete-base vanishing, without an
assumed upper bound on relative higher direct images.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Abelian HomologicalComplex
open AlgebraicGeometry TopologicalSpace Opposite Scheme.Modules QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R : Type u} [CommRing R] (X : Scheme.{u}) (α : R →+* Γ(X, ⊤))

/-- The standard derived category of module sheaves for the structural and Leray triangles. -/
local instance derivedStructureSource (Y : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Y.Modules := HasDerivedCategory.standard _

/-- The standard derived category of `R`-modules for derived structural global sections. -/
local instance derivedStructureTarget : HasDerivedCategory.{u + 1} (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

private theorem rightDerived_single_isGE
    {A B : Type*} [Category A] [Abelian A] [HasDerivedCategory A] [EnoughInjectives A]
    [Category B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] (M : A) :
    (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M)).IsGE 0 :=
  F.rightDerivedFunctorPlus_isGE ((DerivedCategory.Plus.singleFunctor A 0).obj M) 0

private theorem isIso_map_composite
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {M N P : A} (f : M ⟶ N) (g : N ⟶ P) [IsIso (F.map f)] [IsIso (F.map g)] :
    IsIso (F.map (f ≫ g)) := by
  rw [F.map_comp]
  infer_instance

private theorem exact_of_equiv_transport
    {A B C A' B' C' : Type*} [Zero C] [Zero C']
    (e₁ : A ≃ A') (e₂ : B ≃ B') (e₃ : C ≃ C') (h₀ : e₃ 0 = 0)
    (f : A → B) (g : B → C) (j : A' → B') (q : B' → C')
    (hf : Function.Injective f) (he : Function.Exact f g) (hg : Function.Surjective g)
    (hj : ∀ x, j x = e₂ (f (e₁.symm x)))
    (hq : ∀ y, q y = e₃ (g (e₂.symm y))) :
    Function.Injective j ∧ Function.Exact j q ∧ Function.Surjective q := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y h
    apply e₁.symm.injective
    apply hf
    apply e₂.injective
    exact (hj x).symm.trans (h.trans (hj y))
  · intro y
    constructor
    · intro hy
      have hz : g (e₂.symm y) = 0 :=
        e₃.injective (((hq y).symm.trans hy).trans h₀.symm)
      obtain ⟨x, hx⟩ := (he (e₂.symm y)).mp hz
      refine ⟨e₁ x, ?_⟩
      rw [hj, Equiv.symm_apply_apply, hx, Equiv.apply_symm_apply]
    · rintro ⟨x, rfl⟩
      rw [hq, hj, Equiv.symm_apply_apply, he.apply_apply_eq_zero, h₀]
  · intro z
    obtain ⟨y, hy⟩ := hg (e₃.symm z)
    refine ⟨e₂ y, ?_⟩
    rw [hq, Equiv.symm_apply_apply, hy, Equiv.apply_symm_apply]

/-- The actual structural derived unit maps each original scalar to its
original Sheaf.H class under the old section normalization. -/
theorem moduleDerivedStructureUnit_cohomology_sections (r : R) :
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let := moduleCohomologyModuleOfHom X α O 0
    moduleH0EquivOfHom X α O
      (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α (injectiveResolution O) 0
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
          (moduleDerivedStructureUnit X α)
          ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).inv.app
            (ModuleCat.of R R) r))) = α r := by
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let := moduleCohomologyModuleOfHom X α O 0
  exact (moduleDerivedGlobalSections_homology_zero_sections X α O (injectiveResolution O)
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
      (moduleDerivedStructureUnit X α)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).inv.app
        (ModuleCat.of R R) r))).trans (moduleDerivedStructureUnit_homology_apply X α r)

/-- The installed right-derived object retains the original nonnegative bound. -/
theorem moduleDerivedStructure_isGE : (moduleDerivedStructure X α).IsGE 0 :=
  rightDerived_single_isGE (moduleGlobalSectionsFunctorOfHom X α)
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf)

private theorem isZero_of_linearEquiv_subsingleton
    {A : Type*} [Ring A] (M : ModuleCat A) {N : Type*}
    [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) [Subsingleton N] : IsZero M := by
  let : Subsingleton M := ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- The passed closed-fibre dimension theorem gives the upper bound for
the actual installed derived structure object and its original action. -/
theorem moduleDerivedStructure_isLE_of_complete_surface
    [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [IsIntegral X]
    (f : X ⟶ Spec (.of R)) [IsProper f] [IsDominant f]
    (hdR : ringKrullDim R = 2) (hdX : topologicalKrullDim X ≤ 2) :
    (moduleDerivedStructure X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom)).IsLE 1 := by
  let β := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  rw [← DerivedCategory.Plus.isLE_ι_obj_iff, DerivedCategory.isLE_iff]
  intro i hi
  lift i to ℕ using (by omega)
  have hi' : 1 < i := by exact_mod_cast hi
  let := moduleCohomologyModuleOfHom X β O i
  let : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X O) i) :=
    subsingleton_moduleCohomology_of_complete_surface_modification R f hdR hdX O
      (affineLocallyFiniteType_unit X) i hi'
  exact isZero_of_linearEquiv_subsingleton _
    (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X β (injectiveResolution O) i)

/-- The complete-local surface triangle retains the literal structural
unit and original native H1, with its connecting morphism unchanged. -/
def moduleDerivedStructurePostnikov
    [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [IsIntegral X]
    (f : X ⟶ Spec (.of R)) [IsProper f] [IsDominant f]
    (hR : NormalStalks (Spec (.of R)))
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hdR : ringKrullDim R = 2) (hdX : topologicalKrullDim X ≤ 2) :
    Triangle (DerivedCategory.Plus (ModuleCat.{u} R)) := by
  let β := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let K := moduleDerivedStructure X β
  let η := moduleDerivedStructureUnit X β
  let : K.IsGE 0 := moduleDerivedStructure_isGE X β
  let : K.IsLE 1 := moduleDerivedStructure_isLE_of_complete_surface X f hdR hdX
  let : IsIso ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map η) :=
    isIso_moduleDerivedStructureUnit_homology_of_bijective X β
      (Hom.bijective_structuralCoefficients_of_isProper_birational R f hR hff)
  exact DerivedCategory.Plus.unitPostnikovTriangle η

/-- Distinguishedness is inherited from the original native truncation triangle. -/
theorem moduleDerivedStructurePostnikov_distinguished
    [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [IsIntegral X]
    (f : X ⟶ Spec (.of R)) [IsProper f] [IsDominant f]
    (hR : NormalStalks (Spec (.of R)))
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hdR : ringKrullDim R = 2) (hdX : topologicalKrullDim X ≤ 2) :
    moduleDerivedStructurePostnikov X f hR hff hdR hdX ∈ distTriang _ := by
  let β := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let K := moduleDerivedStructure X β
  let η := moduleDerivedStructureUnit X β
  let : K.IsGE 0 := moduleDerivedStructure_isGE X β
  let : K.IsLE 1 := moduleDerivedStructure_isLE_of_complete_surface X f hdR hdX
  let : IsIso ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map η) :=
    isIso_moduleDerivedStructureUnit_homology_of_bijective X β
      (Hom.bijective_structuralCoefficients_of_isProper_birational R f hR hff)
  exact DerivedCategory.Plus.unitPostnikovTriangle_distinguished η

/-- The actual derived pushforward of the structure single is nonnegative. -/
theorem moduleDerivedPushforward_isGE {Y : Scheme.{u}} (g : Y ⟶ X) :
    ((Scheme.Modules.pushforward g).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj
        (SheafOfModules.unit Y.ringCatSheaf))).IsGE 0 :=
  rightDerived_single_isGE (Scheme.Modules.pushforward g)
    (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf)

private theorem isIso_rightDerivedSingleUnit_homology
    {A B : Type*} [Category A] [Abelian A] [HasDerivedCategory A] [EnoughInjectives A]
    [Category B] [Abelian B] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] (M : A) :
    IsIso ((DerivedCategory.Plus.homologyFunctor B 0).map (F.rightDerivedSingleUnit M)) := by
  let E := DerivedCategory.singleFunctorCompHomologyFunctorIso B 0
  let η := (DerivedCategory.Plus.homologyFunctor B 0).map (F.rightDerivedSingleUnit M)
  have : IsIso (E.inv.app (F.obj M) ≫ η) := by
    rw [F.rightDerivedSingleUnit_homology_zero]
    infer_instance
  exact IsIso.of_isIso_comp_left (E.inv.app (F.obj M)) η

/-- Proper birational normality is applied to the original ordinary unit,
and the native left-exact comparison preserves its H0 isomorphism. -/
theorem isIso_moduleDerivedPushforwardUnit_homology
    [IsIntegral X] {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ X)
    [IsProper g] [IsDominant g] (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap g))) :
    IsIso ((DerivedCategory.Plus.homologyFunctor X.Modules 0).map
      (moduleDerivedPushforwardUnit X g)) := by
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let G := Scheme.Modules.pushforward g
  let H := DerivedCategory.Plus.homologyFunctor X.Modules 0
  let S := DerivedCategory.Plus.singleFunctor X.Modules 0
  let φ : OX ⟶ G.obj OY := SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom
  let : IsIso φ :=
    Scheme.Modules.isIso_unitToPushforwardObjUnit_of_isProper_birational g hX hff
  let : IsIso (H.map (G.rightDerivedSingleUnit OY)) :=
    isIso_rightDerivedSingleUnit_homology G OY
  exact isIso_map_composite H (S.map φ) (G.rightDerivedSingleUnit OY)

/-- The original derived global sections of the positive-truncation
triangle of the original structure-module pushforward unit. -/
def moduleBirationalLerayTriangle
    [IsIntegral X] {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ X)
    [IsProper g] [IsDominant g] (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap g))) :
    Triangle (DerivedCategory.Plus (ModuleCat.{u} R)) := by
  let G := Scheme.Modules.pushforward g
  let K := G.rightDerivedFunctorPlus.obj
    ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj
      (SheafOfModules.unit Y.ringCatSheaf))
  let η := moduleDerivedPushforwardUnit X g
  let : K.IsGE 0 := moduleDerivedPushforward_isGE X g
  let : IsIso ((DerivedCategory.Plus.homologyFunctor X.Modules 0).map η) :=
    isIso_moduleDerivedPushforwardUnit_homology X g hX hff
  exact (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.mapTriangle.obj
    (DerivedCategory.Plus.unitTruncationTriangle η)

/-- The actual native derived functor carries the original triangle to
a distinguished triangle. -/
theorem moduleBirationalLerayTriangle_distinguished
    [IsIntegral X] {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ X)
    [IsProper g] [IsDominant g] (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap g))) :
    moduleBirationalLerayTriangle X α g hX hff ∈ distTriang _ := by
  let G := Scheme.Modules.pushforward g
  let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let K := G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj OY)
  let η := moduleDerivedPushforwardUnit X g
  let : K.IsGE 0 := moduleDerivedPushforward_isGE X g
  let : IsIso ((DerivedCategory.Plus.homologyFunctor X.Modules 0).map η) :=
    isIso_moduleDerivedPushforwardUnit_homology X g hX hff
  exact (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map_distinguished
    (DerivedCategory.Plus.unitTruncationTriangle η)
    (DerivedCategory.Plus.unitTruncationTriangle_distinguished η)

/-- The actual degree-one homology maps of the original Leray triangle. -/
def moduleBirationalLerayShortComplex
    [IsIntegral X] {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ X)
    [IsProper g] [IsDominant g] (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap g))) :
    ShortComplex (ModuleCat.{u} R) :=
  DerivedCategory.Plus.homologyOneShortComplex (moduleBirationalLerayTriangle X α g hX hff)
    (moduleBirationalLerayTriangle_distinguished X α g hX hff)

/-- The complete-local surface supplies exactly the two adjacent
vanishings, for the original maps and original scalar action. -/
theorem moduleBirationalLerayShortComplex_shortExact
    [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [IsIntegral X]
    (f : X ⟶ Spec (.of R)) [IsProper f] [IsDominant f]
    (hdR : ringKrullDim R = 2) (hdX : topologicalKrullDim X ≤ 2)
    {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ X) [IsProper g] [IsDominant g]
    (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap g))) :
    (moduleBirationalLerayShortComplex X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) g hX hff).ShortExact := by
  let β := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let T := moduleBirationalLerayTriangle X β g hX hff
  apply DerivedCategory.Plus.homologyOneShortComplex_shortExact T
    (moduleBirationalLerayTriangle_distinguished X β g hX hff)
  · let G := Scheme.Modules.pushforward g
    let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
    let K := G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj OY)
    let P := (DerivedCategory.Plus.TStructure.t.truncGE 1).obj K
    let : P.IsGE 1 := DerivedCategory.Plus.TStructure.t.isGE_truncGE_obj K 1 1 le_rfl
    let : T.obj₃.IsGE 1 := by
      change ((moduleGlobalSectionsFunctorOfHom X β).rightDerivedFunctorPlus.obj P).IsGE 1
      exact (moduleGlobalSectionsFunctorOfHom X β).rightDerivedFunctorPlus_isGE P 1
    exact DerivedCategory.Plus.isZero_homology_of_isGE T.obj₃ 1 0 (by omega)
  · let : T.obj₁.IsLE 1 := moduleDerivedStructure_isLE_of_complete_surface X f hdR hdX
    exact DerivedCategory.Plus.isZero_homology_of_isLE T.obj₁ 1 2 (by omega)

/-- The middle object comparison is the existing original derived
pushforward/global-sections comparison, with the induced structural action. -/
def moduleBirationalLerayMiddleIso
    [IsIntegral X] {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ X)
    [IsProper g] [IsDominant g] (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap g))) :
    moduleDerivedStructure Y (g.appTop.hom.comp α) ≅
      (moduleBirationalLerayTriangle X α g hX hff).obj₂ :=
  (moduleDerivedGlobalSectionsPushforwardCompIso g α).app
    ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj
      (SheafOfModules.unit Y.ringCatSheaf))

/-- The original lowest positive layer identifies the third H1 with
actual sections of the original first higher direct image. -/
def moduleBirationalLerayEdgeIso
    [IsIntegral X] {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ X)
    [IsProper g] [IsDominant g] (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap g))) :
    (moduleBirationalLerayShortComplex X α g hX hff).X₃ ≅
      (moduleGlobalSectionsFunctorOfHom X α).obj
        (((Scheme.Modules.pushforward g).rightDerived 1).obj
          (SheafOfModules.unit Y.ringCatSheaf)) := by
  let F := moduleGlobalSectionsFunctorOfHom X α
  let G := Scheme.Modules.pushforward g
  let O : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let K := G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj O)
  let P := (DerivedCategory.Plus.TStructure.t.truncGE 1).obj K
  let : P.IsGE 1 := by dsimp [P]; infer_instance
  let e : (DerivedCategory.Plus.homologyFunctor X.Modules 1).obj P ≅
      (G.rightDerived 1).obj O :=
    (DerivedCategory.Plus.homologyTruncGEIso K 1 1 le_rfl).symm ≪≫
      (G.rightDerivedSingleHomologyIso 1).symm.app O
  exact F.rightDerivedFirstHomologyIso P ≪≫ F.mapIso e

/-- The source comparison is the original supplied-resolution comparison
with additive-sheaf cohomology and its original scalar action. -/
def moduleBirationalLeraySourceEquiv
    [IsIntegral X] {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ X)
    [IsProper g] [IsDominant g] (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap g))) :
    let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let := moduleCohomologyModuleOfHom X α O 1
    (moduleBirationalLerayShortComplex X α g hX hff).X₁ ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X O) 1 :=
  moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α
    (injectiveResolution (SheafOfModules.unit X.ringCatSheaf)) 1

/-- The middle comparison retains the native derived composition isomorphism
and the unchanged original source-cohomology comparison. -/
def moduleBirationalLerayMiddleEquiv
    [IsIntegral X] {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ X)
    [IsProper g] [IsDominant g] (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap g))) :
    let O : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
    let := moduleCohomologyModuleOfHom Y (g.appTop.hom.comp α) O 1
    (moduleBirationalLerayShortComplex X α g hX hff).X₂ ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf Y O) 1 :=
  ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 1).mapIso
      (moduleBirationalLerayMiddleIso X α g hX hff)).toLinearEquiv.symm.trans
    (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv Y (g.appTop.hom.comp α)
      (injectiveResolution (SheafOfModules.unit Y.ringCatSheaf)) 1)

/-- The original first Leray arrow transported to the actual additive
cohomology groups, retaining the structural module actions. -/
def moduleBirationalLerayMap
    [IsIntegral X] {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ X)
    [IsProper g] [IsDominant g] (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap g))) :
    let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
    let := moduleCohomologyModuleOfHom X α OX 1
    let := moduleCohomologyModuleOfHom Y (g.appTop.hom.comp α) OY 1
    Sheaf.H.{u + 1} (moduleAddSheaf X OX) 1 →ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf Y OY) 1 := by
  letI := moduleCohomologyModuleOfHom X α (SheafOfModules.unit X.ringCatSheaf) 1
  letI := moduleCohomologyModuleOfHom Y (g.appTop.hom.comp α)
    (SheafOfModules.unit Y.ringCatSheaf) 1
  exact ((moduleBirationalLerayMiddleEquiv X α g hX hff).toLinearMap.comp
      (moduleBirationalLerayShortComplex X α g hX hff).f.hom).comp
    (moduleBirationalLeraySourceEquiv X α g hX hff).symm.toLinearMap

/-- The transported first arrow evaluates through its actual source and middle comparisons. -/
theorem moduleBirationalLerayMap_apply
    [IsIntegral X] {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ X)
    [IsProper g] [IsDominant g] (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap g)))
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X (SheafOfModules.unit X.ringCatSheaf)) 1) :
    moduleBirationalLerayMap X α g hX hff x =
      moduleBirationalLerayMiddleEquiv X α g hX hff
        ((moduleBirationalLerayShortComplex X α g hX hff).f
          ((moduleBirationalLeraySourceEquiv X α g hX hff).symm x)) := rfl

/-- The original second Leray arrow followed by the actual lowest-layer
comparison to sections of the first higher direct image. -/
def moduleBirationalLerayEdge
    [IsIntegral X] {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ X)
    [IsProper g] [IsDominant g] (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap g))) :
    let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
    let := moduleCohomologyModuleOfHom Y (g.appTop.hom.comp α) OY 1
    Sheaf.H.{u + 1} (moduleAddSheaf Y OY) 1 →ₗ[R]
      (moduleGlobalSectionsFunctorOfHom X α).obj
        (((Scheme.Modules.pushforward g).rightDerived 1).obj OY) := by
  letI := moduleCohomologyModuleOfHom Y (g.appTop.hom.comp α)
    (SheafOfModules.unit Y.ringCatSheaf) 1
  exact (moduleBirationalLerayEdgeIso X α g hX hff).toLinearEquiv.toLinearMap.comp
    ((moduleBirationalLerayShortComplex X α g hX hff).g.hom.comp
      (moduleBirationalLerayMiddleEquiv X α g hX hff).symm.toLinearMap)

/-- The transported edge evaluates through the actual original second arrow and layer comparison. -/
theorem moduleBirationalLerayEdge_apply
    [IsIntegral X] {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ X)
    [IsProper g] [IsDominant g] (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap g)))
    (x : Sheaf.H.{u + 1} (moduleAddSheaf Y (SheafOfModules.unit Y.ringCatSheaf)) 1) :
    moduleBirationalLerayEdge X α g hX hff x =
      (moduleBirationalLerayEdgeIso X α g hX hff).hom
        ((moduleBirationalLerayShortComplex X α g hX hff).g
          ((moduleBirationalLerayMiddleEquiv X α g hX hff).symm x)) := rfl

/-- The actual transported Leray maps form a short exact sequence on the
original cohomology modules, with no change of scalar action or section carrier. -/
theorem moduleBirationalLeray_exact_of_complete_surface
    [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [IsIntegral X]
    (f : X ⟶ Spec (.of R)) [IsProper f] [IsDominant f]
    (hdR : ringKrullDim R = 2) (hdX : topologicalKrullDim X ≤ 2)
    {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ X) [IsProper g] [IsDominant g]
    (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap g))) :
    let β := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
    let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
    let := moduleCohomologyModuleOfHom X β OX 1
    let := moduleCohomologyModuleOfHom Y (g.appTop.hom.comp β) OY 1
    Function.Injective (moduleBirationalLerayMap X β g hX hff) ∧
      Function.Exact (moduleBirationalLerayMap X β g hX hff)
        (moduleBirationalLerayEdge X β g hX hff) ∧
      Function.Surjective (moduleBirationalLerayEdge X β g hX hff) := by
  let β := f.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  let := moduleCohomologyModuleOfHom X β (SheafOfModules.unit X.ringCatSheaf) 1
  let := moduleCohomologyModuleOfHom Y (g.appTop.hom.comp β)
    (SheafOfModules.unit Y.ringCatSheaf) 1
  let S := moduleBirationalLerayShortComplex X β g hX hff
  let e₁ := moduleBirationalLeraySourceEquiv X β g hX hff
  let e₂ := moduleBirationalLerayMiddleEquiv X β g hX hff
  let e₃ := (moduleBirationalLerayEdgeIso X β g hX hff).toLinearEquiv
  have hs : S.ShortExact :=
    moduleBirationalLerayShortComplex_shortExact X f hdR hdX g hX hff
  have he : Function.Exact S.f S.g :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hs.exact
  exact exact_of_equiv_transport e₁.toEquiv e₂.toEquiv e₃.toEquiv (map_zero e₃)
    S.f S.g (moduleBirationalLerayMap X β g hX hff) (moduleBirationalLerayEdge X β g hX hff)
    hs.moduleCat_injective_f he hs.moduleCat_surjective_g
    (moduleBirationalLerayMap_apply X β g hX hff)
    (moduleBirationalLerayEdge_apply X β g hX hff)

private def moduleOriginalDerivedAlong {Y : Scheme.{u}} (g : Y ⟶ X)
    {M : X.Modules} {N : Y.Modules} (φ : M ⟶ (Scheme.Modules.pushforward g).obj N) :
    (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) ⟶
      (moduleGlobalSectionsFunctorOfHom Y (g.appTop.hom.comp α)).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj N) :=
  (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).map φ ≫
        (Scheme.Modules.pushforward g).rightDerivedSingleUnit N) ≫
    (moduleDerivedGlobalSectionsPushforwardCompIso g α).inv.app
      ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj N)

private def moduleOriginalDerivedCohomologyAlong {Y : Scheme.{u}} (g : Y ⟶ X)
    {M : X.Modules} {N : Y.Modules} (φ : M ⟶ (Scheme.Modules.pushforward g).obj N) (n : ℕ) :
    let := moduleCohomologyModuleOfHom X α M n
    let := moduleCohomologyModuleOfHom Y (g.appTop.hom.comp α) N n
    Sheaf.H.{u + 1} (moduleAddSheaf X M) n →ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf Y N) n := by
  let := moduleCohomologyModuleOfHom X α M n
  let := moduleCohomologyModuleOfHom Y (g.appTop.hom.comp α) N n
  let eX := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α (injectiveResolution M) n
  let eY := moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv Y (g.appTop.hom.comp α)
    (injectiveResolution N) n
  exact (eY.toLinearMap.comp
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
      (moduleOriginalDerivedAlong X α g φ)).hom).comp eX.symm.toLinearMap

private theorem moduleOriginalDerivedCohomologyAlong_model {Y : Scheme.{u}} (g : Y ⟶ X)
    {M : X.Modules} {N : Y.Modules} (φ : M ⟶ (Scheme.Modules.pushforward g).obj N)
    (n : ℕ) (x) :
    moduleOriginalDerivedCohomologyAlong X α g φ n
        (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α (injectiveResolution M) n x) =
      moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv Y (g.appTop.hom.comp α)
        (injectiveResolution N) n
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) (n : ℤ)).map
          (moduleOriginalDerivedAlong X α g φ) x) := by
  simp only [moduleOriginalDerivedCohomologyAlong, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]

private theorem moduleOriginalDerivedAlong_zero {Y : Scheme.{u}} (g : Y ⟶ X)
    {M : X.Modules} {N : Y.Modules} (φ : M ⟶ (Scheme.Modules.pushforward g).obj N) :
    (moduleGlobalSectionsFunctorOfHom X α).rightDerivedSingleHomologyZeroIso.inv.app M ≫
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
          (moduleOriginalDerivedAlong X α g φ) =
      ((moduleGlobalSectionsFunctorOfHom X α).map φ ≫
        (modulePushforwardGlobalSectionsIso g α).hom.app N) ≫
          (moduleGlobalSectionsFunctorOfHom Y
            (g.appTop.hom.comp α)).rightDerivedSingleHomologyZeroIso.inv.app N := by
  let F := moduleGlobalSectionsFunctorOfHom X α
  let G := moduleGlobalSectionsFunctorOfHom Y (g.appTop.hom.comp α)
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0
  let S := DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0
  let E : S ⋙ H ≅ 𝟭 (ModuleCat.{u} R) :=
    DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0
  let c : F.obj M ⟶ G.obj N :=
    F.map φ ≫ (modulePushforwardGlobalSectionsIso g α).hom.app N
  have hu : F.rightDerivedSingleUnit M ≫ moduleOriginalDerivedAlong X α g φ =
      S.map c ≫ G.rightDerivedSingleUnit N :=
    moduleDerivedGlobalSectionsPushforwardCompIso_coefficientUnit g α φ
  have h : H.map (F.rightDerivedSingleUnit M) ≫
        H.map (moduleOriginalDerivedAlong X α g φ) =
      H.map (S.map c) ≫ H.map (G.rightDerivedSingleUnit N) :=
    (H.map_comp (F.rightDerivedSingleUnit M) (moduleOriginalDerivedAlong X α g φ)).symm.trans
      ((congrArg H.map hu).trans (H.map_comp (S.map c) (G.rightDerivedSingleUnit N)))
  have hc := E.inv.naturality c
  change c ≫ E.inv.app (G.obj N) = E.inv.app (F.obj M) ≫ H.map (S.map c) at hc
  calc
    _ = (E.inv.app (F.obj M) ≫ H.map (F.rightDerivedSingleUnit M)) ≫
        H.map (moduleOriginalDerivedAlong X α g φ) :=
      congrArg (fun k => k ≫ H.map (moduleOriginalDerivedAlong X α g φ))
        (F.rightDerivedSingleUnit_homology_zero M).symm
    _ = E.inv.app (F.obj M) ≫ H.map (S.map c) ≫ H.map (G.rightDerivedSingleUnit N) := by
      rw [Category.assoc, h]
    _ = c ≫ E.inv.app (G.obj N) ≫ H.map (G.rightDerivedSingleUnit N) :=
      congrArg (fun k => k ≫ H.map (G.rightDerivedSingleUnit N)) hc.symm
    _ = _ := by
      have hz : E.inv.app (G.obj N) ≫ H.map (G.rightDerivedSingleUnit N) =
          G.rightDerivedSingleHomologyZeroIso.inv.app N :=
        G.rightDerivedSingleUnit_homology_zero N
      exact congrArg (fun k => c ≫ k) hz

private theorem moduleOriginalDerivedAlong_zero_apply {Y : Scheme.{u}} (g : Y ⟶ X)
    {M : X.Modules} {N : Y.Modules} (φ : M ⟶ (Scheme.Modules.pushforward g).obj N)
    (x : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).obj
      ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M))) :
    (moduleGlobalSectionsFunctorOfHom Y
        (g.appTop.hom.comp α)).rightDerivedSingleHomologyZeroIso.hom.app N
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
          (moduleOriginalDerivedAlong X α g φ) x) =
      ((moduleGlobalSectionsFunctorOfHom X α).map φ ≫
        (modulePushforwardGlobalSectionsIso g α).hom.app N)
          ((moduleGlobalSectionsFunctorOfHom X α).rightDerivedSingleHomologyZeroIso.hom.app M
            x) := by
  let F := moduleGlobalSectionsFunctorOfHom X α
  let G := moduleGlobalSectionsFunctorOfHom Y (g.appTop.hom.comp α)
  let E := F.rightDerivedSingleHomologyZeroIso.app M
  let E' := G.rightDerivedSingleHomologyZeroIso.app N
  let s := E.hom x
  have hx : E.inv s = x := congrArg (fun k => k x) E.hom_inv_id
  have h := congrArg (fun k => k s) (moduleOriginalDerivedAlong_zero X α g φ)
  have hy := congrArg (fun y => E'.hom y) h
  have hcancel : E'.hom (E'.inv
      (((moduleGlobalSectionsFunctorOfHom X α).map φ ≫
        (modulePushforwardGlobalSectionsIso g α).hom.app N) s)) =
      ((moduleGlobalSectionsFunctorOfHom X α).map φ ≫
        (modulePushforwardGlobalSectionsIso g α).hom.app N) s :=
    congrArg (fun k => k
      (((moduleGlobalSectionsFunctorOfHom X α).map φ ≫
        (modulePushforwardGlobalSectionsIso g α).hom.app N) s)) E'.inv_hom_id
  exact (congrArg (fun y => E'.hom
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
      (moduleOriginalDerivedAlong X α g φ) y)) hx.symm).trans (hy.trans hcancel)

private theorem moduleCohomologyMapAlong_sections {Y : Scheme.{u}} (g : Y ⟶ X)
    {M : X.Modules} {N : Y.Modules} (φ : M ⟶ (Scheme.Modules.pushforward g).obj N)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) 0) :
    moduleH0EquivOfHom Y (g.appTop.hom.comp α) N
        (moduleCohomologyMapAlongLinear g α φ 0 x) =
      ((moduleGlobalSectionsFunctorOfHom X α).map φ ≫
        (modulePushforwardGlobalSectionsIso g α).hom.app N)
          (moduleH0EquivOfHom X α M x) := by
  have h := moduleCohomologyMapAlong_equiv₀ g φ x
  change Sheaf.H.equiv₀ (moduleAddSheaf Y N) isTerminalTop
      (moduleCohomologyMapAlong g φ 0 x) =
    (modulePushforwardGlobalSectionsIso g α).hom.app N
      ((moduleGlobalSectionsFunctorOfHom X α).map φ
        (Sheaf.H.equiv₀ (moduleAddSheaf X M) isTerminalTop x))
  let z : N.val.obj (op ⊤) :=
    (moduleGlobalSectionsFunctorOfHom X α).map φ
      (Sheaf.H.equiv₀ (moduleAddSheaf X M) isTerminalTop x)
  apply h.trans
  change (moduleAddSheaf Y N).obj.map (𝟙 (op ⊤)) z =
    (modulePushforwardGlobalSectionsIso g α).hom.app N z
  have hi : (moduleAddSheaf Y N).obj.map (𝟙 (op ⊤)) z = z :=
    congrArg (fun k : (moduleAddSheaf Y N).obj.obj (op ⊤) ⟶
      (moduleAddSheaf Y N).obj.obj (op ⊤) => k z)
      ((moduleAddSheaf Y N).obj.map_id (op ⊤))
  exact hi.trans (modulePushforwardGlobalSectionsIso_hom_app_apply g α N z).symm

private theorem moduleOriginalDerivedCohomologyAlong_zero {Y : Scheme.{u}} (g : Y ⟶ X)
    {M : X.Modules} {N : Y.Modules} (φ : M ⟶ (Scheme.Modules.pushforward g).obj N) :
    moduleOriginalDerivedCohomologyAlong X α g φ 0 = moduleCohomologyMapAlongLinear g α φ 0 := by
  let := moduleCohomologyModuleOfHom X α M 0
  let := moduleCohomologyModuleOfHom Y (g.appTop.hom.comp α) N 0
  apply LinearMap.ext
  intro x
  obtain ⟨z, rfl⟩ :=
    (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α
      (injectiveResolution M) 0).surjective x
  apply (moduleH0EquivOfHom Y (g.appTop.hom.comp α) N).injective
  have hmodel := moduleOriginalDerivedCohomologyAlong_model X α g φ 0 z
  have hnew := moduleDerivedGlobalSections_homology_zero_sections Y (g.appTop.hom.comp α)
    N (injectiveResolution N)
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
      (moduleOriginalDerivedAlong X α g φ) z)
  have hsrc := moduleDerivedGlobalSections_homology_zero_sections X α M (injectiveResolution M) z
  have hold := moduleCohomologyMapAlong_sections X α g φ
    (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α (injectiveResolution M) 0 z)
  exact (congrArg (moduleH0EquivOfHom Y (g.appTop.hom.comp α) N) hmodel).trans
    (hnew.trans ((moduleOriginalDerivedAlong_zero_apply X α g φ z).trans
      ((congrArg (fun y => ((moduleGlobalSectionsFunctorOfHom X α).map φ ≫
        (modulePushforwardGlobalSectionsIso g α).hom.app N) y) hsrc.symm).trans hold.symm)))

private def moduleOriginalCoefficientTriangleMap {Y : Scheme.{u}} (g : Y ⟶ X)
    (S : ShortComplex X.Modules) (T : ShortComplex Y.Modules)
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T.map (Scheme.Modules.pushforward g)) :
    (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.mapTriangle.obj
        hS.singleTrianglePlus ⟶
      (moduleGlobalSectionsFunctorOfHom Y
        (g.appTop.hom.comp α)).rightDerivedFunctorPlus.mapTriangle.obj
        hT.singleTrianglePlus :=
  (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus.mapTriangle.map
      ((Scheme.Modules.pushforward g).rightDerivedSingleUnitTriangleMap S T hS hT φ) ≫
    (moduleDerivedGlobalSectionsPushforwardCompTriangleIso g α).inv.app hT.singleTrianglePlus

private theorem moduleOriginalCoefficientTriangleMap_hom₁ {Y : Scheme.{u}} (g : Y ⟶ X)
    (S : ShortComplex X.Modules) (T : ShortComplex Y.Modules)
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T.map (Scheme.Modules.pushforward g)) :
    (moduleOriginalCoefficientTriangleMap X α g S T hS hT φ).hom₁ =
      moduleOriginalDerivedAlong X α g φ.τ₁ := by
  let F := (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus
  let G := Scheme.Modules.pushforward g
  let d := G.rightDerivedSingleUnitTriangleMap S T hS hT φ
  let c := (moduleDerivedGlobalSectionsPushforwardCompTriangleIso g α).inv.app
    hT.singleTrianglePlus
  let a := (DerivedCategory.Plus.singleFunctor X.Modules 0).map φ.τ₁ ≫
    G.rightDerivedSingleUnit T.X₁
  let b := (moduleDerivedGlobalSectionsPushforwardCompIso g α).inv.app
    ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj T.X₁)
  have hd : d.hom₁ = a := G.rightDerivedSingleUnitTriangleMap_hom₁ S T hS hT φ
  have hc : c.hom₁ = b :=
    moduleDerivedGlobalSectionsPushforwardCompTriangleIso_inv_hom₁ g α hT.singleTrianglePlus
  change F.map d.hom₁ ≫ c.hom₁ = F.map a ≫ b
  exact (congrArg (fun k => F.map k ≫ c.hom₁) hd).trans
    (congrArg (fun k => F.map a ≫ k) hc)

private theorem moduleOriginalCoefficientTriangleMap_hom₃ {Y : Scheme.{u}} (g : Y ⟶ X)
    (S : ShortComplex X.Modules) (T : ShortComplex Y.Modules)
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T.map (Scheme.Modules.pushforward g)) :
    (moduleOriginalCoefficientTriangleMap X α g S T hS hT φ).hom₃ =
      moduleOriginalDerivedAlong X α g φ.τ₃ := by
  let F := (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus
  let G := Scheme.Modules.pushforward g
  let d := G.rightDerivedSingleUnitTriangleMap S T hS hT φ
  let c := (moduleDerivedGlobalSectionsPushforwardCompTriangleIso g α).inv.app
    hT.singleTrianglePlus
  let a := (DerivedCategory.Plus.singleFunctor X.Modules 0).map φ.τ₃ ≫
    G.rightDerivedSingleUnit T.X₃
  let b := (moduleDerivedGlobalSectionsPushforwardCompIso g α).inv.app
    ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj T.X₃)
  have hd : d.hom₃ = a := G.rightDerivedSingleUnitTriangleMap_hom₃ S T hS hT φ
  have hc : c.hom₃ = b :=
    moduleDerivedGlobalSectionsPushforwardCompTriangleIso_inv_hom₃ g α hT.singleTrianglePlus
  change F.map d.hom₃ ≫ c.hom₃ = F.map a ≫ b
  exact (congrArg (fun k => F.map k ≫ c.hom₃) hd).trans
    (congrArg (fun k => F.map a ≫ k) hc)

private theorem moduleOriginalDerivedCohomologyAlong_connecting {Y : Scheme.{u}} (g : Y ⟶ X)
    (S : ShortComplex X.Modules) (T : ShortComplex Y.Modules)
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T.map (Scheme.Modules.pushforward g))
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X S.X₃) 0) :
    moduleOriginalDerivedCohomologyAlong X α g φ.τ₁ 1
        (moduleCohomologyConnectingOfHom X α S hS 0 x) =
      moduleCohomologyConnectingOfHom Y (g.appTop.hom.comp α) T hT 0
        (moduleOriginalDerivedCohomologyAlong X α g φ.τ₃ 0 x) := by
  let := moduleCohomologyModuleOfHom X α S.X₁ 1
  let := moduleCohomologyModuleOfHom X α S.X₃ 0
  let := moduleCohomologyModuleOfHom Y (g.appTop.hom.comp α) T.X₁ 1
  let := moduleCohomologyModuleOfHom Y (g.appTop.hom.comp α) T.X₃ 0
  obtain ⟨z, rfl⟩ :=
    (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α
      (injectiveResolution S.X₃) 0).surjective x
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0
  have hn := H.homologySequenceδ_naturality
    (moduleOriginalCoefficientTriangleMap X α g S T hS hT φ) (0 : ℤ) (1 : ℤ) (by omega)
  rw [moduleOriginalCoefficientTriangleMap_hom₁,
    moduleOriginalCoefficientTriangleMap_hom₃] at hn
  have hv := congrArg (fun k => k z) hn.symm
  change (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 1).map
      (moduleOriginalDerivedAlong X α g φ.τ₁)
      (moduleDerivedGlobalSectionsConnectingOfHom X α S hS z) =
    moduleDerivedGlobalSectionsConnectingOfHom Y (g.appTop.hom.comp α) T hT
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
        (moduleOriginalDerivedAlong X α g φ.τ₃) z) at hv
  calc
    _ = moduleOriginalDerivedCohomologyAlong X α g φ.τ₁ 1
        (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α (injectiveResolution S.X₁) 1
          (moduleDerivedGlobalSectionsConnectingOfHom X α S hS z)) :=
      congrArg (moduleOriginalDerivedCohomologyAlong X α g φ.τ₁ 1)
        (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_connecting X α S hS
          (injectiveResolution S.X₁) (injectiveResolution S.X₃) z).symm
    _ = moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv Y (g.appTop.hom.comp α)
        (injectiveResolution T.X₁) 1
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 1).map
          (moduleOriginalDerivedAlong X α g φ.τ₁)
          (moduleDerivedGlobalSectionsConnectingOfHom X α S hS z)) :=
      moduleOriginalDerivedCohomologyAlong_model X α g φ.τ₁ 1 _
    _ = moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv Y (g.appTop.hom.comp α)
        (injectiveResolution T.X₁) 1
        (moduleDerivedGlobalSectionsConnectingOfHom Y (g.appTop.hom.comp α) T hT
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
            (moduleOriginalDerivedAlong X α g φ.τ₃) z)) :=
      congrArg (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv Y (g.appTop.hom.comp α)
        (injectiveResolution T.X₁) 1) hv
    _ = moduleCohomologyConnectingOfHom Y (g.appTop.hom.comp α) T hT 0
        (moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv Y (g.appTop.hom.comp α)
          (injectiveResolution T.X₃) 0
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
            (moduleOriginalDerivedAlong X α g φ.τ₃) z)) :=
      moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_connecting Y (g.appTop.hom.comp α)
        T hT (injectiveResolution T.X₁) (injectiveResolution T.X₃) _
    _ = _ := congrArg (moduleCohomologyConnectingOfHom Y (g.appTop.hom.comp α) T hT 0)
      (moduleOriginalDerivedCohomologyAlong_model X α g φ.τ₃ 0 z).symm

private theorem originalZariskiCohomology_connecting {X Y : Scheme.{u}} (g : Y ⟶ X)
    (S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (T : ShortComplex (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}))
    (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S.map (zariskiPullback g) ⟶ T) (n : ℕ)
    (x : Sheaf.H.{u + 1} S.X₃ n) :
    zariskiCohomologyMap g S.X₁ T.X₁ φ.τ₁ (n + 1)
        (Sheaf.H.δ hS n (n + 1) rfl x) =
      Sheaf.H.δ hT n (n + 1) rfl
        (zariskiCohomologyMap g S.X₃ T.X₃ φ.τ₃ n x) := by
  let k := Ext.mk₀ ((constantPullbackIso g).inv.app (AddCommGrpCat.of (ULift.{u} ℤ)))
  let y := x.mapExactFunctor (zariskiPullback g)
  let hS' := hS.map_of_exact (zariskiPullback g)
  have he := ShortComplex.ShortExact.extClass_naturality hS' hT φ
  change (k.comp ((x.comp hS.extClass rfl).mapExactFunctor (zariskiPullback g))
      (Nat.zero_add (n + 1))).comp (Ext.mk₀ φ.τ₁) (Nat.add_zero (n + 1)) =
    ((k.comp y (Nat.zero_add n)).comp (Ext.mk₀ φ.τ₃) (Nat.add_zero n)).comp hT.extClass rfl
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
    Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero, he]
  symm
  rw [Ext.comp_assoc_of_third_deg_zero,
    Ext.comp_assoc _ _ _ (Nat.zero_add n) rfl (by omega),
    Ext.comp_assoc_of_second_deg_zero]

private def originalCoefficientSequenceMap {Y : Scheme.{u}} (g : Y ⟶ X)
    (S : ShortComplex X.Modules) (T : ShortComplex Y.Modules)
    (φ : S ⟶ T.map (Scheme.Modules.pushforward g)) :
    (moduleCoefficientSequence X S).map (zariskiPullback g) ⟶
      moduleCoefficientSequence Y T where
  τ₁ := moduleCoefficientPullback g φ.τ₁
  τ₂ := moduleCoefficientPullback g φ.τ₂
  τ₃ := moduleCoefficientPullback g φ.τ₃
  comm₁₂ :=
    (moduleCoefficientPullback_postcomp g φ.τ₁ T.f).symm.trans
      ((congrArg (moduleCoefficientPullback g) φ.comm₁₂).trans
        (moduleCoefficientPullback_precomp g S.f φ.τ₂))
  comm₂₃ :=
    (moduleCoefficientPullback_postcomp g φ.τ₂ T.g).symm.trans
      ((congrArg (moduleCoefficientPullback g) φ.comm₂₃).trans
        (moduleCoefficientPullback_precomp g S.g φ.τ₃))

private theorem moduleCohomologyMapAlong_connecting {Y : Scheme.{u}} (g : Y ⟶ X)
    (S : ShortComplex X.Modules) (T : ShortComplex Y.Modules)
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T.map (Scheme.Modules.pushforward g))
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X S.X₃) 0) :
    moduleCohomologyMapAlongLinear g α φ.τ₁ 1
        (moduleCohomologyConnectingOfHom X α S hS 0 x) =
      moduleCohomologyConnectingOfHom Y (g.appTop.hom.comp α) T hT 0
        (moduleCohomologyMapAlongLinear g α φ.τ₃ 0 x) :=
  originalZariskiCohomology_connecting g
    (moduleCoefficientSequence X S) (moduleCoefficientSequence Y T)
    (moduleCoefficientSequence_shortExact X S hS) (moduleCoefficientSequence_shortExact Y T hT)
    (originalCoefficientSequenceMap X g S T φ) 0 x

private theorem moduleOriginalDerivedCohomologyAlong_one {Y : Scheme.{u}} (g : Y ⟶ X)
    {M : X.Modules} {N : Y.Modules} (φ : M ⟶ (Scheme.Modules.pushforward g).obj N) :
    moduleOriginalDerivedCohomologyAlong X α g φ 1 = moduleCohomologyMapAlongLinear g α φ 1 := by
  let := moduleCohomologyModuleOfHom X α M 1
  let := moduleCohomologyModuleOfHom Y (g.appTop.hom.comp α) N 1
  let G := Scheme.Modules.pushforward g
  let I := injectiveResolution M
  let J := injectiveResolution N
  let i : M ⟶ I.cocomplex.X 0 := I.ι.f 0
  let j : N ⟶ J.cocomplex.X 0 := J.ι.f 0
  let : Mono i := by change Mono (I.ι.f 0); infer_instance
  let : Mono j := by change Mono (J.ι.f 0); infer_instance
  let E : X.Modules := I.cocomplex.X 0 ⨯ G.obj (J.cocomplex.X 0)
  let k : M ⟶ E := prod.lift i (φ ≫ G.map j)
  let : Mono k := by
    constructor
    intro W a b hab
    apply (cancel_mono i).mp
    simpa only [k, Category.assoc, prod.lift_fst] using
      congrArg (fun q => q ≫ (prod.fst : E ⟶ I.cocomplex.X 0)) hab
  let S : ShortComplex X.Modules := ShortComplex.mk k (cokernel.π k) (cokernel.condition k)
  let T : ShortComplex Y.Modules := ShortComplex.mk j (cokernel.π j) (cokernel.condition j)
  have hS : S.ShortExact := {
    exact := ShortComplex.exact_cokernel k
    mono_f := by change Mono k; infer_instance
    epi_g := by change Epi (cokernel.π k); infer_instance }
  have hT : T.ShortExact := {
    exact := ShortComplex.exact_cokernel j
    mono_f := by change Mono j; infer_instance
    epi_g := by change Epi (cokernel.π j); infer_instance }
  have hk : k ≫ ((prod.snd : E ⟶ G.obj (J.cocomplex.X 0)) ≫
      G.map (cokernel.π j)) = 0 := by
    dsimp only [k]
    rw [← Category.assoc, prod.lift_snd, Category.assoc,
      ← G.map_comp, cokernel.condition, G.map_zero, comp_zero]
  let φbar : S.X₃ ⟶ G.obj T.X₃ :=
    cokernel.desc k (prod.snd ≫ G.map (cokernel.π j)) hk
  let ψ : S ⟶ T.map G := {
    τ₁ := φ
    τ₂ := prod.snd
    τ₃ := φbar
    comm₁₂ := (prod.lift_snd i (φ ≫ G.map j)).symm
    comm₂₃ := (cokernel.π_desc k _ hk).symm }
  let : TopCat.Presheaf.IsFlasque E.presheaf := by
    change TopCat.Presheaf.IsFlasque
      (I.cocomplex.X 0 ⨯ (Scheme.Modules.pushforward g).obj (J.cocomplex.X 0)).presheaf
    infer_instance
  let : TopCat.Presheaf.IsFlasque (moduleAddSheaf X E).obj := by
    change TopCat.Presheaf.IsFlasque E.presheaf
    infer_instance
  let : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X E) 1) :=
    subsingleton_sheafH_of_isFlasque _ 0
  let := moduleCohomologyModuleOfHom X α S.X₃ 0
  let := moduleCohomologyModuleOfHom X α E 1
  let := moduleCohomologyModuleOfHom Y (g.appTop.hom.comp α) T.X₃ 0
  apply LinearMap.ext
  intro x
  have hex := moduleCohomologyConnectingOfHom_exact_right X α S hS 0
  obtain ⟨s, hs⟩ := (hex x).mp (Subsingleton.elim _ _)
  have hnew := moduleOriginalDerivedCohomologyAlong_connecting X α g S T hS hT ψ s
  have hold := moduleCohomologyMapAlong_connecting X α g S T hS hT ψ s
  have hzero := congrArg (fun f => f s)
    (moduleOriginalDerivedCohomologyAlong_zero X α g φbar)
  calc
    _ = moduleOriginalDerivedCohomologyAlong X α g φ 1
        (moduleCohomologyConnectingOfHom X α S hS 0 s) :=
      congrArg (moduleOriginalDerivedCohomologyAlong X α g φ 1) hs.symm
    _ = moduleCohomologyConnectingOfHom Y (g.appTop.hom.comp α) T hT 0
        (moduleOriginalDerivedCohomologyAlong X α g φbar 0 s) := hnew
    _ = moduleCohomologyConnectingOfHom Y (g.appTop.hom.comp α) T hT 0
        (moduleCohomologyMapAlongLinear g α φbar 0 s) :=
      congrArg (moduleCohomologyConnectingOfHom Y (g.appTop.hom.comp α) T hT 0) hzero
    _ = moduleCohomologyMapAlongLinear g α φ 1
        (moduleCohomologyConnectingOfHom X α S hS 0 s) := hold.symm
    _ = _ := congrArg (moduleCohomologyMapAlongLinear g α φ 1) hs

private theorem originalLinearTransport_comparison
    {A B C : ModuleCat.{u} R} {P Q : Type*}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (eX : A ≃ₗ[R] P) (eY : C ≃ₗ[R] Q) (j : C ≅ B) (f : A ⟶ B) (a : A ⟶ C)
    (L T : P →ₗ[R] Q)
    (hL : L = ((j.toLinearEquiv.symm.trans eY).toLinearMap.comp f.hom).comp
      eX.symm.toLinearMap)
    (hT : T = (eY.toLinearMap.comp a.hom).comp eX.symm.toLinearMap)
    (ha : a = f ≫ j.inv) : L = T := by
  rw [hL, hT, ha]
  apply LinearMap.ext
  intro x
  rfl

/-- The existing first Leray arrow is the separately published original
geometric cohomology map, with the same structure unit and scalar action. -/
theorem moduleBirationalLerayMap_eq_moduleCohomologyMapAlongLinear
    [IsIntegral X] {Y : Scheme.{u}} [IsIntegral Y] (g : Y ⟶ X)
    [IsProper g] [IsDominant g] (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap g))) :
    moduleBirationalLerayMap X α g hX hff =
      moduleCohomologyMapAlongLinear g α
        (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) 1 := by
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let := moduleCohomologyModuleOfHom X α OX 1
  let := moduleCohomologyModuleOfHom Y (g.appTop.hom.comp α) OY 1
  let φ : OX ⟶ (Scheme.Modules.pushforward g).obj OY :=
    SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 1
  let S := moduleBirationalLerayShortComplex X α g hX hff
  let V : ModuleCat.{u} R := H.obj (moduleDerivedStructure Y (g.appTop.hom.comp α))
  let eX := moduleBirationalLeraySourceEquiv X α g hX hff
  let eY : V ≃ₗ[R] Sheaf.H.{u + 1} (moduleAddSheaf Y OY) 1 :=
    moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv Y (g.appTop.hom.comp α)
      (injectiveResolution OY) 1
  let j : V ≅ S.X₂ := H.mapIso (moduleBirationalLerayMiddleIso X α g hX hff)
  let a : S.X₁ ⟶ V := H.map (moduleOriginalDerivedAlong X α g φ)
  have ha : a = S.f ≫ j.inv := by
    let F := (moduleGlobalSectionsFunctorOfHom X α).rightDerivedFunctorPlus
    let b := F.map (moduleDerivedPushforwardUnit X g)
    let c := (moduleDerivedGlobalSectionsPushforwardCompIso g α).inv.app
      ((DerivedCategory.Plus.singleFunctor Y.Modules 0).obj OY)
    change H.map (b ≫ c) = H.map b ≫ H.map c
    exact H.map_comp b c
  have hL : moduleBirationalLerayMap X α g hX hff =
      ((j.toLinearEquiv.symm.trans eY).toLinearMap.comp S.f.hom).comp
        eX.symm.toLinearMap := rfl
  have hT : moduleOriginalDerivedCohomologyAlong X α g φ 1 =
      (eY.toLinearMap.comp a.hom).comp eX.symm.toLinearMap := rfl
  have hnormal := originalLinearTransport_comparison eX eY j S.f a
    (moduleBirationalLerayMap X α g hX hff)
    (moduleOriginalDerivedCohomologyAlong X α g φ 1) hL hT ha
  exact hnormal.trans (moduleOriginalDerivedCohomologyAlong_one X α g φ)


end AlgebraicGeometry.Scheme.Cohomology
