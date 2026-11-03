/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethOpen
public import Aglib.AlgebraicGeometry.Cohomology.Restriction.CoefficientSquare
public import Aglib.AlgebraicGeometry.Modules.Restriction.Unit

/-!
# The original Künneth map on an affine open of the fixed second factor

The canonical open comparison retains the original local section action.
The normalized scalar-extension map on the actual product-open square then
identifies the original mixed tensor map, before its bijectivity is proved.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct DirectSum ChangeOfRings

universe u u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃

namespace CategoryTheory.Abelian.Ext

private theorem map_precomp_conj
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w₁} C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w₂} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {A L : C} {B K : D} (s : K ⟶ F.obj L) (g : L ⟶ A) (e : F.obj A ≅ B)
    {n : ℕ} (z : Ext.{w₁} A A n) :
    ((Ext.mk₀ s).comp (((Ext.mk₀ g).comp z (Nat.zero_add n)).mapExactFunctor F)
        (Nat.zero_add n)).comp (Ext.mk₀ e.hom) (Nat.add_zero n) =
      (Ext.mk₀ (s ≫ F.map g ≫ e.hom)).comp
        (((Ext.mk₀ e.inv).comp (z.mapExactFunctor F) (Nat.zero_add n)).comp
          (Ext.mk₀ e.hom) (Nat.add_zero n)) (Nat.zero_add n) := by
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc_of_third_deg_zero, ← Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end CategoryTheory.Abelian.Ext

namespace CategoryTheory.Functor

private theorem extBifunctorWithMaps_mk₀_right_conj
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w₁} C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w₂} D]
    {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasExt.{w₃} E]
    (F : C ⥤ D ⥤ E) [F.Additive] [∀ A, (F.obj A).Additive]
    [∀ A, PreservesFiniteLimits (F.obj A)] [∀ A, PreservesFiniteColimits (F.obj A)]
    [∀ B, PreservesFiniteLimits (F.flip.obj B)]
    [∀ B, PreservesFiniteColimits (F.flip.obj B)] [∀ B, (F.flip.obj B).Additive]
    {A : C} {B L : D} {K V : E}
    (s : K ⟶ (F.obj A).obj L) (e : (F.obj A).obj B ≅ V)
    (g : L ⟶ B) {n : ℕ} (x : Ext.{w₁} A A n) :
    F.extBifunctorWithMaps s e.hom (Nat.add_zero n) x (Ext.mk₀ g) =
      (Ext.mk₀ (s ≫ (F.obj A).map g ≫ e.hom)).comp
        (((Ext.mk₀ e.inv).comp (x.mapExactFunctor (F.flip.obj B)) (Nat.zero_add n)).comp
          (Ext.mk₀ e.hom) (Nat.add_zero n)) (Nat.zero_add n) := by
  rw [extBifunctorWithMaps_apply, F.extBifunctor_mk₀_right]
  simp only [← Ext.comp_assoc_of_third_deg_zero, ← Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The canonical open comparison followed by the actual restricted-unit isomorphism. -/
def moduleOpenUnitNormalize (A : Scheme.{u}) (D : A.Opens) (n : ℕ) :
    Sheaf.H'.{u + 1} (moduleAddSheaf A (SheafOfModules.unit A.ringCatSheaf)) n D ≃+
      Sheaf.H.{u + 1}
        (moduleAddSheaf D.toScheme (SheafOfModules.unit D.toScheme.ringCatSheaf)) n := by
  let e := (SheafOfModules.toSheaf D.toScheme.ringCatSheaf).mapIso (restrictUnitIso D.ι)
  let H : Sheaf (Opens.grothendieckTopology D.toScheme) AddCommGrpCat.{u} ⥤
      AddCommGrpCat.{u + 1} := Sheaf.functorH _ n
  exact (sheafHPrimeOpenRestrictionAddEquiv A D
    (moduleAddSheaf A (SheafOfModules.unit A.ringCatSheaf)) n).trans
      (H.mapIso e).addCommGroupIsoToAddEquiv

/-- The original restriction normalization uses the original geometric structure map. -/
theorem moduleOpenUnitNormalize_geometric (A : Scheme.{u}) (D : A.Opens) (n : ℕ)
    (x : Sheaf.H'.{u + 1} (moduleAddSheaf A (SheafOfModules.unit A.ringCatSheaf)) n D) :
    moduleOpenUnitNormalize A D n x =
      sheafHPrimeTopAddEquiv D.toScheme
        (moduleAddSheaf D.toScheme (SheafOfModules.unit D.toScheme.ringCatSheaf)) n
        ((Sheaf.cohomologyPresheaf
          (moduleAddSheaf D.toScheme (SheafOfModules.unit D.toScheme.ringCatSheaf)) n).map
          (eqToHom D.ι_preimage_self.symm).op
          ((zariskiCohomologyOpenMap D.ι
            (moduleAddSheaf A (SheafOfModules.unit A.ringCatSheaf))
            (moduleAddSheaf D.toScheme (SheafOfModules.unit D.toScheme.ringCatSheaf))
            (structurePullbackMap D.ι) n).app (op D) x)) := by
  let M : A.Modules := SheafOfModules.unit A.ringCatSheaf
  let ε := (restrictUnitIso D.ι).hom
  have hPost := moduleOpenRestrictionCoefficientSquare_apply A D M ε n x
  have hR := restrictUnitIso_hom_adjoint D.ι
  have hP := pullbackUnitIso_homEquiv D.ι
  rw [Adjunction.homEquiv_unit] at hR hP
  have hφ := hR.trans hP.symm
  have hCoef : moduleCoefficientPullback D.ι
      ((Scheme.Modules.restrictAdjunction D.ι).unit.app M ≫
        (Scheme.Modules.pushforward D.ι).map ε) = structurePullbackMap D.ι := by
    rw [hφ, moduleCoefficientPullback_postcomp]
    exact modulePullbackAdditiveComparison_unit D.ι
  dsimp only [moduleOpenRestrictionCoefficientSquare,
    TopCat.Sheaf.openCohomologyRestrictionCoefficientSquare,
    Functor.extDiagramOpenRestrictionCoefficientSquare, openRestrictionCoefficientSquare] at hPost
  rw [hCoef] at hPost
  change Sheaf.H.map ((SheafOfModules.toSheaf D.toScheme.ringCatSheaf).map ε) n
    (sheafHPrimeOpenRestrictionAddEquiv A D (moduleAddSheaf A M) n x) = _
  exact hPost

/-- The original normalized source arrow represents the actual pulled-back section. -/
theorem openFreePullback_unit_sections {A B : Scheme.{u}} (p : B ⟶ A) (D : A.Opens)
    (g : openFree A D ⟶ SheafOfModules.unit A.ringCatSheaf) :
    openFreeHomEquiv B (p ⁻¹ᵁ D) (SheafOfModules.unit B.ringCatSheaf)
        ((openFreePullbackIso p D).inv ≫ (Scheme.Modules.pullback p).map g ≫
          (pullbackUnitIso p).hom) =
      p.app D (openFreeHomEquiv A D (SheafOfModules.unit A.ringCatSheaf) g) := by
  let γ := (openFreePullbackIso p D).inv ≫ (Scheme.Modules.pullback p).map g ≫
    (pullbackUnitIso p).hom
  have h := openFreePullbackIso_homEquiv p D (SheafOfModules.unit B.ringCatSheaf) γ
  dsimp only [γ] at h
  rw [Iso.hom_inv_id_assoc, Adjunction.homEquiv_naturality_left,
    pullbackUnitIso_homEquiv, openFreeHomEquiv_comp] at h
  exact h.symm

/-- Flat module pullback and its actual unit coefficient give the original open structure map. -/
private theorem moduleOpenExtCohomologyMap_pullback_unit {A B : Scheme.{u}}
    (p : B ⟶ A) [Flat p] (D : A.Opens) (n : ℕ)
    (x : Ext.{u + 1} (C := A.Modules) (openFree A D)
      (SheafOfModules.unit A.ringCatSheaf) n) :
    (zariskiCohomologyOpenMap p
        (moduleAddSheaf A (SheafOfModules.unit A.ringCatSheaf))
        (moduleAddSheaf B (SheafOfModules.unit B.ringCatSheaf))
        (structurePullbackMap p) n).app (op D)
      (moduleOpenExtCohomologyMap A D (SheafOfModules.unit A.ringCatSheaf) n x) =
      moduleOpenExtCohomologyMap B (p ⁻¹ᵁ D) (SheafOfModules.unit B.ringCatSheaf) n
        (((Ext.mk₀ (openFreePullbackIso p D).inv).comp
          (x.mapExactFunctor (Scheme.Modules.pullback p)) (Nat.zero_add n)).comp
            (Ext.mk₀ (pullbackUnitIso p).hom) (Nat.add_zero n)) := by
  let M : A.Modules := SheafOfModules.unit A.ringCatSheaf
  let N : B.Modules := (Scheme.Modules.pullback p).obj M
  let η : M ⟶ (Scheme.Modules.pushforward p).obj N :=
    (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
  let ψ : N ⟶ SheafOfModules.unit B.ringCatSheaf := (pullbackUnitIso p).hom
  have hPull := moduleOpenExtCohomologyMap_pullback p D M n x
  have hPost := moduleOpenExtCohomologyMap_naturality B (p ⁻¹ᵁ D) ψ n
    ((Ext.mk₀ (openFreePullbackIso p D).inv).comp
      (x.mapExactFunctor (Scheme.Modules.pullback p)) (Nat.zero_add n))
  have hCoef := zariskiCohomologyOpenMap_module_postcomp p η ψ n
  have hUnit : moduleCoefficientPullback p (η ≫ (Scheme.Modules.pushforward p).map ψ) =
      structurePullbackMap p := by
    rw [moduleCoefficientPullback_postcomp]
    exact modulePullbackAdditiveComparison_unit p
  dsimp only [modulePostcompositionCohomologySquare, zariskiCohomologyCoefficientSquare,
    TopCat.Sheaf.openCohomologyCoefficientSquare, Functor.extDiagramCoefficientSquare] at hCoef
  rw [hUnit] at hCoef
  have hValue := ConcreteCategory.congr_hom (NatTrans.congr_app hCoef (op D))
    (moduleOpenExtCohomologyMap A D M n x)
  have hMap := congrArg
    (fun y : Sheaf.H'.{u + 1} (moduleAddSheaf B N) n (p ⁻¹ᵁ D) =>
      (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology B) n).map
        ((SheafOfModules.toSheaf B.ringCatSheaf).map ψ)).app (op (p ⁻¹ᵁ D))) y) hPull
  have hFinal := hValue.trans (hMap.trans hPost.symm)
  exact hFinal

/-- The canonical top source arrow for restriction of the actual open-free module. -/
private def moduleOpenRestrictionSource (A : Scheme.{u}) (D : A.Opens) :
    openFree D.toScheme ⊤ ⟶ (Scheme.Modules.pullback D.ι).obj (openFree A D) :=
  (openFreeFunctor D.toScheme).map (eqToHom D.ι_preimage_self.symm) ≫
    (openFreePullbackIso D.ι D).inv

/-- The original normalized local source arrow, retaining the actual top-open transport. -/
private def moduleOpenUnitSource (A : Scheme.{u}) (D : A.Opens)
    (g : openFree A D ⟶ SheafOfModules.unit A.ringCatSheaf) :
    openFree D.toScheme ⊤ ⟶ SheafOfModules.unit D.toScheme.ringCatSheaf :=
  moduleOpenRestrictionSource A D ≫ (Scheme.Modules.pullback D.ι).map g ≫
    (pullbackUnitIso D.ι).hom

/-- The original canonical open comparison is the exact native module pullback on Ext. -/
private theorem moduleOpenUnitNormalize_ext (A : Scheme.{u}) (D : A.Opens) (n : ℕ)
    (x : Ext.{u + 1} (C := A.Modules) (openFree A D)
      (SheafOfModules.unit A.ringCatSheaf) n) :
    moduleOpenUnitNormalize A D n
        (moduleOpenExtCohomologyMap A D (SheafOfModules.unit A.ringCatSheaf) n x) =
      sheafHPrimeTopAddEquiv D.toScheme
        (moduleAddSheaf D.toScheme (SheafOfModules.unit D.toScheme.ringCatSheaf)) n
        (moduleOpenExtCohomologyMap D.toScheme ⊤
          (SheafOfModules.unit D.toScheme.ringCatSheaf) n
          (((Ext.mk₀ (moduleOpenRestrictionSource A D)).comp
            (x.mapExactFunctor (Scheme.Modules.pullback D.ι)) (Nat.zero_add n)).comp
              (Ext.mk₀ (pullbackUnitIso D.ι).hom) (Nat.add_zero n))) := by
  rw [moduleOpenUnitNormalize_geometric, moduleOpenExtCohomologyMap_pullback_unit]
  rw [← moduleOpenExtCohomologyMap_restriction]
  apply congrArg (sheafHPrimeTopAddEquiv D.toScheme
    (moduleAddSheaf D.toScheme (SheafOfModules.unit D.toScheme.ringCatSheaf)) n)
  apply congrArg (moduleOpenExtCohomologyMap D.toScheme ⊤
    (SheafOfModules.unit D.toScheme.ringCatSheaf) n)
  rw [← Ext.comp_assoc_of_third_deg_zero, ← Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀]
  rfl

/-- At the top, an original open-free arrow is the original unit map followed by its section. -/
private theorem moduleOpenTopUnitMap_unitMul (A : Scheme.{u})
    (g : openFree A ⊤ ⟶ SheafOfModules.unit A.ringCatSheaf) :
    moduleOpenTopUnitMap A ≫
        unitMul A (openFreeHomEquiv A ⊤ (SheafOfModules.unit A.ringCatSheaf) g) = g := by
  apply (openFreeHomEquiv A ⊤ (SheafOfModules.unit A.ringCatSheaf)).injective
  rw [openFreeHomEquiv_comp]
  change Scheme.Modules.Hom.app (unitMul A _) ⊤
      ((openFreeHomEquiv A ⊤ (SheafOfModules.unit A.ringCatSheaf))
        ((openFreeHomEquiv A ⊤ (SheafOfModules.unit A.ringCatSheaf)).symm (1 : Γ(A, ⊤)))) = _
  rw [Equiv.apply_symm_apply, unitMul_app, one_mul]
  change A.presheaf.map (𝟙 (op ⊤)) _ = _
  rw [CategoryTheory.Functor.map_id]
  rfl


/-- Local source multiplication is the actual coefficient endomorphism
after canonical restriction. -/
private theorem moduleOpenUnitNormalize_precomp (A : Scheme.{u}) (D : A.Opens) (n : ℕ)
    (g : openFree A D ⟶ SheafOfModules.unit A.ringCatSheaf)
    (z : Ext.{u + 1} (C := A.Modules) (SheafOfModules.unit A.ringCatSheaf)
      (SheafOfModules.unit A.ringCatSheaf) n) :
    moduleOpenUnitNormalize A D n
        (moduleOpenExtCohomologyMap A D (SheafOfModules.unit A.ringCatSheaf) n
          ((Ext.mk₀ g).comp z (Nat.zero_add n))) =
      Sheaf.H.map
        (moduleScalarOfGlobal D.toScheme (SheafOfModules.unit D.toScheme.ringCatSheaf)
          (openFreeHomEquiv D.toScheme ⊤ (SheafOfModules.unit D.toScheme.ringCatSheaf)
            (moduleOpenUnitSource A D g))) n
        (structureCohomologyPullback D.ι n
          (moduleExtCohomologyMap A (SheafOfModules.unit A.ringCatSheaf) n z)) := by
  let B := D.toScheme
  let O : B.Modules := SheafOfModules.unit B.ringCatSheaf
  let g' := moduleOpenUnitSource A D g
  let s := openFreeHomEquiv B ⊤ O g'
  let z' : Ext.{u + 1} (C := B.Modules) O O n :=
    ((Ext.mk₀ (pullbackUnitIso D.ι).inv).comp
      (z.mapExactFunctor (Scheme.Modules.pullback D.ι)) (Nat.zero_add n)).comp
        (Ext.mk₀ (pullbackUnitIso D.ι).hom) (Nat.add_zero n)
  let Q := moduleOpenExtCohomologyMap B ⊤ O n
  let T := sheafHPrimeTopAddEquiv B (moduleAddSheaf B O) n
  have hNormalize := moduleOpenUnitNormalize_ext A D n ((Ext.mk₀ g).comp z (Nat.zero_add n))
  have hAlgebra := Ext.map_precomp_conj (Scheme.Modules.pullback D.ι)
    (moduleOpenRestrictionSource A D) g (pullbackUnitIso D.ι) z
  have hStep := hNormalize.trans (congrArg (fun e => T (Q e)) hAlgebra)
  have hSource := moduleOpenTopUnitMap_unitMul B g'
  have hSourceExt := congrArg
    (fun h : openFree B ⊤ ⟶ O => (Ext.mk₀ h).comp z' (Nat.zero_add n)) hSource.symm
  have hAssoc := Ext.mk₀_comp_mk₀_assoc (moduleOpenTopUnitMap B) (unitMul B s) z'
  have hTop := moduleOpenExtCohomologyMap_top B O n
    ((Ext.mk₀ (unitMul B s)).comp z' (Nat.zero_add n))
  have hScalar := moduleExtCohomologyMap_unitMul B O n s z'
  have hPull := moduleUnitExtCohomologyMap_pullback D.ι n z
  have hLast := congrArg (Sheaf.H.map (moduleScalarOfGlobal B O s) n) hPull.symm
  have hFinal := hStep.trans
    ((congrArg (fun e => T (Q e)) (hSourceExt.trans hAssoc.symm)).trans
      (hTop.trans (hScalar.trans hLast)))
  exact hFinal


/-- The native identification of sections on an open with global sections of that open scheme. -/
private def openUnitSectionsIso (A : Scheme.{u}) (D : A.Opens) :
    Γ(A, D) ≅ Γ(D.toScheme, ⊤) :=
  A.presheaf.mapIso (eqToIso (show D.ι ''ᵁ ⊤ = D by simp)).op

private theorem moduleOpenUnitSource_sections (A : Scheme.{u}) (D : A.Opens)
    (g : openFree A D ⟶ SheafOfModules.unit A.ringCatSheaf) :
    openFreeHomEquiv D.toScheme ⊤ (SheafOfModules.unit D.toScheme.ringCatSheaf)
        (moduleOpenUnitSource A D g) =
      (openUnitSectionsIso A D).hom
        (openFreeHomEquiv A D (SheafOfModules.unit A.ringCatSheaf) g) := by
  dsimp only [moduleOpenUnitSource, moduleOpenRestrictionSource]
  rw [Category.assoc, openFreeHomEquiv_naturality_open, openFreePullback_unit_sections]
  change D.toScheme.presheaf.map (eqToHom D.ι_preimage_self.symm).op
      (D.ι.app D (openFreeHomEquiv A D (SheafOfModules.unit A.ringCatSheaf) g)) = _
  rw [Scheme.Opens.toScheme_presheaf_map, Scheme.Opens.ι_app]
  change A.presheaf.map _ (A.presheaf.map _ _) = A.presheaf.map _ _
  rw [← CommRingCat.comp_apply, ← CategoryTheory.Functor.map_comp]
  congr 2

private theorem openUnitSectionsIso_pullback {A B : Scheme.{u}} (p : B ⟶ A)
    (D : A.Opens) :
    (openUnitSectionsIso A D).hom ≫ (p ∣_ D).appTop =
      p.app D ≫ (openUnitSectionsIso B (p ⁻¹ᵁ D)).hom := by
  have hn := p.naturality (eqToHom (show D.ι ''ᵁ ⊤ = D by simp)).op
  change A.presheaf.map (eqToHom (show D.ι ''ᵁ ⊤ = D by simp)).op ≫
      p.app (D.ι ''ᵁ ⊤) = p.app D ≫ B.presheaf.map _ at hn
  change A.presheaf.map (eqToHom (show D.ι ''ᵁ ⊤ = D by simp)).op ≫
      (p ∣_ D).appTop = p.app D ≫ B.presheaf.map _
  rw [morphismRestrict_appTop, ← Category.assoc, hn, Category.assoc,
    ← CategoryTheory.Functor.map_comp]
  congr 2

private theorem moduleOpenUnitNormalize_mk₀_sections (A : Scheme.{u}) (D : A.Opens)
    (g : openFree A D ⟶ SheafOfModules.unit A.ringCatSheaf) :
    Sheaf.H.equiv₀
        (moduleAddSheaf D.toScheme (SheafOfModules.unit D.toScheme.ringCatSheaf))
        isTerminalTop
        (moduleOpenUnitNormalize A D 0
          (moduleOpenExtCohomologyMap A D (SheafOfModules.unit A.ringCatSheaf) 0
            (Ext.mk₀ g))) =
      (openUnitSectionsIso A D).hom
        (openFreeHomEquiv A D (SheafOfModules.unit A.ringCatSheaf) g) := by
  let B := D.toScheme
  let O : B.Modules := SheafOfModules.unit B.ringCatSheaf
  let g' := moduleOpenUnitSource A D g
  let s := openFreeHomEquiv B ⊤ O g'
  let Q := moduleOpenExtCohomologyMap B ⊤ O 0
  let T := sheafHPrimeTopAddEquiv B (moduleAddSheaf B O) 0
  have hNormalize := moduleOpenUnitNormalize_ext A D 0 (Ext.mk₀ g)
  simp only [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Category.assoc] at hNormalize
  have hSource := moduleOpenTopUnitMap_unitMul B g'
  have hSourceExt := congrArg (fun h : openFree B ⊤ ⟶ O => Ext.mk₀ h) hSource.symm
  have hComp := Ext.mk₀_comp_mk₀ (moduleOpenTopUnitMap B) (unitMul B s)
  have hTop := moduleOpenExtCohomologyMap_top B O 0 (Ext.mk₀ (unitMul B s))
  have hStep := hNormalize.trans
    ((congrArg (fun e => T (Q e)) (hSourceExt.trans hComp.symm)).trans hTop)
  have hH0 := congrArg (Sheaf.H.equiv₀ (moduleAddSheaf B O) isTerminalTop) hStep
  have hSection : Sheaf.H.equiv₀ (moduleAddSheaf B O) isTerminalTop
      (moduleExtCohomologyMap B O 0 (Ext.mk₀ (unitMul B s))) = s := by
    rw [moduleExtCohomologyMap_mk₀_sections, unitHomGlobalSectionsEquiv_apply,
      unitMul_app, one_mul]
    change B.presheaf.map (𝟙 (op ⊤)) s = s
    rw [CategoryTheory.Functor.map_id]
    rfl
  have hFinal := (hH0.trans hSection).trans (moduleOpenUnitSource_sections A D g)
  exact hFinal

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- The original local H0 comparison, with the actual restricted structural constants. -/
def structureOpenH0Equiv (Y : FScheme k) (U : Y.left.Opens) :
    letI : Module k Γ(U.toScheme, ⊤) := (U.ι.appTop.hom.comp (constants Y)).toModule
    structureOpenCohomology Y U 0 ≃ₗ[k] Γ(U.toScheme, ⊤) := by
  let σ := U.ι.appTop.hom.comp (constants Y)
  let M : Y.left.Modules := SheafOfModules.unit Y.left.ringCatSheaf
  letI : Module k Γ(U.toScheme, ⊤) := σ.toModule
  exact (moduleHPrimeOpenLinearEquiv Y.left (constants Y) M U 0).trans
    ((moduleCohomologyIsoOfHom U.toScheme σ (restrictUnitIso U.ι) 0).toLinearEquiv.trans
      (moduleH0EquivOfHom U.toScheme σ (SheafOfModules.unit U.toScheme.ringCatSheaf)))

/-- The forward local H0 equivalence is the canonical restricted cohomology comparison. -/
theorem structureOpenH0Equiv_apply (Y : FScheme k) (U : Y.left.Opens)
    (y : structureOpenCohomology Y U 0) :
    structureOpenH0Equiv Y U y =
      Sheaf.H.equiv₀
        (moduleAddSheaf U.toScheme (SheafOfModules.unit U.toScheme.ringCatSheaf))
        isTerminalTop (moduleOpenUnitNormalize Y.left U 0 y) := rfl

private theorem structureOpenH0Equiv_mk₀ (Y : FScheme k) (U : Y.left.Opens)
    (g : openFree Y.left U ⟶ SheafOfModules.unit Y.left.ringCatSheaf) :
    structureOpenH0Equiv Y U
        (moduleOpenExtCohomologyMap Y.left U (SheafOfModules.unit Y.left.ringCatSheaf) 0
          (Ext.mk₀ g)) =
      (openUnitSectionsIso Y.left U).hom
        (openFreeHomEquiv Y.left U (SheafOfModules.unit Y.left.ringCatSheaf) g) :=
  moduleOpenUnitNormalize_mk₀_sections Y.left U g

/-- The canonical source normalization uses the original local H0 section and tensor symmetry. -/
def structureOpenAffineSourceEquiv (X Y : FScheme k) (U : Y.left.Opens) (n : ℕ) :
    letI : Module k Γ(U.toScheme, ⊤) := (U.ι.appTop.hom.comp (constants Y)).toModule
    structureCohomology k X n ⊗[k] structureOpenCohomology Y U 0 ≃ₗ[k]
      Γ(U.toScheme, ⊤) ⊗[k] structureCohomology k X n := by
  letI : Module k Γ(U.toScheme, ⊤) := (U.ι.appTop.hom.comp (constants Y)).toModule
  exact (TensorProduct.congr (LinearEquiv.refl k (structureCohomology k X n))
      (structureOpenH0Equiv Y U)).trans
    (TensorProduct.comm k (structureCohomology k X n) Γ(U.toScheme, ⊤))

@[simp]
theorem structureOpenAffineSourceEquiv_tmul (X Y : FScheme k) (U : Y.left.Opens) (n : ℕ)
    (x : structureCohomology k X n) (y : structureOpenCohomology Y U 0) :
    letI : Module k Γ(U.toScheme, ⊤) := (U.ι.appTop.hom.comp (constants Y)).toModule
    structureOpenAffineSourceEquiv X Y U n (x ⊗ₜ[k] y) =
      structureOpenH0Equiv Y U y ⊗ₜ[k] x := by
  let : Module k Γ(U.toScheme, ⊤) := (U.ι.appTop.hom.comp (constants Y)).toModule
  simp only [structureOpenAffineSourceEquiv, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply, TensorProduct.comm_tmul]


/-- The mixed degree-zero factor acts by its actual local section on the original first pullback. -/
theorem structureExternalOpenTensor_zero_right (X Y : FScheme k) (U : Y.left.Opens)
    (n : ℕ) (x : structureCohomology k X n) (y : structureOpenCohomology Y U 0) :
    moduleOpenUnitNormalize (X ⊗ Y).left ((snd X Y).left ⁻¹ᵁ U) n
        (structureExternalOpenTensor X Y U (Nat.add_zero n) (x ⊗ₜ[k] y)) =
      Sheaf.H.map
        (moduleScalarOfGlobal ((snd X Y).left ⁻¹ᵁ U).toScheme
          (SheafOfModules.unit ((snd X Y).left ⁻¹ᵁ U).toScheme.ringCatSheaf)
          (((snd X Y).left ∣_ U).appTop (structureOpenH0Equiv Y U y))) n
        (structureCohomologyPullback
          (((snd X Y).left ⁻¹ᵁ U).ι ≫ (fst X Y).left) n x) := by
  let := moduleCategoryLinearOfHom X.left (constants X)
  let := moduleCategoryLinearOfHom Y.left (constants Y)
  let x' := (structureExtLinearEquiv X n).symm x
  let y' := (structureOpenExtLinearEquiv Y U 0).symm y
  let g := Ext.homEquiv₀ y'
  have hx := (structureExtLinearEquiv X n).apply_symm_apply x
  have hg := Ext.mk₀_homEquiv₀_apply y'
  have hy := (congrArg (structureOpenExtLinearEquiv Y U 0) hg).trans
    ((structureOpenExtLinearEquiv Y U 0).apply_symm_apply y)
  let Z := (X ⊗ Y).left
  let V := (snd X Y).left ⁻¹ᵁ U
  let O : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  let e := externalTensorUnitIso X.hom Y.hom
  let γ : openFree Z V ⟶ O :=
    (openFreePullbackIso (snd X Y).left U).inv ≫
      (Scheme.Modules.pullback (snd X Y).left).map g ≫ (pullbackUnitIso (snd X Y).left).hom
  let z : Ext.{u + 1} (C := Z.Modules) O O n :=
    ((Ext.mk₀ e.inv).comp
      (x'.mapExactFunctor ((externalTensor X.hom Y.hom).flip.obj
        (SheafOfModules.unit Y.left.ringCatSheaf))) (Nat.zero_add n)).comp
          (Ext.mk₀ e.hom) (Nat.add_zero n)
  have hExt := Functor.extBifunctorWithMaps_mk₀_right_conj
    (externalTensor X.hom Y.hom) ((structureExternalOpenSourceIso X Y).app U).inv e g x'
  rw [structureExternalOpenSourceIso_coefficient] at hExt
  have hOriginal := congrArg (fun yy =>
    structureExternalOpenExt X Y U (Nat.add_zero n) x' yy) hg
  have hExt' := hOriginal.symm.trans hExt
  have hNormalize := moduleOpenUnitNormalize_precomp Z V n γ z
  have hMixed := congrArg
    (fun t : Ext.{u + 1} (C := Z.Modules) (openFree Z V) O n =>
      moduleOpenUnitNormalize Z V n (moduleOpenExtCohomologyMap Z V O n t)) hExt'
  have hValue := structureExternalOpenCup_apply X Y U (Nat.add_zero n) x y
  have hTensor := structureExternalOpenTensor_tmul X Y U (Nat.add_zero n) x y
  have hStart := congrArg (moduleOpenUnitNormalize Z V n) (hTensor.trans hValue)
  have hLocal := hStart.trans (hMixed.trans hNormalize)
  have hSection := moduleOpenUnitSource_sections Z V γ
  have hPullSection := openFreePullback_unit_sections (snd X Y).left U g
  have hSectionsMap := ConcreteCategory.congr_hom
    (openUnitSectionsIso_pullback (snd X Y).left U)
    (openFreeHomEquiv Y.left U (SheafOfModules.unit Y.left.ringCatSheaf) g)
  have hH0 := (congrArg (structureOpenH0Equiv Y U) hy).symm.trans
    (structureOpenH0Equiv_mk₀ Y U g)
  have hS := ((hSection.trans (congrArg (openUnitSectionsIso Z V).hom hPullSection)).trans
    hSectionsMap.symm).trans (congrArg ((snd X Y).left ∣_ U).appTop hH0.symm)
  have hFirst := structureExtLinearEquiv_fst_external X Y n x'
  have hFirst' := hFirst.symm.trans
    (congrArg (structureCohomologyPullbackLinear (fst X Y) n) hx)
  have hFirstOpen := congrArg (structureCohomologyPullback V.ι n) hFirst'
  have hComp := DFunLike.congr_fun
    (structureCohomologyPullback_comp (fst X Y).left V.ι n) x
  have hPull := hFirstOpen.trans hComp.symm
  have hAction := congrArg₂
    (fun (a : Γ(V.toScheme, ⊤))
      (b : Sheaf.H.{u + 1}
        (moduleAddSheaf V.toScheme (SheafOfModules.unit V.toScheme.ringCatSheaf)) n) =>
      Sheaf.H.map (moduleScalarOfGlobal V.toScheme
        (SheafOfModules.unit V.toScheme.ringCatSheaf) a) n b) hS hPull
  exact hLocal.trans hAction

/-- The actual product-open square over the affine open's original global-section ring. -/
theorem structureOpenProduct_isoSpec_isPullback (X Y : FScheme k) (U : Y.left.Opens)
    (hU : IsAffineOpen U) :
    letI : IsAffine U.toScheme := hU
    IsPullback (((snd X Y).left ⁻¹ᵁ U).ι ≫ (fst X Y).left)
      (((snd X Y).left ∣_ U) ≫ U.toScheme.isoSpec.hom) X.hom
      (Spec.map (CommRingCat.ofHom (U.ι.appTop.hom.comp (constants Y)))) := by
  let : IsAffine U.toScheme := hU
  let YU : FScheme k := Over.mk (U.ι ≫ Y.hom)
  let j : YU ⟶ Y := Over.homMk U.ι rfl
  have hs : constants YU = U.ι.appTop.hom.comp (constants Y) := by
    ext a
    exact (map_constants j a).symm
  have h := ((isPullback_morphismRestrict (snd X Y).left U).flip).paste_horiz
    (IsPullback.of_hasPullback X.hom Y.hom)
  apply h.of_iso (Iso.refl _) (Iso.refl _) U.toScheme.isoSpec (Iso.refl _)
  · simp
  · simp
  · simp
  · have hf := structureMorphism_toSpec_constants YU
    rw [hs] at hf
    simp only [YU, Over.mk_left, Over.mk_hom] at hf
    simpa only [Iso.refl_hom, Category.comp_id, Scheme.isoSpec_hom] using hf

/-- The native scalar-extension map on the actual original product-open scheme. -/
def structureOpenAffineTensorMap (X Y : FScheme k) (U : Y.left.Opens)
    (hU : IsAffineOpen U) (n : ℕ) :
    letI : IsAffine U.toScheme := hU
    let S : Type u := Γ(U.toScheme, ⊤)
    let V := (snd X Y).left ⁻¹ᵁ U
    let β := (((snd X Y).left ∣_ U) ≫ U.toScheme.isoSpec.hom).appTop.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
    letI := moduleCohomologyModuleOfHom V.toScheme β
      (SheafOfModules.unit V.toScheme.ringCatSheaf) n
    (ModuleCat.extendScalars (U.ι.appTop.hom.comp (constants Y))).obj
        (ModuleCat.of k (structureCohomology k X n)) ⟶
      ModuleCat.of S
        (Sheaf.H.{u + 1} (moduleAddSheaf V.toScheme
          (SheafOfModules.unit V.toScheme.ringCatSheaf)) n) := by
  letI : IsAffine U.toScheme := hU
  let S : Type u := Γ(U.toScheme, ⊤)
  let V := (snd X Y).left ⁻¹ᵁ U
  let p := V.ι ≫ (fst X Y).left
  let q := ((snd X Y).left ∣_ U) ≫ U.toScheme.isoSpec.hom
  let σ := U.ι.appTop.hom.comp (constants Y)
  let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
  exact unitCohomologyTensorMap p σ (constants X) β
    (moduleSectionsBaseChangeScalars p q X.hom σ
      (structureOpenProduct_isoSpec_isPullback X Y U hU).w) n

/-- Every pure tensor has the actual local section coefficient on the original pullback. -/
theorem structureOpenAffineTensorMap_tmul (X Y : FScheme k) (U : Y.left.Opens)
    (hU : IsAffineOpen U) (n : ℕ) (s : Γ(U.toScheme, ⊤))
    (x : structureCohomology k X n) :
    structureOpenAffineTensorMap X Y U hU n
        (s ⊗ₜ[k,U.ι.appTop.hom.comp (constants Y)] x) =
      Sheaf.H.map
        (moduleScalarOfGlobal ((snd X Y).left ⁻¹ᵁ U).toScheme
          (SheafOfModules.unit ((snd X Y).left ⁻¹ᵁ U).toScheme.ringCatSheaf)
          (((snd X Y).left ∣_ U).appTop s)) n
        (structureCohomologyPullback
          (((snd X Y).left ⁻¹ᵁ U).ι ≫ (fst X Y).left) n x) := by
  let : IsAffine U.toScheme := hU
  let S : Type u := Γ(U.toScheme, ⊤)
  let V := (snd X Y).left ⁻¹ᵁ U
  let p := V.ι ≫ (fst X Y).left
  let q := ((snd X Y).left ∣_ U) ≫ U.toScheme.isoSpec.hom
  let σ := U.ι.appTop.hom.comp (constants Y)
  let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
  have h := unitCohomologyTensorMap_tmul p σ (constants X) β
    (moduleSectionsBaseChangeScalars p q X.hom σ
      (structureOpenProduct_isoSpec_isPullback X Y U hU).w) n s x
  have hs := congrArg (fun t : Γ(U.toScheme, ⊤) →+* Γ(V.toScheme, ⊤) => t s)
    (isoSpec_comp_scalar ((snd X Y).left ∣_ U))
  have hFinal := h.trans (congrArg
    (fun a : Γ(V.toScheme, ⊤) => Sheaf.H.map
      (moduleScalarOfGlobal V.toScheme (SheafOfModules.unit V.toScheme.ringCatSheaf) a) n
      (structureCohomologyPullback p n x)) hs)
  exact hFinal

/-- The whole original mixed tensor is the actual scalar-extension map
after canonical normalization. -/
theorem structureOpenAffineTensorMap_sourceEquiv (X Y : FScheme k) (U : Y.left.Opens)
    (hU : IsAffineOpen U) (n : ℕ) :
    (fun z : structureCohomology k X n ⊗[k] structureOpenCohomology Y U 0 =>
      structureOpenAffineTensorMap X Y U hU n (structureOpenAffineSourceEquiv X Y U n z)) =
      fun z => moduleOpenUnitNormalize (X ⊗ Y).left ((snd X Y).left ⁻¹ᵁ U) n
        (structureExternalOpenTensor X Y U (Nat.add_zero n) z) := by
  let : IsAffine U.toScheme := hU
  let S : Type u := Γ(U.toScheme, ⊤)
  let σ := U.ι.appTop.hom.comp (constants Y)
  let : Module k S := σ.toModule
  let V := (snd X Y).left ⁻¹ᵁ U
  let β := (((snd X Y).left ∣_ U) ≫ U.toScheme.isoSpec.hom).appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
  let := moduleCohomologyModuleOfHom V.toScheme β
    (SheafOfModules.unit V.toScheme.ringCatSheaf) n
  let E := structureOpenAffineTensorMap X Y U hU n
  let T := moduleOpenUnitNormalize (X ⊗ Y).left V n
  let κ := structureExternalOpenTensor X Y U (Nat.add_zero n)
  funext z
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    have hφ := structureOpenAffineSourceEquiv_tmul X Y U n x y
    have he := structureOpenAffineTensorMap_tmul X Y U hU n (structureOpenH0Equiv Y U y) x
    have hκ := structureExternalOpenTensor_zero_right X Y U n x y
    exact ((congrArg E hφ).trans he).trans hκ.symm
  | add a b ha hb =>
    have hφ := (structureOpenAffineSourceEquiv X Y U n).map_add a b
    have he := E.hom.map_add
      (structureOpenAffineSourceEquiv X Y U n a) (structureOpenAffineSourceEquiv X Y U n b)
    have hκ := κ.map_add a b
    have hT := T.map_add (κ a) (κ b)
    have hLeft := (congrArg E hφ).trans he
    have hRight := (congrArg T hκ).trans hT
    exact (hLeft.trans (congrArg₂ (· + ·) ha hb)).trans hRight.symm

variable (X Y : FScheme k) [QuasiCompact X.hom] [QuasiSeparated X.hom]

/-- Flat base change over the field makes the same original product-open tensor map invertible. -/
theorem structureOpenAffineTensorMap_isIso (U : Y.left.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    IsIso (structureOpenAffineTensorMap X Y U hU n) := by
  let : IsAffine U.toScheme := hU
  let σ := U.ι.appTop.hom.comp (constants Y)
  have hflat : σ.Flat := by
    let := σ.toAlgebra
    change Module.Flat k Γ(U.toScheme, ⊤)
    infer_instance
  exact unitCohomologyTensorMap_isIso_of_isPullback
    (((snd X Y).left ⁻¹ᵁ U).ι ≫ (fst X Y).left)
    (((snd X Y).left ∣_ U) ≫ U.toScheme.isoSpec.hom) X.hom σ
    (structureOpenProduct_isoSpec_isPullback X Y U hU) hflat n

/-- The original mixed degree-(n,0) tensor map is bijective for every affine open. -/
theorem structureExternalOpenTensor_bijective_of_isAffineOpen
    (U : Y.left.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    Function.Bijective (structureExternalOpenTensor X Y U (Nat.add_zero n)) := by
  let := structureOpenAffineTensorMap_isIso X Y U hU n
  have hE := ConcreteCategory.bijective_of_isIso (structureOpenAffineTensorMap X Y U hU n)
  have hφ := (structureOpenAffineSourceEquiv X Y U n).bijective
  have h := structureOpenAffineTensorMap_sourceEquiv X Y U hU n
  have hComposite := Eq.mp (congrArg Function.Bijective h) (hE.comp hφ)
  exact (Function.Bijective.of_comp_iff'
    (moduleOpenUnitNormalize (X ⊗ Y).left ((snd X Y).left ⁻¹ᵁ U) n).bijective
    (structureExternalOpenTensor X Y U (Nat.add_zero n))).mp hComposite

private theorem directSum_lof_bijective_of_subsingleton
    {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (i₀ : ι) (hM : ∀ i, i ≠ i₀ → Subsingleton (M i)) :
    Function.Bijective (DirectSum.lof R ι M i₀) := by
  refine ⟨DirectSum.of_injective i₀, ?_⟩
  intro z
  induction z using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | of i x =>
    by_cases hi : i = i₀
    · subst i
      exact ⟨x, rfl⟩
    · let := hM i hi
      refine ⟨0, ?_⟩
      rw [map_zero, Subsingleton.elim x 0, map_zero]
  | add a b ha hb =>
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x + y, map_add _ _ _⟩

omit [QuasiCompact X.hom] [QuasiSeparated X.hom] in
/-- Affine-open acyclicity leaves exactly the original (n,0) antidiagonal coordinate. -/
theorem structureOpenKunnethSum_lof_bijective_of_isAffineOpen
    (U : Y.left.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    Function.Bijective (DirectSum.lof k _
      (fun s : HomologicalComplex₂.TotalDegree n =>
        structureCohomology k X s.val.1 ⊗[k] structureOpenCohomology Y U s.val.2)
      (⟨(n, 0), Nat.add_zero n⟩ : HomologicalComplex₂.TotalDegree n)) := by
  classical
  apply directSum_lof_bijective_of_subsingleton
  intro s hs
  have hq : s.val.2 ≠ 0 := by
    intro hq
    apply hs
    apply Subtype.ext
    apply Prod.ext
    · have h := s.property
      change s.val.1 + s.val.2 = n at h
      change s.val.1 = n
      omega
    · exact hq
  obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero hq
  have : Subsingleton (structureOpenCohomology Y U s.val.2) := by
    rw [hq]
    let := Scheme.Modules.isQuasicoherent_unit Y.left
    exact subsingleton_sheafHPrime_of_isAffineOpen
      (SheafOfModules.unit Y.left.ringCatSheaf) U hU q
  infer_instance

/-- The original mixed-open Künneth map is bijective for an affine open in the fixed ambient. -/
theorem structureOpenKunnethMap_bijective_of_isAffineOpen
    (U : Y.left.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    Function.Bijective (structureOpenKunnethMap X Y U n) := by
  let ι := DirectSum.lof k _
    (fun s : HomologicalComplex₂.TotalDegree n =>
      structureCohomology k X s.val.1 ⊗[k] structureOpenCohomology Y U s.val.2)
    (⟨(n, 0), Nat.add_zero n⟩ : HomologicalComplex₂.TotalDegree n)
  have hι := structureOpenKunnethSum_lof_bijective_of_isAffineOpen X Y U hU n
  have hComp : (structureOpenKunnethMap X Y U n).comp ι =
      structureExternalOpenTensor X Y U (Nat.add_zero n) := by
    apply LinearMap.ext
    intro z
    exact structureOpenKunnethMap_lof X Y U n ⟨(n, 0), Nat.add_zero n⟩ z
  apply (Function.Bijective.of_comp_iff (structureOpenKunnethMap X Y U n) hι).mp
  change Function.Bijective ((structureOpenKunnethMap X Y U n).comp ι)
  rw [hComp]
  exact structureExternalOpenTensor_bijective_of_isAffineOpen X Y U hU n

end AlgebraicGeometry.Scheme.Cohomology
