/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Coefficients
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.DegreeZero
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology
public import Aglib.Algebra.Homology.ShortComplex.Adjunction.Counit
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeExact

/-!
# Actual affine higher-image sections and unchanged cohomology

The actual higher direct image over a spectrum has the original cohomology
module as its sections, with the specified structural action. The comparison
uses the original counit computation, original tilde unit and actual section
complex of the supplied native module injective resolution. The installed
bounded-below derived functor at the original single has the same canonical
comparison through the native higher-derived/homology isomorphism.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
  (M : X.Modules) [M.IsQuasicoherent]

/-- Actual affine sections of the original higher direct image are unchanged original
cohomology, with its actual structural ring action and original resolution classes. -/
def moduleHigherDirectImageAffineSectionsLinearEquiv (I : InjectiveResolution M) (n : ℕ) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M n
    moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward f).rightDerived n).obj M) ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X M) n := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  letI := moduleCohomologyModuleOfHom X α M n
  let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let C := (moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K
  let e₀ := moduleSpecΓFunctor.mapIso (moduleHigherDirectImageAffineIso f M I n)
  let e₁ := (tilde.toTildeΓNatIso (R := CommRingCat.of R)).app (C.homology (n : ℤ))
  let e₂ := (homologyFunctor (ModuleCat.{u} R) (.up ℤ) (n : ℤ)).mapIso
    (moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ) I.cochainComplex)
  exact e₀.toLinearEquiv.trans (e₁.symm.toLinearEquiv.trans
    (e₂.toLinearEquiv.trans (moduleResolutionSectionsCohomologyLinearEquiv X α I n)))

/-- Every original factor and the original section-resolution class remain in the forward map. -/
theorem moduleHigherDirectImageAffineSectionsLinearEquiv_apply
    (I : InjectiveResolution M) (n : ℕ)
    (x : moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward f).rightDerived n).obj M)) :
    moduleHigherDirectImageAffineSectionsLinearEquiv f M I n x =
      moduleResolutionSectionsCohomologyLinearEquiv X
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) I n
        (homologyMap (moduleSpecPushforwardGlobalSectionsComplexIso
          f (.up ℤ) I.cochainComplex).hom (n : ℤ)
          ((tilde.toTildeΓNatIso (R := CommRingCat.of R)).inv.app
            (((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj
              (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj
                I.cochainComplex)).homology (n : ℤ))
            (moduleSpecΓFunctor.map (moduleHigherDirectImageAffineIso f M I n).hom x))) := rfl

/-- Use the installed standard derived categories of the actual module sheaves. -/
local instance affineHigherImageCohomologyStandard (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

/-- Original affine sections of homology of the installed derived direct image at the actual
single are the unchanged original cohomology module. -/
def moduleDerivedPushforwardSingleAffineSectionsLinearEquiv
    (I : InjectiveResolution M) (n : ℕ) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M n
    moduleSpecΓFunctor.obj
      ((DerivedCategory.Plus.homologyFunctor (Spec (CommRingCat.of R)).Modules (n : ℤ)).obj
        ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M))) ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X M) n :=
  (moduleSpecΓFunctor.mapIso
      (((Scheme.Modules.pushforward f).rightDerivedSingleHomologyIso n).app M).symm).toLinearEquiv
    |>.trans (moduleHigherDirectImageAffineSectionsLinearEquiv f M I n)

/-- The native derived-single homology sheaves over an affine target are quasicoherent. -/
theorem moduleDerivedPushforwardSingleAffineHomology_isQuasicoherent (n : ℕ) :
    ((DerivedCategory.Plus.homologyFunctor (Spec (CommRingCat.of R)).Modules (n : ℤ)).obj
      ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M))).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of R)).ringCatSheaf).prop_of_iso
    (((Scheme.Modules.pushforward f).rightDerivedSingleHomologyIso n).app M)
    (moduleHigherDirectImageAffine_isQuasicoherent f M n)

/-- The unchanged first two affine cohomology factors, from actual higher-image sections
to homology of the original section complex of the supplied resolution. -/
def moduleHigherDirectImageAffineSectionsHomologyMap (I : InjectiveResolution M) (n : ℕ) :
    moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward f).rightDerived n).obj M) ⟶
      ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj
        (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj
          I.cochainComplex)).homology (n : ℤ) :=
  moduleSpecΓFunctor.map (moduleHigherDirectImageAffineIso f M I n).hom ≫
    (tilde.toTildeΓNatIso (R := CommRingCat.of R)).inv.app
      (((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj
        (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj
          I.cochainComplex)).homology (n : ℤ))


/-- The original affine section/homology factor is invertible. -/
theorem moduleHigherDirectImageAffineSectionsHomologyMap_isIso
    (I : InjectiveResolution M) (n : ℕ) :
    IsIso (moduleHigherDirectImageAffineSectionsHomologyMap f M I n) := by
  dsimp only [moduleHigherDirectImageAffineSectionsHomologyMap]
  infer_instance

/-- The unchanged affine factor retains the native homology counit mate and the original
integer-resolution comparison. Global sections need not preserve homology. -/
theorem moduleHigherDirectImageAffineSectionsHomologyMap_counit
    (I : InjectiveResolution M) (n : ℕ) :
    let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let : (tilde.functor (CommRingCat.of R)).Additive := by
      let : PreservesFiniteLimits (tilde.functor (CommRingCat.of R)) :=
        Scheme.Modules.tilde_preservesFiniteLimits (CommRingCat.of R)
      exact CategoryTheory.Functor.additive_of_preserves_binary_products _
    let : (tilde.functor (CommRingCat.of R)).PreservesHomology :=
      Scheme.Modules.tilde_preservesHomology (CommRingCat.of R)
    let : (moduleSpecΓFunctor (R := CommRingCat.of R)).Additive :=
      Scheme.Modules.moduleSpecΓFunctor_additive (CommRingCat.of R)
    moduleHigherDirectImageAffineSectionsHomologyMap f M I n ≫
        (tilde.adjunction (R := CommRingCat.of R)).homologyCounitMate (K.sc (n : ℤ)) =
      moduleSpecΓFunctor.map
        (I.isoRightDerivedObjCochain (Scheme.Modules.pushforward f) n).hom := by
  let : PreservesFiniteLimits (tilde.functor (CommRingCat.of R)) :=
    Scheme.Modules.tilde_preservesFiniteLimits (CommRingCat.of R)
  let : (tilde.functor (CommRingCat.of R)).Additive :=
    CategoryTheory.Functor.additive_of_preserves_binary_products _
  let : (tilde.functor (CommRingCat.of R)).PreservesHomology :=
    Scheme.Modules.tilde_preservesHomology (CommRingCat.of R)
  let : (moduleSpecΓFunctor (R := CommRingCat.of R)).Additive :=
    Scheme.Modules.moduleSpecΓFunctor_additive (CommRingCat.of R)
  let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let C := (moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K
  let : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
      (CommRingCat.of R) (.up ℤ) K) := moduleResolutionPushforwardTildeCounit_quasiIso f M I
  change moduleSpecΓFunctor.map (moduleHigherDirectImageAffineIso f M I n).hom ≫
      (tilde.toTildeΓNatIso (R := CommRingCat.of R)).inv.app (C.homology (n : ℤ)) ≫
      (tilde.toTildeΓNatIso (R := CommRingCat.of R)).hom.app (C.homology (n : ℤ)) ≫
      moduleSpecΓFunctor.map
        (Scheme.Modules.Complex.tildeGlobalSectionsHomologyIso
          (CommRingCat.of R) (.up ℤ) K (n : ℤ)).hom = _
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp]
  exact congrArg moduleSpecΓFunctor.map
    (moduleHigherDirectImageAffineIso_hom_comp f M I n)

private theorem affineSectionsHomologyMap_toRightDerivedZero (I : InjectiveResolution M) :
    let F : X.Modules ⥤ (Spec (CommRingCat.of R)).Modules := Scheme.Modules.pushforward f
    let G : (Spec (CommRingCat.of R)).Modules ⥤ ModuleCat.{u} R := moduleSpecΓFunctor
    let : G.Additive := Scheme.Modules.moduleSpecΓFunctor_additive (CommRingCat.of R)
    let K : CochainComplex (Spec (CommRingCat.of R)).Modules ℤ :=
      (F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let C : CochainComplex (ModuleCat.{u} R) ℤ := (G.mapHomologicalComplex (.up ℤ)).obj K
    let e : C ≅ ((F ⋙ G).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex :=
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).app I.cochainComplex
    G.map (F.toRightDerivedZero.app M) ≫
        moduleHigherDirectImageAffineSectionsHomologyMap f M I 0 =
      I.toRightDerivedZeroCochainCycles (F ⋙ G) ≫ cyclesMap e.inv 0 ≫ C.homologyπ 0 := by
  let F : X.Modules ⥤ (Spec (CommRingCat.of R)).Modules := Scheme.Modules.pushforward f
  let G : (Spec (CommRingCat.of R)).Modules ⥤ ModuleCat.{u} R := moduleSpecΓFunctor
  let : G.Additive := Scheme.Modules.moduleSpecΓFunctor_additive (CommRingCat.of R)
  let K : CochainComplex (Spec (CommRingCat.of R)).Modules ℤ :=
    (F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let C : CochainComplex (ModuleCat.{u} R) ℤ := (G.mapHomologicalComplex (.up ℤ)).obj K
  let e : C ≅ ((F ⋙ G).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex :=
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).app I.cochainComplex
  let T : ModuleCat.{u} R ⥤ (Spec (CommRingCat.of R)).Modules :=
    tilde.functor (CommRingCat.of R)
  let : PreservesFiniteLimits T := Scheme.Modules.tilde_preservesFiniteLimits (CommRingCat.of R)
  let : T.Additive := CategoryTheory.Functor.additive_of_preserves_binary_products T
  let : T.PreservesHomology := Scheme.Modules.tilde_preservesHomology (CommRingCat.of R)
  let adj : T ⊣ G := tilde.adjunction (R := CommRingCat.of R)
  let A := moduleHigherDirectImageAffineSectionsHomologyMap f M I 0
  let m : C.homology 0 ⟶ G.obj (K.homology 0) := adj.homologyCounitMate (K.sc 0)
  let zS := I.toRightDerivedZeroCochainCycles F
  let zC := I.toRightDerivedZeroCochainCycles (F ⋙ G) ≫ cyclesMap e.inv 0
  let : G.IsRightAdjoint := adj.isRightAdjoint
  have hA : A ≫ m = G.map (I.isoRightDerivedObjCochain F 0).hom :=
    moduleHigherDirectImageAffineSectionsHomologyMap_counit f M I 0
  let : IsIso A := moduleHigherDirectImageAffineSectionsHomologyMap_isIso f M I 0
  let : IsIso (A ≫ m) := by rw [hA]; infer_instance
  let : IsIso m := IsIso.of_isIso_comp_left A m
  have hzC : zC ≫ C.iCycles 0 =
      (F ⋙ G).map (I.ι.f 0) ≫ (F ⋙ G).map (I.cochainComplexXIso 0 0 rfl).inv := by
    change (I.toRightDerivedZeroCochainCycles (F ⋙ G) ≫ cyclesMap e.inv 0) ≫ C.iCycles 0 = _
    rw [Category.assoc, cyclesMap_i]
    rw [← Category.assoc, InjectiveResolution.toRightDerivedZeroCochainCycles_comp_iCycles]
    have he : e.inv.f 0 = 𝟙 _ := rfl
    rw [he, Category.comp_id]
  have hcycle_i : zC ≫ C.iCycles 0 = G.map zS ≫ G.map (K.iCycles 0) := by
    calc
      _ = G.map (F.map (I.ι.f 0) ≫ F.map (I.cochainComplexXIso 0 0 rfl).inv) := by
        simpa only [Functor.comp_map, Functor.map_comp] using hzC
      _ = G.map (zS ≫ K.iCycles 0) := by
        exact congrArg G.map (I.toRightDerivedZeroCochainCycles_comp_iCycles F).symm
      _ = _ := G.map_comp _ _
  have hcycle : zC ≫ adj.cyclesCounitMate (K.sc 0) = G.map zS := by
    apply (cancel_mono (G.map (K.iCycles 0))).mp
    rw [Category.assoc]
    erw [adj.cyclesCounitMate_iCycles]
    exact hcycle_i
  have hπ := adj.homologyCounitMate_homologyπ (K.sc 0)
  change C.homologyπ 0 ≫ m = adj.cyclesCounitMate (K.sc 0) ≫ G.map (K.homologyπ 0) at hπ
  change G.map (F.toRightDerivedZero.app M) ≫ A = zC ≫ C.homologyπ 0
  apply (cancel_mono m).mp
  simp only [Category.assoc]
  calc
    _ = G.map (F.toRightDerivedZero.app M) ≫ G.map (I.isoRightDerivedObjCochain F 0).hom := by
      rw [hA]
    _ = G.map zS ≫ G.map (K.homologyπ 0) := by
      simpa only [Functor.map_comp] using
        congrArg G.map (I.toRightDerivedZero_comp_isoRightDerivedObjCochain F)
    _ = _ := by rw [hπ, ← Category.assoc, hcycle]


open CategoryTheory.Abelian CochainComplex HomComplex

section ExtZero
universe v w t
variable {C : Type v} [Category.{w} C] [Abelian C] [HasExt.{t} C]

omit [HasExt C] in
private theorem cocycle_equivHomShift_ofHom {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    Cocycle.equivHomShift.symm (Cocycle.ofHom φ) = ShiftedHom.mk₀ (0 : ℤ) rfl φ := by
  ext i
  simp [Cocycle.equivHomShift_symm_apply, Cocycle.homOf, Cocycle.ofHom,
    Cochain.rightShift_v, Cochain.ofHom, ShiftedHom.mk₀,
    CategoryTheory.shiftFunctorZero', CochainComplex.shiftFunctorZero_inv_app_f,
    HomologicalComplex.XIsoOfEq]

private theorem extMk_iota_zero {U M : C} (I : InjectiveResolution M) (g : U ⟶ M) :
    I.extMk (g ≫ I.ι.f 0) 1 rfl (by
      rw [Category.assoc, I.ι.comm 0 1]
      simp) = Ext.mk₀ g := by
  let := HasDerivedCategory.standard C
  have h0 : (g ≫ I.ι.f 0) ≫ I.cocomplex.d 0 1 = 0 := by
    rw [Category.assoc, I.ι.comm 0 1]
    simp
  have hc :
      Cocycle.fromSingleMk ((g ≫ I.ι.f 0) ≫ (I.cochainComplexXIso 0 0 rfl).inv)
          (zero_add (0 : ℤ)) 1 rfl (by
            rw [I.cochainComplex_d 0 1 0 1 rfl rfl]
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
            simpa only [Category.assoc, zero_comp] using
              congrArg (fun k => k ≫ (I.cochainComplexXIso 1 1 rfl).inv) h0) =
        Cocycle.ofHom ((CochainComplex.singleFunctor C 0).map g ≫ I.ι') := by
    apply Cocycle.ext
    apply (Cochain.fromSingleEquiv (zero_add (0 : ℤ))).injective
    simp only [Cocycle.fromSingleMk_coe, Cochain.fromSingleEquiv_fromSingleMk]
    dsimp only [Cocycle.ofHom, Cocycle.mk, Cochain.fromSingleEquiv]
    change _ = (HomologicalComplex.singleObjXSelf (.up ℤ) 0 U).inv ≫
      (Cochain.ofHom ((CochainComplex.singleFunctor C 0).map g ≫ I.ι')).v 0 0 (add_zero 0)
    rw [Cochain.ofHom_v]
    rw [HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self,
      InjectiveResolution.ι'_f_zero]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  ext
  rw [InjectiveResolution.extMk_hom]
  erw [hc]
  erw [cocycle_equivHomShift_ofHom, ShiftedHom.map_mk₀,
    ShiftedHom.mk₀_comp_mk₀, ShiftedHom.mk₀_comp_mk₀, Ext.mk₀_hom]
  congr 1
  have hn := (DerivedCategory.singleFunctorIsoCompQ C 0).hom.naturality g
  simp only [Functor.comp_map] at hn
  rw [Functor.map_comp]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, ← hn]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]


end ExtZero

private theorem resolutionSectionClass_zero
    {A : Type u} [CommRing A] (Z : Scheme.{u}) (α : A →+* Γ(Z, ⊤))
    (P : Z.Modules) (J : InjectiveResolution P)
    (s : moduleResolutionSectionCycles Z α J 0) (x : Γ(P, ⊤))
    (hs : s.val = Scheme.Modules.Hom.app
      (J.ι.f 0 ≫ (J.cochainComplexXIso 0 0 rfl).inv) ⊤ x) :
    letI := moduleCohomologyModuleOfHom Z α P 0
    moduleH0EquivOfHom Z α P (moduleResolutionSectionClass Z α J 0 s) = x := by
  let g := (Scheme.Modules.unitHomGlobalSectionsAddEquiv Z P).symm x
  have hrep : moduleResolutionSectionHom Z α J 0 s = g ≫ J.ι.f 0 := by
    change (Scheme.Modules.unitHomGlobalSectionsAddEquiv Z (J.cochainComplex.X 0)).symm
        s.val ≫ (J.cochainComplexXIso 0 0 rfl).hom = g ≫ J.ι.f 0
    apply (cancel_mono (J.cochainComplexXIso 0 0 rfl).inv).mp
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply (Scheme.Modules.unitHomGlobalSectionsAddEquiv Z _).injective
    rw [AddEquiv.apply_symm_apply]
    change s.val = Scheme.Modules.unitHomGlobalSectionsEquiv Z _ (g ≫ _ ≫ _)
    rw [Scheme.Modules.unitHomGlobalSectionsEquiv_naturality]
    change s.val = Scheme.Modules.Hom.app
      (J.ι.f 0 ≫ (J.cochainComplexXIso 0 0 rfl).inv) ⊤
        ((Scheme.Modules.unitHomGlobalSectionsAddEquiv Z P) g)
    rw [AddEquiv.apply_symm_apply]
    exact hs
  have hext : moduleResolutionSectionExtClass Z α J 0 s = Ext.mk₀ g := by
    rw [moduleResolutionSectionExtClass_eq_extMk]
    simpa only [hrep] using extMk_iota_zero J g
  change Sheaf.H.equiv₀ (moduleAddSheaf Z P) isTerminalTop
    (moduleExtCohomologyMap Z P 0 (moduleResolutionSectionExtClass Z α J 0 s)) = x
  rw [hext, moduleExtCohomologyMap_mk₀_sections]
  change (Scheme.Modules.unitHomGlobalSectionsAddEquiv Z P)
    ((Scheme.Modules.unitHomGlobalSectionsAddEquiv Z P).symm x) = x
  exact AddEquiv.apply_symm_apply _ _

/-- In degree zero, the original higher-image section comparison recovers the original
pushforward global section through the native right-derived-zero map. -/
theorem moduleHigherDirectImageAffineSectionsLinearEquiv_toRightDerivedZero
    (I : InjectiveResolution M)
    (x : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward f).obj M)) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M 0
    moduleH0EquivOfHom X α M
        (moduleHigherDirectImageAffineSectionsLinearEquiv f M I 0
          (moduleSpecΓFunctor.map ((Scheme.Modules.pushforward f).toRightDerivedZero.app M) x)) =
      (moduleSpecPushforwardGlobalSectionsIso f).hom.app M x := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let := moduleCohomologyModuleOfHom X α M 0
  let F : X.Modules ⥤ (Spec (CommRingCat.of R)).Modules := Scheme.Modules.pushforward f
  let G : (Spec (CommRingCat.of R)).Modules ⥤ ModuleCat.{u} R := moduleSpecΓFunctor
  let : G.Additive := Scheme.Modules.moduleSpecΓFunctor_additive (CommRingCat.of R)
  let K : CochainComplex (Spec (CommRingCat.of R)).Modules ℤ :=
    (F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let C : CochainComplex (ModuleCat.{u} R) ℤ := (G.mapHomologicalComplex (.up ℤ)).obj K
  let e : C ≅ ((F ⋙ G).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex :=
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).app I.cochainComplex
  let z := I.toRightDerivedZeroCochainCycles (F ⋙ G) ≫ cyclesMap e.inv 0
  let cf := moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ) I.cochainComplex
  let s : moduleResolutionSectionCycles X α I 0 :=
    (moduleResolutionSectionCyclesIso X α I 0).hom (cyclesMap cf.hom 0 (z x))
  have hE : moduleHigherDirectImageAffineSectionsLinearEquiv f M I 0
        (G.map (F.toRightDerivedZero.app M) x) = moduleResolutionSectionClass X α I 0 s := by
    have hz := ConcreteCategory.congr_hom (affineSectionsHomologyMap_toRightDerivedZero f M I) x
    change moduleHigherDirectImageAffineSectionsHomologyMap f M I 0
        (G.map (F.toRightDerivedZero.app M) x) = C.homologyπ 0 (z x) at hz
    change moduleResolutionSectionsCohomologyLinearEquiv X α I 0
        (homologyMap cf.hom 0
          (moduleHigherDirectImageAffineSectionsHomologyMap f M I 0
            (G.map (F.toRightDerivedZero.app M) x))) = _
    rw [hz]
    have hπ := ConcreteCategory.congr_hom (homologyπ_naturality cf.hom (0 : ℤ)) (z x)
    change homologyMap cf.hom 0 (C.homologyπ 0 (z x)) =
      (moduleResolutionSectionComplex X α I).homologyπ 0 (cyclesMap cf.hom 0 (z x)) at hπ
    rw [hπ]
    exact moduleResolutionSectionsCohomologyLinearEquiv_homologyπ X α I 0 _
  have hz : z ≫ C.iCycles 0 =
      (F ⋙ G).map (I.ι.f 0) ≫ (F ⋙ G).map (I.cochainComplexXIso 0 0 rfl).inv := by
    change (I.toRightDerivedZeroCochainCycles (F ⋙ G) ≫ cyclesMap e.inv 0) ≫ C.iCycles 0 = _
    rw [Category.assoc, cyclesMap_i]
    rw [← Category.assoc, InjectiveResolution.toRightDerivedZeroCochainCycles_comp_iCycles]
    have he : e.inv.f 0 = 𝟙 _ := rfl
    rw [he, Category.comp_id]
  have hs : s.val = Scheme.Modules.Hom.app
      (I.ι.f 0 ≫ (I.cochainComplexXIso 0 0 rfl).inv) ⊤
        ((moduleSpecPushforwardGlobalSectionsIso f).hom.app M x) := by
    change ((moduleResolutionSectionCyclesIso X α I 0).hom
      (cyclesMap cf.hom 0 (z x))).val = _
    rw [moduleResolutionSectionCyclesIso_hom_val]
    have hi := ConcreteCategory.congr_hom (cyclesMap_i cf.hom (0 : ℤ)) (z x)
    change (moduleResolutionSectionComplex X α I).iCycles 0 (cyclesMap cf.hom 0 (z x)) =
      cf.hom.f 0 (C.iCycles 0 (z x)) at hi
    erw [hi]
    change C.iCycles 0 (z x) = _
    exact (ConcreteCategory.congr_hom hz x).trans rfl
  change moduleH0EquivOfHom X α M
      (moduleHigherDirectImageAffineSectionsLinearEquiv f M I 0
        (G.map (F.toRightDerivedZero.app M) x)) = _
  rw [hE]
  exact resolutionSectionClass_zero X α M I s _ hs


end AlgebraicGeometry.Scheme.Cohomology
