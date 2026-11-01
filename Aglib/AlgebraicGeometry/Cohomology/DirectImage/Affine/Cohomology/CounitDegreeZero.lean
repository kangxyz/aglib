/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology.SectionsCounitHomology

/-! # Original right-derived-zero section normalization from the actual counit

The original cycle, homology and section-class proofs live here once. Geometry
supplies the actual resolution counit quasi-isomorphism; no new model is chosen.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open AlgebraicGeometry TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules)

private theorem affineSectionsHomologyMap_toRightDerivedZero (I : InjectiveResolution M)
    (hI : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
      (CommRingCat.of R) (.up ℤ)
      (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex))) :
    let F : X.Modules ⥤ (Spec (CommRingCat.of R)).Modules := Scheme.Modules.pushforward f
    let G : (Spec (CommRingCat.of R)).Modules ⥤ ModuleCat.{u} R := moduleSpecΓFunctor
    let : G.Additive := Scheme.Modules.moduleSpecΓFunctor_additive (CommRingCat.of R)
    let K : CochainComplex (Spec (CommRingCat.of R)).Modules ℤ :=
      (F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let C : CochainComplex (ModuleCat.{u} R) ℤ := (G.mapHomologicalComplex (.up ℤ)).obj K
    let e : C ≅ ((F ⋙ G).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex :=
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).app I.cochainComplex
    G.map (F.toRightDerivedZero.app M) ≫
        moduleHigherDirectImageAffineSectionsHomologyMap_of_counit_quasiIso f M I hI 0 =
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
  let A := moduleHigherDirectImageAffineSectionsHomologyMap_of_counit_quasiIso f M I hI 0
  let m : C.homology 0 ⟶ G.obj (K.homology 0) := adj.homologyCounitMate (K.sc 0)
  let zS := I.toRightDerivedZeroCochainCycles F
  let zC := I.toRightDerivedZeroCochainCycles (F ⋙ G) ≫ cyclesMap e.inv 0
  let : G.IsRightAdjoint := adj.isRightAdjoint
  have hA : A ≫ m = G.map (I.isoRightDerivedObjCochain F 0).hom :=
    moduleHigherDirectImageAffineSectionsHomologyMap_counit_of_counit_quasiIso f M I hI 0
  let : IsIso A :=
    moduleHigherDirectImageAffineSectionsHomologyMap_isIso_of_counit_quasiIso f M I hI 0
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
    simpa only [hrep] using InjectiveResolution.extMk_ι_zero J g
  change Sheaf.H.equiv₀ (moduleAddSheaf Z P) isTerminalTop
    (moduleExtCohomologyMap Z P 0 (moduleResolutionSectionExtClass Z α J 0 s)) = x
  rw [hext, moduleExtCohomologyMap_mk₀_sections]
  change (Scheme.Modules.unitHomGlobalSectionsAddEquiv Z P)
    ((Scheme.Modules.unitHomGlobalSectionsAddEquiv Z P).symm x) = x
  exact AddEquiv.apply_symm_apply _ _

/-- In degree zero, the original higher-image section comparison recovers the original
pushforward global section through the native right-derived-zero map. -/
theorem moduleHigherDirectImageAffineSectionsLinearEquiv_toRightDerivedZero_of_counit_quasiIso
    (I : InjectiveResolution M)
    (hI : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
      (CommRingCat.of R) (.up ℤ)
      (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)))
    (x : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward f).obj M)) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M 0
    moduleH0EquivOfHom X α M
        (moduleHigherDirectImageAffineSectionsLinearEquiv_of_counit_quasiIso f M I hI 0
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
  have hE : moduleHigherDirectImageAffineSectionsLinearEquiv_of_counit_quasiIso f M I hI 0
        (G.map (F.toRightDerivedZero.app M) x) = moduleResolutionSectionClass X α I 0 s := by
    have hz := ConcreteCategory.congr_hom (affineSectionsHomologyMap_toRightDerivedZero f M I hI) x
    change moduleHigherDirectImageAffineSectionsHomologyMap_of_counit_quasiIso f M I hI 0
        (G.map (F.toRightDerivedZero.app M) x) = C.homologyπ 0 (z x) at hz
    change moduleResolutionSectionsCohomologyLinearEquiv X α I 0
        (homologyMap cf.hom 0
          (moduleHigherDirectImageAffineSectionsHomologyMap_of_counit_quasiIso f M I hI 0
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
      (moduleHigherDirectImageAffineSectionsLinearEquiv_of_counit_quasiIso f M I hI 0
        (G.map (F.toRightDerivedZero.app M) x)) = _
  rw [hE]
  exact resolutionSectionClass_zero X α M I s _ hs

end AlgebraicGeometry.Scheme.Cohomology
