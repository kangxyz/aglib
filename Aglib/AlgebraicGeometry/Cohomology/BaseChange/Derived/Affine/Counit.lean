/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Derived.Affine.Sections
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Resolution

/-!
# The actual resolved flat base-change map through the original affine counits

The original affine pullback comparison and original tilde counits identify
the actual resolved geometric map with tilde of the same section-complex
scalar mate. Resolution terms need not be quasicoherent. The qcqs counit
quasi-isomorphisms and flat scalar comparison then prove a quasi-isomorphism
of that original resolved geometric map.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

/-- Retain the original native standard derived models of the actual module sheaves. -/
local instance affineBaseChangeCounitStandard (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
  (a : Y ⟶ X) (b : Y ⟶ Spec S)
  (f : X ⟶ Spec R) (φ : R ⟶ S)
  (h : IsPullback a b f (Spec.map φ)) [Flat a]
  {M : X.Modules} (I : InjectiveResolution M)
  (J : InjectiveResolution ((Scheme.Modules.pullback a).obj M))

/-- Native complex composition comparisons retain the original affine pullback isomorphism. -/
def affineTildePullbackComplexIso (C : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((Scheme.Modules.pullback (Spec.map φ)).mapHomologicalComplex
        (.up ℤ)).obj (((tilde.functor R).mapHomologicalComplex (.up ℤ)).obj C) ≅
      ((tilde.functor S).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars φ.hom).mapHomologicalComplex (.up ℤ)).obj C) :=
  (Functor.mapHomologicalComplexCompIso
      (Iso.refl (tilde.functor R ⋙ Scheme.Modules.pullback
        (Spec.map φ))) (.up ℤ)).app C ≪≫
    (NatIso.mapHomologicalComplex
      (Scheme.Modules.tildePullbackIso φ) (.up ℤ)).app C ≪≫
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (ModuleCat.extendScalars φ.hom ⋙ tilde.functor S)) (.up ℤ)).app C).symm

/-- The native complex pullback comparison has the original affine pullback component. -/
theorem affineTildePullbackComplexIso_inv_f
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    (affineTildePullbackComplexIso φ C).inv.f i =
      (Scheme.Modules.tildePullbackIso φ).inv.app (C.X i) := by
  simp only [affineTildePullbackComplexIso, Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
    HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_inv_app_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app]
  erw [Category.id_comp, Category.comp_id]

private theorem tildeCounit_of_scalarMate (φ : R ⟶ S) (P : (Spec R).Modules)
    (Q : (Spec S).Modules) (k : (Scheme.Modules.pullback (Spec.map φ)).obj P ⟶ Q)
    (D : (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj P) ⟶
      moduleSpecΓFunctor.obj Q)
    (hD : D = ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv
      (moduleSpecΓFunctor.obj P) (moduleSpecΓFunctor.obj Q)).symm
        (moduleSpecΓFunctor.map
            ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app P ≫
              (Scheme.Modules.pushforward (Spec.map φ)).map k) ≫
          (Scheme.Modules.pushforwardGlobalSectionsIso φ).hom.app Q)) :
    (tilde.functor S).map D ≫ Q.fromTildeΓ =
      (Scheme.Modules.tildePullbackIso φ).inv.app (moduleSpecΓFunctor.obj P) ≫
        (Scheme.Modules.pullback (Spec.map φ)).map P.fromTildeΓ ≫ k := by
  rw [hD]
  exact Scheme.Modules.tildePullbackIso_counit φ P Q k

private theorem affineBaseChangeResolution_counit_component (i : ℤ) :
    (Scheme.Modules.tildePullbackIso φ).inv.app
        (moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward f).obj (I.cochainComplex.X i))) ≫
      (Scheme.Modules.pullback (Spec.map φ)).map
        ((Scheme.Modules.pushforward f).obj (I.cochainComplex.X i)).fromTildeΓ ≫
      (Scheme.Modules.cartesianBaseChangeMap a b f (Spec.map φ) h).app
          (I.cochainComplex.X i) ≫
        (Scheme.Modules.pushforward b).map
          ((InjectiveResolution.mapCochainComparison (Scheme.Modules.pullback a) I J).f i) =
      (tilde.functor S).map ((affineBaseChangeResolutionSectionsMap a b f φ h I J).f i) ≫
        ((Scheme.Modules.pushforward b).obj (J.cochainComplex.X i)).fromTildeΓ := by
  have hd := affineBaseChangeResolutionSectionsMap_f_eq_scalarMate a b f φ h I J i
  exact (tildeCounit_of_scalarMate φ
    ((Scheme.Modules.pushforward f).obj (I.cochainComplex.X i))
    ((Scheme.Modules.pushforward b).obj (J.cochainComplex.X i))
    ((Scheme.Modules.cartesianBaseChangeMap a b f (Spec.map φ) h).app
        (I.cochainComplex.X i) ≫
      (Scheme.Modules.pushforward b).map
        ((InjectiveResolution.mapCochainComparison (Scheme.Modules.pullback a) I J).f i))
    ((affineBaseChangeResolutionSectionsMap a b f φ h I J).f i)
    hd).symm

/-- The actual resolved geometric map is tilde of its original scalar mate through the
original affine pullback comparison and the original source and target counits. -/
theorem affineBaseChangeResolution_counit :
    let K : CochainComplex (Spec R).Modules ℤ :=
      ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let L : CochainComplex (Spec S).Modules ℤ :=
      ((Scheme.Modules.pushforward b).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
    let C : CochainComplex (ModuleCat.{u} R) ℤ :=
      (moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K
    (affineTildePullbackComplexIso φ C).inv ≫
        ((Scheme.Modules.pullback (Spec.map φ)).mapHomologicalComplex
          (.up ℤ)).map
          (Scheme.Modules.Complex.tildeGlobalSectionsCounit R (.up ℤ) K) ≫
        (Scheme.Modules.flatBaseChangeResolutionMapPlus a b f
          (Spec.map φ) h M I J).hom =
      ((tilde.functor S).mapHomologicalComplex (.up ℤ)).map
          (affineBaseChangeResolutionSectionsMap a b f φ h I J) ≫
        Scheme.Modules.Complex.tildeGlobalSectionsCounit S (.up ℤ) L := by
  dsimp only
  ext i : 1
  simp only [HomologicalComplex.comp_f, affineTildePullbackComplexIso_inv_f,
    Functor.mapHomologicalComplex_map_f, Scheme.Modules.Complex.tildeGlobalSectionsCounit_f,
    Scheme.Modules.flatBaseChangeResolutionMapPlus_hom_f]
  exact affineBaseChangeResolution_counit_component a b f φ h I J i

/-- The original resolved geometric flat base-change map is a quasi-isomorphism over affine
bases for a qcqs morphism and quasicoherent coefficient, on every supplied resolution. -/
theorem flatBaseChangeResolutionMapPlus_quasiIso_of_spec [QuasiCompact f] [QuasiSeparated f]
    [M.IsQuasicoherent] (hflat : φ.hom.Flat) :
    QuasiIso (Scheme.Modules.flatBaseChangeResolutionMapPlus a b f
      (Spec.map φ) h M I J).hom := by
  let : Flat (Spec.map φ) := Flat.SpecMap_iff.mpr hflat
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  let N : Y.Modules := (Scheme.Modules.pullback a).obj M
  let : N.IsQuasicoherent := Scheme.Modules.quasicoherent_pullback a M
  let K : CochainComplex (Spec R).Modules ℤ :=
    ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let L : CochainComplex (Spec S).Modules ℤ :=
    ((Scheme.Modules.pushforward b).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
  let C : CochainComplex (ModuleCat.{u} R) ℤ :=
    (moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K
  let e := affineTildePullbackComplexIso φ C
  let θ := Scheme.Modules.Complex.tildeGlobalSectionsCounit R (.up ℤ) K
  let θ' := Scheme.Modules.Complex.tildeGlobalSectionsCounit S (.up ℤ) L
  let P := (Scheme.Modules.pullback (Spec.map φ)).mapHomologicalComplex
    (.up ℤ)
  let t := e.inv ≫ P.map θ
  let γ := (Scheme.Modules.flatBaseChangeResolutionMapPlus a b f
    (Spec.map φ) h M I J).hom
  let δ := affineBaseChangeResolutionSectionsMap a b f φ h I J
  let : QuasiIso θ := moduleResolutionPushforwardTildeCounit_quasiIso f M I
  let : QuasiIso θ' := moduleResolutionPushforwardTildeCounit_quasiIso b N J
  let : QuasiIso δ := affineBaseChangeResolutionSectionsMap_quasiIso a b f φ h I J hflat
  let : QuasiIso t := by dsimp only [t, P]; infer_instance
  have hcomp : QuasiIso (t ≫ γ) := by
    have he := affineBaseChangeResolution_counit a b f φ h I J
    change t ≫ γ =
      ((tilde.functor S).mapHomologicalComplex (.up ℤ)).map δ ≫ θ' at he
    rw [he]
    infer_instance
  exact (quasiIso_iff_comp_left t γ).mp hcomp

end AlgebraicGeometry.Scheme.Cohomology
