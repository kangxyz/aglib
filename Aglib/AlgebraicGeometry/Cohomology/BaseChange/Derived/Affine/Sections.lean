/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Derived.Affine.Homology
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Derived.Resolution
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Pushforward.Spec
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ScalarAdjunction.Counit

/-!
# Original affine sections of the actual resolved base-change map

The source and target use the original module section complexes of the
actual pushed-forward resolutions. Their native structural-ring
comparisons identify the same geometric-unit tensor map. No resolution
term is required to be quasicoherent.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

/-- Keep the original native standard models in the displayed resolution components. -/
local instance affineResolutionSectionsStandard (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
  (a : Y ⟶ X) (b : Y ⟶ Spec S)
  (f : X ⟶ Spec R) (φ : R ⟶ S)
  (h : IsPullback a b f (Spec.map φ)) [Flat a]
  {M : X.Modules} (I : InjectiveResolution M)
  (J : InjectiveResolution ((Scheme.Modules.pullback a).obj M))

/-- The original tensor map in the native affine section coordinates of the actual
pushed-forward resolutions. Both coordinate maps are the original section identities. -/
def affineBaseChangeResolutionSectionsMap :
    ((ModuleCat.extendScalars φ.hom).mapHomologicalComplex (.up ℤ)).obj
        ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj
          (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj
            I.cochainComplex)) ⟶
      (moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj
        (((Scheme.Modules.pushforward b).mapHomologicalComplex (.up ℤ)).obj
          J.cochainComplex) :=
  ((ModuleCat.extendScalars φ.hom).mapHomologicalComplex (.up ℤ)).map
      (moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ) I.cochainComplex).hom ≫
    moduleResolutionPullbackSectionsTensorMap a
      (f.appTop.hom.comp (Scheme.ΓSpecIso R).inv.hom)
      (b.appTop.hom.comp (Scheme.ΓSpecIso S).inv.hom) φ.hom
      (moduleSectionsBaseChangeScalars a b f φ.hom h.w) I J ≫
    (moduleSpecPushforwardGlobalSectionsComplexIso b (.up ℤ) J.cochainComplex).inv

/-- The original coordinate changes retain the literal geometric-unit and original
resolution-comparison component on every unit pure tensor. -/
theorem affineBaseChangeResolutionSectionsMap_one_tmul (i : ℤ)
    (x : ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj
      (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj
        I.cochainComplex)).X i) :
    (affineBaseChangeResolutionSectionsMap a b f φ h I J).f i ((1 : S) ⊗ₜ[R,φ.hom] x) =
      ((InjectiveResolution.mapCochainComparison (Scheme.Modules.pullback a) I J).f i).app ⊤
        ((((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
          (I.cochainComplex.X i)).app ⊤) x) := by
  simp only [affineBaseChangeResolutionSectionsMap, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, ModuleCat.comp_apply]
  erw [ModuleCat.ExtendScalars.map_tmul,
    moduleSpecPushforwardGlobalSectionsComplexIso_hom_f_apply,
    moduleResolutionPullbackSectionsTensorMap_one_tmul]
  rfl

/-- Every original affine section component is exactly the scalar adjoint of the actual
resolved geometric base-change component, with its original geometric unit. -/
theorem affineBaseChangeResolutionSectionsMap_f_eq_scalarMate (i : ℤ) :
    let P := (Scheme.Modules.pushforward f).obj (I.cochainComplex.X i)
    let Q := (Scheme.Modules.pushforward b).obj (J.cochainComplex.X i)
    let k : (Scheme.Modules.pullback (Spec.map φ)).obj P ⟶ Q :=
      (Scheme.Modules.cartesianBaseChangeMap a b f (Spec.map φ) h).app
          (I.cochainComplex.X i) ≫
        (Scheme.Modules.pushforward b).map
          ((InjectiveResolution.mapCochainComparison (Scheme.Modules.pullback a) I J).f i)
    (affineBaseChangeResolutionSectionsMap a b f φ h I J).f i =
      ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv
        (moduleSpecΓFunctor.obj P) (moduleSpecΓFunctor.obj Q)).symm
          (moduleSpecΓFunctor.map
              ((Scheme.Modules.pullbackPushforwardAdjunction
                  (Spec.map φ)).unit.app P ≫
                (Scheme.Modules.pushforward (Spec.map φ)).map k) ≫
            (Scheme.Modules.pushforwardGlobalSectionsIso φ).hom.app Q) := by
  dsimp only
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  erw [affineBaseChangeResolutionSectionsMap_one_tmul]
  erw [← ModuleCat.extendRestrictScalarsAdj_homEquiv_apply, Equiv.apply_symm_apply]
  have hu := congrArg (fun z => z.app ⊤ x)
    (Scheme.Modules.cartesianBaseChangeMap_unit a b f
      (Spec.map φ) h (I.cochainComplex.X i))
  have hv := congrArg
    (fun y => ((InjectiveResolution.mapCochainComparison (Scheme.Modules.pullback a) I J).f i).app
      ⊤ y) hu
  change ((InjectiveResolution.mapCochainComparison (Scheme.Modules.pullback a) I J).f i).app
      ⊤ ((((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
        (I.cochainComplex.X i)).app ⊤) x) =
    ((InjectiveResolution.mapCochainComparison (Scheme.Modules.pullback a) I J).f i).app ⊤
      (((Scheme.Modules.cartesianBaseChangeMap a b f (Spec.map φ) h).app
          (I.cochainComplex.X i)).app ⊤
        ((((Scheme.Modules.pullbackPushforwardAdjunction
          (Spec.map φ)).unit.app
            ((Scheme.Modules.pushforward f).obj (I.cochainComplex.X i))).app ⊤) x))
  simpa [Scheme.Modules.cartesianPushforwardSquare] using hv

/-- After affine flat base change for a qcqs morphism and a quasicoherent coefficient,
the actual map in native pushed-forward section coordinates is a quasi-isomorphism. -/
theorem affineBaseChangeResolutionSectionsMap_quasiIso [QuasiCompact f] [QuasiSeparated f]
    [M.IsQuasicoherent] (hflat : φ.hom.Flat) :
    QuasiIso (affineBaseChangeResolutionSectionsMap a b f φ h I J) := by
  let : Flat (Spec.map φ) := Flat.SpecMap_iff.mpr hflat
  let := moduleResolutionPullbackSectionsTensorMap_quasiIso_of_isPullback
    a b f φ.hom h hflat M I J
  unfold affineBaseChangeResolutionSectionsMap
  infer_instance

end AlgebraicGeometry.Scheme.Cohomology
