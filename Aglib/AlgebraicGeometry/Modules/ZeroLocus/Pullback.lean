/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ZeroLocus.ImageFactorisation
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.QuotientModule
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback

/-!
# Pullback of the image ideal of a module-to-unit map

For a quasi-coherent `M` on `X`, a morphism `φ : M ⟶ 𝒪_X` and any morphism of schemes
`f : Y ⟶ X`, the image ideal of the pulled-back map `f^* φ : f^* M ⟶ f^* 𝒪_X ≅ 𝒪_Y` is the
pullback of the image ideal of `φ` (`Scheme.Modules.Hom.imageIdealData_pullback`):

`I(f^* φ) = I(φ).comap f`.

No flatness is needed. The image factorisation `M ↠ I(φ) ↪ 𝒪_X`
(`Hom.epi_zeroIdealFactor`) pulls back to `f^* M ↠ f^* I(φ) ⟶ f^* 𝒪_X`, since `f^*` is right
exact (Stacks Project, Tag 01AJ, Lemma 17.3.3), and the image of `f^* I(φ) ⟶ 𝒪_Y` is the ideal of
`I(φ).comap f` (Stacks Project, Tag 01JU, Lemma 26.17.6 (1);
`IdealSheafData.pullbackIdealMonoFactorisation`, `IdealSheafData.epi_idealPullbackMap`). Hence
`f^* M ↠ I(φ.comap f) ↪ 𝒪_Y` is an epimorphism followed by an ideal inclusion, and
`Hom.imageIdealData_eq_of_epi_comp` identifies the image ideal.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite
open AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Modules.Hom

variable {X Y : Scheme.{u}} {M : X.Modules}

/-- The pulled-back map `f^* φ : f^* M ⟶ f^* 𝒪_X ≅ 𝒪_Y` of a module-to-unit map. -/
def pullbackToUnit (f : Y ⟶ X) (φ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) :
    (Scheme.Modules.pullback f).obj M ⟶
      (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf) :=
  (Scheme.Modules.pullback f).map φ ≫ (Scheme.Modules.pullbackUnitIso f).hom

/-- `f^* M ↠ f^* I(φ) ↠ I(I(φ).comap f) ↪ 𝒪_Y` factors the pulled-back map: the pulled-back image
factor followed by the ideal comparison of the pulled-back closed subscheme. -/
theorem pullback_zeroIdealFactor_comp_idealPullbackMap_inclusion (f : Y ⟶ X)
    (φ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
    (h : ImageIdealLocalizes φ) :
    ((Scheme.Modules.pullback f).map (zeroIdealFactor φ h) ≫
        (IdealSheafData.pullbackIdealMonoFactorisation (imageIdealData φ) f).e) ≫
      idealInclusion ((imageIdealData φ).comap f).subschemeι = pullbackToUnit f φ := by
  rw [Category.assoc]
  erw [(IdealSheafData.pullbackIdealMonoFactorisation (imageIdealData φ) f).fac]
  rw [IdealSheafData.pullbackIdealToUnit, ← Functor.map_comp_assoc,
    show zeroIdealFactor φ h ≫ idealInclusion (imageIdealData φ).subschemeι = φ from
      zeroIdealFactor_inclusion φ h]
  rfl

/-- **The image ideal commutes with pullback, without flatness**: for quasi-coherent `M`, a
morphism `φ : M ⟶ 𝒪_X` and any `f : Y ⟶ X`, the image ideal of
`f^* φ : f^* M ⟶ f^* 𝒪_X ≅ 𝒪_Y` is `I(φ).comap f`. -/
theorem imageIdealData_pullback (f : Y ⟶ X) [M.IsQuasicoherent]
    (φ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) :
    imageIdealData (pullbackToUnit f φ) = (imageIdealData φ).comap f := by
  have h := imageIdealLocalizes_of_isQuasicoherent φ
  have : (Scheme.Modules.pullback f).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (Scheme.Modules.pullbackPushforwardAdjunction f)
  have := epi_zeroIdealFactor φ h
  have : Epi (IdealSheafData.pullbackIdealMonoFactorisation (imageIdealData φ) f).e :=
    IdealSheafData.epi_idealPullbackMap _ f _ _
  exact imageIdealData_eq_of_epi_comp (imageIdealLocalizes_of_isQuasicoherent _)
    ((imageIdealData φ).comap f) _
    (pullback_zeroIdealFactor_comp_idealPullbackMap_inclusion f φ h)

end AlgebraicGeometry.Scheme.Modules.Hom
