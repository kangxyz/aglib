/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ZeroLocus
public import Aglib.AlgebraicGeometry.IdealSheaf.Order
public import Aglib.AlgebraicGeometry.IdealSheaf.QuotientModule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# The image factorisation of a module-to-unit map

Let `φ : M ⟶ 𝒪_X` be a morphism of `𝒪_X`-modules whose section image ideals localize
(`Hom.ImageIdealLocalizes φ`; this holds for quasi-coherent `M`,
`Hom.imageIdealLocalizes_of_isQuasicoherent`), and let `I(φ) = Hom.imageIdealData φ`, with ideal
module `idealModule (Hom.zeroInclusion φ)`.

* `Hom.zeroIdealFactor_surjective_affine`: on every affine open `U`, the factor
  `M(U) ⟶ I(φ)(U)` is surjective, since `I(φ)(U)` is the image of `φ_U`
  (`Hom.zeroInclusion_kernel`).
* `Hom.epi_zeroIdealFactor`: the factor `M ⟶ I(φ)` is an epimorphism, so
  `M ↠ I(φ) ↪ 𝒪_X` is an image factorisation of `φ` (`Hom.zeroIdealMonoFactorisationIsImage`).
* `Hom.imageIdealData_eq_of_epi_comp`: if `φ = e ≫ idealInclusion W.subschemeι` for a closed
  subscheme `W` and an epimorphism `e`, then `I(φ) = W`. Two image factorisations of `φ` are
  isomorphic over `𝒪_X`, and closed subschemes are ordered by their ideal inclusions
  (`IdealSheafData.le_of_idealInclusion_factor`).
* `Hom.imageIdealData_epi_comp`: `I(e ≫ φ) = I(φ)` for every epimorphism `e`.
* `Hom.comp_toQuotientModule_imageIdealData_eq_zero`: for quasi-coherent `M`, `φ` vanishes on the
  structure module `𝒪_X / I(φ)`.

No flatness, finiteness or Noetherian hypothesis is used. Consumer: the closed subscheme cut
out by the image of `π^* K(-r) ⟶ 𝒪` in the Hilbert-scheme construction (Nitsure, *Construction
of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 26, property (F)), in
`Aglib.AlgebraicGeometry.HilbertScheme.UniversalSubscheme`.
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

variable {X : Scheme.{u}} {M : X.Modules}
variable (φ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf))

/-- The factor `M ⟶ I(φ)` of a module-to-unit map through its image ideal is surjective on the
sections over every affine open. -/
theorem zeroIdealFactor_surjective_affine (h : ImageIdealLocalizes φ) (U : X.affineOpens) :
    Function.Surjective ((zeroIdealFactor φ h).val.app (op U.1)) := by
  intro a
  have ha := (Scheme.Hom.idealSectionsEquiv (zeroInclusion φ) U.1 a).property
  have ha' : ((Scheme.Hom.idealSectionsEquiv (zeroInclusion φ) U.1 a) : Γ(X, U)) ∈
      sectionImageIdeal φ U.1 :=
    (congrArg (fun I : Ideal Γ(X, U) ↦
      ((Scheme.Hom.idealSectionsEquiv (zeroInclusion φ) U.1 a) : Γ(X, U)) ∈ I)
        (zeroInclusion_kernel φ h U)).mp ha
  obtain ⟨m, hm⟩ := ha'
  refine ⟨m, ?_⟩
  apply (Scheme.Hom.idealSectionsEquiv (zeroInclusion φ) U.1).injective
  apply Subtype.ext
  rw [Scheme.Hom.idealSectionsEquiv_val, Scheme.Hom.idealSectionsEquiv_val]
  have hf := congrArg (fun ψ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ↦
    ψ.val.app (op U.1) m) (zeroIdealFactor_inclusion φ h)
  exact hf.trans (hm.trans (Scheme.Hom.idealSectionsEquiv_val (zeroInclusion φ) U.1 a))

/-- **The factor onto the image ideal is an epimorphism**: for a module-to-unit map `φ` whose
section image ideals localize, `M ⟶ I(φ)` is an epimorphism, because it is surjective on the
sections over every affine open. -/
theorem epi_zeroIdealFactor (h : ImageIdealLocalizes φ) : Epi (zeroIdealFactor φ h) := by
  constructor
  intro T g k hcomp
  apply moduleHom_ext_affine
  intro U
  ext a
  obtain ⟨m, rfl⟩ := zeroIdealFactor_surjective_affine φ h U a
  exact congrArg (fun f ↦ f.val.app (op U.1) m) hcomp

/-- The factorisation `M ↠ I(φ) ↪ 𝒪_X` of a module-to-unit map through its image ideal. -/
@[simps]
def zeroIdealMonoFactorisation (h : ImageIdealLocalizes φ) : MonoFactorisation φ where
  I := idealModule (zeroInclusion φ)
  m := idealInclusion (zeroInclusion φ)
  e := zeroIdealFactor φ h
  fac := zeroIdealFactor_inclusion φ h

/-- `M ↠ I(φ) ↪ 𝒪_X` is an image factorisation of `φ`, since its first map is an epimorphism
(`epi_zeroIdealFactor`). -/
def zeroIdealMonoFactorisationIsImage (h : ImageIdealLocalizes φ) :
    IsImage (zeroIdealMonoFactorisation φ h) :=
  haveI : Epi (zeroIdealMonoFactorisation φ h).e := epi_zeroIdealFactor φ h
  haveI : StrongEpi (zeroIdealMonoFactorisation φ h).e := strongEpi_of_epi _
  StrongEpiMonoFactorisation.toMonoIsImage
    (StrongEpiMonoFactorisation.mk (zeroIdealMonoFactorisation φ h))

variable {φ}

/-- **The image ideal of an epimorphism followed by an ideal inclusion**: if
`φ = e ≫ idealInclusion W.subschemeι` with `e` an epimorphism, the image ideal data of `φ` is
`W`. Both are image factorisations of `φ`, so each ideal inclusion factors through the other. -/
theorem imageIdealData_eq_of_epi_comp (h : ImageIdealLocalizes φ) (W : X.IdealSheafData)
    (e : M ⟶ idealModule W.subschemeι) [Epi e] (he : e ≫ idealInclusion W.subschemeι = φ) :
    imageIdealData φ = W := by
  let F : MonoFactorisation φ :=
    { I := idealModule W.subschemeι
      m := idealInclusion W.subschemeι
      e := e
      fac := he }
  have : StrongEpi F.e := strongEpi_of_epi (show M ⟶ idealModule W.subschemeι from e)
  let hF : IsImage F := StrongEpiMonoFactorisation.toMonoIsImage (StrongEpiMonoFactorisation.mk F)
  apply le_antisymm
  · exact IdealSheafData.le_of_idealInclusion_factor (imageIdealData φ) W
      ((zeroIdealMonoFactorisationIsImage φ h).lift F)
      ((zeroIdealMonoFactorisationIsImage φ h).lift_fac F)
  · exact IdealSheafData.le_of_idealInclusion_factor W (imageIdealData φ)
      (hF.lift (zeroIdealMonoFactorisation φ h)) (hF.lift_fac (zeroIdealMonoFactorisation φ h))

/-- **Precomposition with an epimorphism does not change the image ideal**: for an epimorphism
`e : M' ⟶ M`, `I(e ≫ φ) = I(φ)`, when the section image ideals of both maps localize. -/
theorem imageIdealData_epi_comp {M' : X.Modules} (e : M' ⟶ M) [Epi e]
    (h' : ImageIdealLocalizes (e ≫ φ)) (h : ImageIdealLocalizes φ) :
    imageIdealData (e ≫ φ) = imageIdealData φ := by
  have := epi_zeroIdealFactor φ h
  refine imageIdealData_eq_of_epi_comp h' (imageIdealData φ) (e ≫ zeroIdealFactor φ h) ?_
  rw [Category.assoc]
  exact congrArg (e ≫ ·) (zeroIdealFactor_inclusion φ h)

/-- `I(e ≫ φ) = I(φ)` for an epimorphism `e` between quasi-coherent modules. -/
theorem imageIdealData_epi_comp_of_isQuasicoherent {M' : X.Modules} [M.IsQuasicoherent]
    [M'.IsQuasicoherent] (e : M' ⟶ M) [Epi e] :
    imageIdealData (e ≫ φ) = imageIdealData φ :=
  imageIdealData_epi_comp e (imageIdealLocalizes_of_isQuasicoherent _)
    (imageIdealLocalizes_of_isQuasicoherent _)

/-- **A module-to-unit map vanishes on the structure module of its image ideal**: for `φ : M ⟶ 𝒪`
with `M` quasi-coherent, `φ` followed by `𝒪 ⟶ 𝒪 / I(φ)` is zero, since `φ` factors through the
ideal `I(φ)` (`zeroIdealFactor_inclusion`). -/
theorem comp_toQuotientModule_imageIdealData_eq_zero [M.IsQuasicoherent]
    (φ : M ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)) :
    φ ≫ (imageIdealData φ).toQuotientModule = 0 := by
  have h := zeroIdealFactor_inclusion φ (imageIdealLocalizes_of_isQuasicoherent φ)
  have h0 : Scheme.Hom.idealInclusion (zeroInclusion φ) ≫ (imageIdealData φ).toQuotientModule =
      0 :=
    (imageIdealData φ).shortComplex.zero
  calc φ ≫ (imageIdealData φ).toQuotientModule
      = zeroIdealFactor φ (imageIdealLocalizes_of_isQuasicoherent φ) ≫
          (Scheme.Hom.idealInclusion (zeroInclusion φ) ≫
            (imageIdealData φ).toQuotientModule) := by
        rw [← Category.assoc, h]
    _ = 0 := by rw [h0, comp_zero]

end AlgebraicGeometry.Scheme.Modules.Hom
