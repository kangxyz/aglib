/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ZeroLocus.Pullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Uniqueness
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Pairing
public import Aglib.AlgebraicGeometry.Modules.Pullback.FreeTransfer
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Tensor
public import Aglib.AlgebraicGeometry.ProjectiveSpace.HomogeneousEvaluation
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Equivalence.Hom
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Point

/-!
# The closed subscheme cut out by a subsheaf of the free sheaf on the monomials

Let `A` be a ring, `P = P^n_A = ProjectiveSpace A ι`, `T` a scheme over `Spec A` through
`g : T ⟶ Spec A`, and `X_T = P ×_{Spec A} T` (`pullback (toSpec A ι) g`) with projections
`p : X_T ⟶ P` (`pullback.fst`) and `π : X_T ⟶ T` (`pullback.snd`). Fix `r : ℕ` and a family
`s : I → A[x]_r` of homogeneous polynomials of degree `r`; the case of interest is the family of
all monomials `x^a` of degree `r` (`monomialFamily`).

* `homogeneousEvaluation ι r s : 𝒪_P^I ⟶ 𝒪(r)` (`ProjectiveSpace/HomogeneousEvaluation`) sends the
  basis section `e_i` to the section `s i` of `𝒪(r)`; for the monomials (`monomialFamily`) it is
  the monomial map `monomialMap`.
* `homogeneousEvaluationPairing ι r s : 𝒪_P^I ⊗ 𝒪(-r) ⟶ 𝒪(r) ⊗ 𝒪(-r) ≅ 𝒪` untwists it through
  `twistingTensorNegIso`.
* For `ιK : K ⟶ 𝒪_T^I`, `twistedEvaluationMap ι g r s ιK : π^* K ⊗ p^* 𝒪(-r) ⟶ 𝒪_{X_T}` is
  `π^* K ⟶ π^* 𝒪_T^I ≅ 𝒪^I ≅ p^* 𝒪_P^I` (`Scheme.Modules.freeTransfer`) tensored with
  `p^* 𝒪(-r)`, followed by the pullback of the evaluation pairing
  (`Scheme.Modules.pullbackPairingOf`). Informally, on the chart `x_i ≠ 0` a section
  `k = (k_a)` of `K` gives the function `Σ_a k_a s_a / x_i^r`; this local description is not
  formalized here.
* `evaluationIdeal ι g r s ιK : X_T.IdealSheafData` is the image ideal of this map
  (`Scheme.Modules.Hom.imageIdealData`); its closed subscheme is `Z(K)`.

Main results:

* `evaluationIdeal_comap_baseChangeMap`: **base change**. For `f : T' ⟶ T` over `Spec A` and
  quasi-coherent `K`, the pullback of `Z(K)` along `X_{T'} ⟶ X_T` (`baseChangeMap`) is
  `Z(f^* K)`, where `f^* K` carries the pulled-back inclusion `f^* ιK ≫ pullbackFreeIso f I`. No
  flatness is needed: the image ideal commutes with every pullback
  (`Scheme.Modules.Hom.imageIdealData_pullback`).
* `evaluationIdeal_eq_of_iso`: `Z(K)` depends only on `K` as an object over `𝒪_T^I`.

Source: Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 26,
"Use of Flattening Stratification", property (F): for `K_Y = φ^* ker(f)`, the composite
`h : π_Y^* K_Y → π_Y^*(W ⊗ Sym^r V) = π_Y^* π_{Y*} E_Y(r) → E_Y(r)` (written with `E_Y` there,
since `π_* E(r) = W ⊗ Sym^r V`) and its cokernel `q`. For the Hilbert scheme `E = 𝒪_X`,
`W = 𝒪_S`, and `Sym^r V` is free on the monomials of degree `r`; the ideal of `Z(K)` is the image
of `h(-r)`, so that the cokernel of `h` is `𝒪_{Z(K)}(r)` (this identification of the cokernel is
not formalized here). Encoded subset: `P^n_A` over any ring `A`, any scheme `T` over `Spec A`,
any `r`, any family `s` and any `ιK` (no injectivity or local freeness).
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits MvPolynomial

namespace AlgebraicGeometry.ProjectiveSpace

variable (ι : Type u) {A : Type u} [CommRing A]

/-- **The untwisted evaluation pairing** `𝒪_P^I ⊗ 𝒪(-r) ⟶ 𝒪(r) ⊗ 𝒪(-r) ≅ 𝒪`. -/
def homogeneousEvaluationPairing (r : ℕ) {I : Type u} (s : I → homogeneousSubmodule ι A r) :
    (show (ProjectiveSpace A ι).Modules from
      Scheme.Modules.tensorSheaf (ProjectiveSpace A ι)
        (SheafOfModules.free (R := (ProjectiveSpace A ι).ringCatSheaf) I)
        (twistingSheaf A ι (-(r : ℤ)))) ⟶
      (show (ProjectiveSpace A ι).Modules from
        SheafOfModules.unit (ProjectiveSpace A ι).ringCatSheaf) :=
  Scheme.Modules.tensorSheafMap (ProjectiveSpace A ι) (homogeneousEvaluation ι r s) (𝟙 _) ≫
    (twistingTensorNegIso (R := A) (ι := ι) (r : ℤ)).hom

variable {T : Scheme.{u}} (g : T ⟶ Spec (CommRingCat.of A))

/-- **The twisted evaluation map** `π^* K ⊗ p^* 𝒪(-r) ⟶ 𝒪` on `X_T = P^n_A ×_{Spec A} T` of
`ιK : K ⟶ 𝒪_T^I`: the transfer `π^* K ⟶ p^* 𝒪_P^I` tensored with `p^* 𝒪(-r)`, followed by the
pullback along `p` of the evaluation pairing `𝒪_P^I ⊗ 𝒪(-r) ⟶ 𝒪`. -/
def twistedEvaluationMap (r : ℕ) {I : Type u} (s : I → homogeneousSubmodule ι A r)
    {K : T.Modules} (ιK : K ⟶ SheafOfModules.free (R := T.ringCatSheaf) I) :
    (show (pullback (toSpec A ι) g).Modules from
      Scheme.Modules.tensorSheaf (pullback (toSpec A ι) g)
        ((Scheme.Modules.pullback (pullback.snd (toSpec A ι) g)).obj K)
        ((Scheme.Modules.pullback (pullback.fst (toSpec A ι) g)).obj
          (twistingSheaf A ι (-(r : ℤ))))) ⟶
      (show (pullback (toSpec A ι) g).Modules from
        SheafOfModules.unit (pullback (toSpec A ι) g).ringCatSheaf) :=
  Scheme.Modules.pullbackPairingOf (pullback.fst (toSpec A ι) g)
    (homogeneousEvaluationPairing ι r s)
    (Scheme.Modules.freeTransfer (pullback.snd (toSpec A ι) g) (pullback.fst (toSpec A ι) g) ιK)

/-- **The closed subscheme `Z(K)`** of `X_T = P^n_A ×_{Spec A} T` cut out by `ιK : K ⟶ 𝒪_T^I`: its
ideal is the image ideal (`Scheme.Modules.Hom.imageIdealData`) of `π^* K ⊗ p^* 𝒪(-r) ⟶ 𝒪`; for
quasi-coherent `K` this is the image of that map (Nitsure, arXiv:math/0504590v1, §5, p. 26,
property (F), with `E = 𝒪_X`, so that `E(r) = 𝒪(r)`). For general `K` it is the largest
quasi-coherent ideal contained in the section images. -/
def evaluationIdeal (r : ℕ) {I : Type u} (s : I → homogeneousSubmodule ι A r)
    {K : T.Modules} (ιK : K ⟶ SheafOfModules.free (R := T.ringCatSheaf) I) :
    (pullback (toSpec A ι) g).IdealSheafData :=
  Scheme.Modules.Hom.imageIdealData (twistedEvaluationMap ι g r s ιK)

/-- The source of the twisted evaluation map is quasi-coherent for quasi-coherent `K`. -/
theorem isQuasicoherent_twistedEvaluationSource (r : ℕ) {K : T.Modules} [K.IsQuasicoherent] :
    (Scheme.Modules.tensorSheaf (pullback (toSpec A ι) g)
        ((Scheme.Modules.pullback (pullback.snd (toSpec A ι) g)).obj K)
        ((Scheme.Modules.pullback (pullback.fst (toSpec A ι) g)).obj
          (twistingSheaf A ι (-(r : ℤ))))).IsQuasicoherent :=
  Scheme.Modules.isQuasicoherent_moduleTensorLeftFunctor
    ((Scheme.Modules.pullback (pullback.snd (toSpec A ι) g)).obj K)
    ((Scheme.Modules.pullback (pullback.fst (toSpec A ι) g)).obj (twistingSheaf A ι (-(r : ℤ))))

/-- **`Z(K)` depends only on `K` over `𝒪_T^I`**: an isomorphism `e : K ≅ K'` with
`e ≫ ιK' = ιK` gives `Z(K) = Z(K')`. -/
theorem evaluationIdeal_eq_of_iso (r : ℕ) {I : Type u} (s : I → homogeneousSubmodule ι A r)
    {K K' : T.Modules} (e : K ≅ K') (ιK : K ⟶ SheafOfModules.free (R := T.ringCatSheaf) I)
    (ιK' : K' ⟶ SheafOfModules.free (R := T.ringCatSheaf) I) (he : e.hom ≫ ιK' = ιK) :
    evaluationIdeal ι g r s ιK = evaluationIdeal ι g r s ιK' := by
  have hj : (Scheme.Modules.pullback (pullback.snd (toSpec A ι) g)).map e.hom ≫
      Scheme.Modules.freeTransfer (pullback.snd (toSpec A ι) g) (pullback.fst (toSpec A ι) g)
        ιK' =
      Scheme.Modules.freeTransfer (pullback.snd (toSpec A ι) g) (pullback.fst (toSpec A ι) g)
        ιK := by
    rw [Scheme.Modules.freeTransfer, Scheme.Modules.freeTransfer, ← Functor.map_comp_assoc, he]
  have hmap : twistedEvaluationMap ι g r s ιK =
      (Scheme.Modules.tensorSheafIso _
        ((Scheme.Modules.pullback (pullback.snd (toSpec A ι) g)).mapIso e)
        (Iso.refl _)).hom ≫ twistedEvaluationMap ι g r s ιK' := by
    simp only [twistedEvaluationMap, Scheme.Modules.pullbackPairingOf,
      Scheme.Modules.tensorSheafIso_hom, Functor.mapIso_hom, Iso.refl_hom]
    rw [Scheme.Modules.tensorSheafMap_comp_assoc, hj, Category.id_comp]
  rw [evaluationIdeal, evaluationIdeal, hmap, Scheme.Modules.Hom.imageIdealData_precomp_iso]

variable {g}

/-- **Base change of `Z(K)`** (Nitsure, arXiv:math/0504590v1, §5, p. 26, property (F):
`K_Y = φ^* ker(f)`): for `f : T' ⟶ T` over `Spec A` and quasi-coherent `K`, the pullback of
`Z(K)` along `baseChangeMap : X_{T'} ⟶ X_T` is `Z(f^* K)`, where `f^* K` carries the pulled-back
map `f^* ιK ≫ pullbackFreeIso f I` into `𝒪_{T'}^I`. No flatness is needed. -/
theorem evaluationIdeal_comap_baseChangeMap {T' : Scheme.{u}}
    (g' : T' ⟶ Spec (CommRingCat.of A)) (f : T' ⟶ T) (h : f ≫ g = g') (r : ℕ) {I : Type u}
    (s : I → homogeneousSubmodule ι A r) {K : T.Modules} [K.IsQuasicoherent]
    (ιK : K ⟶ SheafOfModules.free (R := T.ringCatSheaf) I) :
    (evaluationIdeal ι g r s ιK).comap (baseChangeMap ι g g' f h) =
      evaluationIdeal ι g' r s
        ((Scheme.Modules.pullback f).map ιK ≫ (Scheme.Modules.pullbackFreeIso f I).hom) := by
  have := isQuasicoherent_twistedEvaluationSource ι g r (K := K)
  let b := baseChangeMap ι g g' f h
  have hp : b ≫ pullback.fst (toSpec A ι) g = pullback.fst (toSpec A ι) g' :=
    baseChangeMap_fst ι g g' f h
  have hπ : b ≫ pullback.snd (toSpec A ι) g = pullback.snd (toSpec A ι) g' ≫ f :=
    baseChangeMap_snd ι g g' f h
  let L := twistingSheaf A ι (-(r : ℤ))
  let E := Scheme.Modules.tensorSheafIso _
      ((Scheme.Modules.pullbackSquareIso b (pullback.snd (toSpec A ι) g')
        (pullback.snd (toSpec A ι) g) f hπ).app K)
      ((Scheme.Modules.pullbackCongr hp.symm).app L ≪≫
        ((Scheme.Modules.pullbackComp b (pullback.fst (toSpec A ι) g)).app L).symm) ≪≫
    (Scheme.Modules.pullbackTensorMapIso b
      ((Scheme.Modules.pullback (pullback.snd (toSpec A ι) g)).obj K)
      ((Scheme.Modules.pullback (pullback.fst (toSpec A ι) g)).obj L)).symm
  have key : E.hom ≫ Scheme.Modules.Hom.pullbackToUnit b (twistedEvaluationMap ι g r s ιK) =
      twistedEvaluationMap ι g' r s
        ((Scheme.Modules.pullback f).map ιK ≫ (Scheme.Modules.pullbackFreeIso f I).hom) := by
    have hB := Scheme.Modules.pullbackPairingOf_pullback (pullback.fst (toSpec A ι) g) b
      (pullback.fst (toSpec A ι) g') hp (homogeneousEvaluationPairing ι r s)
      (Scheme.Modules.freeTransfer (pullback.snd (toSpec A ι) g)
        (pullback.fst (toSpec A ι) g) ιK)
      ((Scheme.Modules.pullbackSquareIso b (pullback.snd (toSpec A ι) g')
        (pullback.snd (toSpec A ι) g) f hπ).app K).hom
      (Scheme.Modules.freeTransfer (pullback.snd (toSpec A ι) g')
        (pullback.fst (toSpec A ι) g')
        ((Scheme.Modules.pullback f).map ιK ≫ (Scheme.Modules.pullbackFreeIso f I).hom))
      (Scheme.Modules.pullbackSquareIso_hom_freeTransfer b (pullback.snd (toSpec A ι) g)
        (pullback.snd (toSpec A ι) g') f hπ (pullback.fst (toSpec A ι) g)
        (pullback.fst (toSpec A ι) g') hp ιK)
    simp only [E, Iso.trans_hom, Iso.symm_hom, Scheme.Modules.tensorSheafIso_hom,
      Iso.app_hom, Iso.app_inv, Category.assoc]
    exact hB
  calc (evaluationIdeal ι g r s ιK).comap b
      = Scheme.Modules.Hom.imageIdealData
          (Scheme.Modules.Hom.pullbackToUnit b (twistedEvaluationMap ι g r s ιK)) :=
        (Scheme.Modules.Hom.imageIdealData_pullback b _).symm
    _ = Scheme.Modules.Hom.imageIdealData
          (E.hom ≫ Scheme.Modules.Hom.pullbackToUnit b (twistedEvaluationMap ι g r s ιK)) :=
        (Scheme.Modules.Hom.imageIdealData_precomp_iso E _).symm
    _ = _ := congrArg Scheme.Modules.Hom.imageIdealData key

end AlgebraicGeometry.ProjectiveSpace
