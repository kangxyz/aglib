/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.PositiveSection
public import Aglib.AlgebraicGeometry.Modules.InternalHom.HomFunctor
public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual
public import Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.Uniqueness
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.TensorAssociator
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.SchemeOverField
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Field
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf
public import Aglib.AlgebraicGeometry.Geometrically.Integral.GlobalSections
public import Aglib.AlgebraicGeometry.Cohomology.Finiteness.ProperInputs
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Isomorphism
public import Aglib.AlgebraicGeometry.Cohomology.Finiteness.Coherent
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Vanishing.Basic
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Relative
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Rank

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Divisors.Relative.PositiveSectionUniqueness`
at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`edf24adc21ee38b36ada4e290d1120cc34c79abfaa1220bcac2d8a056ba42900`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme
  (NormalComponentsOpen  SmoothClosedPointDimension
    SmoothFieldDimension SmoothFieldNormality SmoothFieldRegularity)
open _root_.AlgebraicGeometry.Scheme.Cohomology
  (FibreCohomologyConcentrated LocalFreeCohomologyBaseChange NoetherianSheafCohomologyVanishing
    ProperStructureCohomologyBaseChange)
open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (IsLocallyRankOne classOf dualLineBundle dualSheaf pullbackClass pullbackClass_zero
    pullbackLineBundle )
open _root_.AlgebraicGeometry.Scheme.Modules (pullbackUnitIso)
open _root_.AlgebraicGeometry.Scheme.OverField (Base FScheme)

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/
/-!
# Injectivity of the actual Abel class on field-valued points

The actual positive-divisor section is a generator of its direct image in
relative degree one and genus one. This is derived from actual geometric
fibre degree, coherent Riemann–Roch and arbitrary-base cohomology/base change.
Over Spec K a nonzero map of actual line bundles is invertible directly;
the optional finite-locally-free geometric isomorphism family is not used.

An isomorphism of positive-divisor bundles identifies their canonical
sections up to the pullback of an actual structure-module automorphism.
Literal internal-Hom functoriality and canonical biduality identify the
actual kernel ideals. The native zero-scheme comparison then identifies
sections themselves. Pic(Spec K)=0 removes the origin normalization.
The final injectivity theorem tests every field K and every structural
Spec K → Spec F, not merely a chosen algebraic closure. No inverse,
injectivity, graph uniqueness or group-law conclusion is a premise.
All retained general source families are the previously reviewed incoming
curve, degree, cohomology and Cartier families in the explicit signature.

Manuscript application: K2-018 `prop:k2018-arithmetic-characters` and
`lem:k2018-geometric-exact-order`, mathematical-source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen engineering basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
Incoming HomFunctor d8752f682a16137aba0d5ea899ff1d46a81cddf8b6c72b88525805443bdcf52a;
Bidual 4b38bdec5013bba396fa0f04e0bf9d732107a18af31208e19996c3b01fa537bc;
Uniqueness 089219d061fb4d158a7e3156c93853e8df8b22d5966eb485f61a6500a93c4e45.
-/
noncomputable section
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Hom
open AlgebraicGeometry.Scheme.Modules.Invertible
namespace AlgebraicGeometry.Scheme.Hom
universe u
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Hom
variable {X S D E : Scheme.{u}} (p : X ⟶ S) (i : D ⟶ X) (j : E ⟶ X)
variable (hI : IsLocallyRankOne X (idealModule i)) (hJ : IsLocallyRankOne X (idealModule j))
variable [IsIso (divisorPositiveAdjoint p i hI)] [IsIso (divisorPositiveAdjoint p j hJ)]
variable (e : (show X.Modules from (dualLineBundle X ⟨idealModule i, hI⟩).val) ≅
  (show X.Modules from (dualLineBundle X ⟨idealModule j, hJ⟩).val))
/-- The base unit-module automorphism induced by `e` through the two invertible positive
adjoints. -/
def positiveBaseIso :
    (show S.Modules from SheafOfModules.unit S.ringCatSheaf) ≅
      (show S.Modules from SheafOfModules.unit S.ringCatSheaf) :=
  asIso (divisorPositiveAdjoint p i hI) ≪≫ (Scheme.Modules.pushforward p).mapIso e ≪≫
    (asIso (divisorPositiveAdjoint p j hJ)).symm

/-- The unit-module automorphism on `X` obtained by pulling back the induced base automorphism. -/
def positiveUnitIso :
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ≅
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) :=
  (pullbackUnitIso p).symm ≪≫ (Scheme.Modules.pullback p).mapIso (positiveBaseIso p i j hI hJ e) ≪≫
    pullbackUnitIso p

theorem positiveSection_iso_square :
    divisorPositiveSection i hI ≫ e.hom =
      (positiveUnitIso p i j hI hJ e).hom ≫ divisorPositiveSection j hJ := by
  have hh : ((pullbackUnitIso p).hom ≫ divisorPositiveSection i hI) ≫ e.hom =
      (Scheme.Modules.pullback p).map (positiveBaseIso p i j hI hJ e).hom ≫
        ((pullbackUnitIso p).hom ≫ divisorPositiveSection j hJ) := by
    apply ((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left]
    change divisorPositiveAdjoint p i hI ≫ (Scheme.Modules.pushforward p).map e.hom =
      (positiveBaseIso p i j hI hJ e).hom ≫ divisorPositiveAdjoint p j hJ
    simp [positiveBaseIso, Category.assoc]
  apply (cancel_epi (pullbackUnitIso p).hom).mp
  simpa [positiveUnitIso, Category.assoc] using hh
end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom
universe u
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Hom
variable {X : Scheme.{u}} {M N : SheafOfModules.{u} X.ringCatSheaf}
variable (σ : SheafOfModules.unit X.ringCatSheaf ⟶ M)
variable (τ : SheafOfModules.unit X.ringCatSheaf ⟶ N)
variable (e : M ≅ N)
variable (v : SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.unit X.ringCatSheaf)
/-- The unit-module automorphism induced by precomposition with `v.symm` on internal Hom. -/
def dualUnitIso : SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.unit X.ringCatSheaf :=
  (Scheme.Modules.InternalHom.unitSourceIso X (SheafOfModules.unit
      X.ringCatSheaf)).symm ≪≫
    AlgebraicGeometry.Scheme.Modules.InternalHom.iso X v.symm (Iso.refl _) ≪≫
      Scheme.Modules.InternalHom.unitSourceIso X (SheafOfModules.unit
          X.ringCatSheaf)
theorem dualSection_iso_square (h : σ ≫ e.hom = v.hom ≫ τ) :
    (AlgebraicGeometry.Scheme.Modules.InternalHom.iso X e.symm (Iso.refl (SheafOfModules.unit
        X.ringCatSheaf))).hom ≫
      AlgebraicGeometry.Scheme.Modules.InternalHom.dualSection X σ =
          AlgebraicGeometry.Scheme.Modules.InternalHom.dualSection X τ ≫ (dualUnitIso v).hom := by
  have he : AlgebraicGeometry.Scheme.Modules.InternalHom.map X e.hom (𝟙 (SheafOfModules.unit
      X.ringCatSheaf)) ≫
      AlgebraicGeometry.Scheme.Modules.InternalHom.map X σ (𝟙 _) =
          AlgebraicGeometry.Scheme.Modules.InternalHom.map X τ (𝟙 _) ≫
          AlgebraicGeometry.Scheme.Modules.InternalHom.map X v.hom (𝟙 _) := by
    rw [AlgebraicGeometry.Scheme.Modules.InternalHom.map_comp,
        AlgebraicGeometry.Scheme.Modules.InternalHom.map_comp, h]
  simpa only [AlgebraicGeometry.Scheme.Modules.InternalHom.iso,
      SheafOfModules.InternalHom.iso, Iso.symm_inv, Iso.refl_hom,
      AlgebraicGeometry.Scheme.Modules.InternalHom.dualSection,
    dualUnitIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
    using congrArg (fun z ↦ z ≫
        (Scheme.Modules.InternalHom.unitSourceIso X
        (SheafOfModules.unit X.ringCatSheaf)).hom) he

theorem dualSection_imageIdeal_eq (h : σ ≫ e.hom = v.hom ≫ τ) :
    imageIdealData (AlgebraicGeometry.Scheme.Modules.InternalHom.dualSection X σ) =
        imageIdealData (AlgebraicGeometry.Scheme.Modules.InternalHom.dualSection X τ) := by
  rw [← imageIdealData_precomp_iso (AlgebraicGeometry.Scheme.Modules.InternalHom.iso X e.symm
      (Iso.refl _)),
    dualSection_iso_square σ τ e v h, imageIdealData_postcomp_unit_iso]

theorem bidual_dualSection_transpose
    (φ : M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    bidualMap X M ≫ AlgebraicGeometry.Scheme.Modules.InternalHom.dualSection X
        (AlgebraicGeometry.Scheme.Modules.InternalHom.transpose X φ) = φ := by
  apply SheafOfModules.hom_ext
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change (AlgebraicGeometry.Scheme.Modules.InternalHom.dualSection X
      (AlgebraicGeometry.Scheme.Modules.InternalHom.transpose X φ)).val.app U
    ((bidualMap X M).val.app U m) = φ.val.app U m
  exact (bidualMap_evaluate X M U.unop m
    ((AlgebraicGeometry.Scheme.Modules.InternalHom.transpose X φ).val.app (op U.unop) (1 :
        Γ(X,U.unop)))).trans
      (AlgebraicGeometry.Scheme.Modules.InternalHom.transpose_one_evaluate X φ U.unop m)

variable {S D E : Scheme.{u}} (p : X ⟶ S) (i : D ⟶ X) (j : E ⟶ X)
variable (hI : IsLocallyRankOne X (idealModule i)) (hJ : IsLocallyRankOne X (idealModule j))
variable [IsIso (divisorPositiveAdjoint p i hI)] [IsIso (divisorPositiveAdjoint p j hJ)]
variable (epos : (show X.Modules from (dualLineBundle X ⟨idealModule i, hI⟩).val) ≅
  (show X.Modules from (dualLineBundle X ⟨idealModule j, hJ⟩).val))
include p hI hJ epos in
theorem kernel_eq_of_positive_iso : i.ker = j.ker := by
  have h := dualSection_imageIdeal_eq (divisorPositiveSection i hI) (divisorPositiveSection j hJ)
    epos (positiveUnitIso p i j hI hJ epos) (positiveSection_iso_square p i j hI hJ epos)
  have side {D : Scheme.{u}} (i : D ⟶ X) (hI : IsLocallyRankOne X (idealModule i)) :
      imageIdealData (AlgebraicGeometry.Scheme.Modules.InternalHom.dualSection X
          (divisorPositiveSection i hI)) = i.ker := by
    let b : (show X.Modules from idealModule i) ≅
        (show X.Modules from dualSheaf X (dualSheaf X (idealModule i))) :=
      bidualIso X ⟨idealModule i, hI⟩
    let φ : (show X.Modules from dualSheaf X (dualSheaf X (idealModule i))) ⟶
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) :=
      AlgebraicGeometry.Scheme.Modules.InternalHom.dualSection X (divisorPositiveSection i hI)
    have hb : b.hom ≫ φ = idealInclusion i :=
      bidual_dualSection_transpose (idealInclusion i)
    exact (imageIdealData_precomp_iso b φ).symm.trans
      ((congrArg imageIdealData hb).trans (imageIdealData_idealInclusion i))
  have hI' := side i hI
  have hJ' := side j hJ
  exact hI'.symm.trans (h.trans hJ')
end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom
universe u
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Hom
variable {X S : Scheme.{u}} (p : X ⟶ S) (i j : S ⟶ X)
variable [IsClosedImmersion i] [IsClosedImmersion j]
theorem section_eq_of_kernel_eq (hi : i ≫ p = 𝟙 _) (hj : j ≫ p = 𝟙 _)
    (h : i.ker = j.ker) : i = j := by
  let e : Over.mk i ≅ Over.mk j :=
    (zeroOverIsoOfIdealEq i (imageIdealData_idealInclusion i)).symm ≪≫
      zeroOverIsoOfIdealEq j ((imageIdealData_idealInclusion i).trans h)
  let q : S ⟶ S := e.hom.left
  have he : q ≫ j = i := Over.w e.hom
  have hid : q = 𝟙 S := by
    calc
      q = q ≫ (j ≫ p) := by rw [hj, Category.comp_id]
      _ = (q ≫ j) ≫ p := (Category.assoc _ _ _).symm
      _ = i ≫ p := by rw [he]
      _ = 𝟙 S := hi
  rw [hid, Category.id_comp] at he
  exact he.symm
end AlgebraicGeometry.Scheme.Hom
