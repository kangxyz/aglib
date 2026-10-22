/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AffineAtlas
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Affine
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom

/-!
# Original ideal frames on saturated blowup charts

Multiplication by the original denominator gives a frame of the actual image
ideal on a saturated chart. The canonical ideal pullback along the open chart
transports this frame to the actual inverse-image-centre kernel module.
Its inclusion equation retains the original multiplication map.

No isomorphism from the full pullback of the original centre ideal along
blowdown is asserted. That map can have torsion in its kernel.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Hom Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Blowup.IdealFrames

section Image

variable {D X : Scheme.{u}} (q : D ⟶ X) [IsClosedImmersion q]

/-- The original closed immersion and its image inclusion form this actual iso square. -/
theorem imageSquare : inv q.toImage ≫ q = q.imageι ≫ 𝟙 X := by
  rw [Category.comp_id, IsIso.inv_comp_eq]
  exact q.toImage_imageι.symm

/-- The actual kernel ideal is unchanged by the canonical isomorphism onto the closed image. -/
def imageIdealIso : idealModule q ≅ idealModule q.imageι := by
  let : IsIso (idealPullbackMap q q.imageι (𝟙 X) (inv q.toImage) (imageSquare q)) :=
    idealPullbackMap_isIso_of_iso_square _ _ _ _ _
  exact ((pullbackId X).app (idealModule q)).symm ≪≫
    asIso (idealPullbackMap q q.imageι (𝟙 X) (inv q.toImage) (imageSquare q))

/-- The image comparison keeps the original inclusion into the structure module. -/
@[reassoc]
theorem imageIdealIso_hom_inclusion :
    (imageIdealIso q).hom ≫ idealInclusion q.imageι = idealInclusion q := by
  simp only [imageIdealIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]
  rw [idealPullbackMap_inclusion q q.imageι (𝟙 X) (inv q.toImage) (imageSquare q)]
  change (pullbackId X).inv.app (idealModule q) ≫
      (Scheme.Modules.pullback (𝟙 X)).map (idealInclusion q) ≫
        (pullbackUnitIso (𝟙 X)).hom = idealInclusion q
  have hn := (pullbackId X).inv.naturality (idealInclusion q)
  simp only [Functor.id_map] at hn
  rw [← reassoc_of% hn, ← pullbackUnitIso_id X, Iso.inv_hom_id_app]
  exact Category.comp_id _

end Image

section Affine

variable (S : Type u) [CommRing S] (J : Ideal S) (eJ : S ≃ₗ[S] J)

/-- Sheafification of the displayed actual ideal basis, followed by the native kernel comparison. -/
def spectralIdealFrame :
    SheafOfModules.unit (Spec (.of S)).ringCatSheaf ≅
      idealModule (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
  (tildeSelf (R := CommRingCat.of S)).symm ≪≫
    (tilde.functor (.of S)).mapIso
      (eJ.trans (LinearEquiv.ofEq _ _ (Ideal.mk_ker (I := J)).symm)).toModuleIso ≪≫
    affineIdealIso (R := .of S) (CommRingCat.ofHom (Ideal.Quotient.mk J))

/-- The spectral frame has the original ideal-basis map as its actual structure-module image. -/
@[reassoc]
theorem spectralIdealFrame_inclusion :
    (spectralIdealFrame S J eJ).hom ≫
        idealInclusion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) =
      tilde.map (ModuleCat.ofHom (J.subtype.comp eJ.toLinearMap)) := by
  let e := (eJ.trans (LinearEquiv.ofEq _ _ (Ideal.mk_ker (I := J)).symm)).toModuleIso
  have he : e.hom ≫ ModuleCat.ofHom (RingHom.ker (Ideal.Quotient.mk J)).subtype =
      ModuleCat.ofHom (J.subtype.comp eJ.toLinearMap) := by
    rfl
  simp only [spectralIdealFrame, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc]
  rw [affineIdealIso_hom_inclusion]
  change (tildeSelf (R := CommRingCat.of S)).inv ≫
      (tilde.functor (.of S)).map e.hom ≫
        (tilde.functor (.of S)).map
          (ModuleCat.ofHom (RingHom.ker (Ideal.Quotient.mk J)).subtype) = _
  rw [← Functor.map_comp, he]
  exact Category.id_comp _

/-- The same frame on the actual ideal-sheaf quotient centre, rather than an alternate model. -/
def affineCentreFrame :
    SheafOfModules.unit (Spec (.of S)).ringCatSheaf ≅
      idealModule (affineCenter S J).subschemeι := by
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact spectralIdealFrame S J eJ ≪≫ imageIdealIso q

/-- The actual quotient-centre frame keeps the original basis inclusion. -/
@[reassoc]
theorem affineCentreFrame_inclusion :
    (affineCentreFrame S J eJ).hom ≫ idealInclusion (affineCenter S J).subschemeι =
      tilde.map (ModuleCat.ofHom (J.subtype.comp eJ.toLinearMap)) := by
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  change ((spectralIdealFrame S J eJ).hom ≫ (imageIdealIso q).hom) ≫
    idealInclusion q.imageι = _
  rw [Category.assoc, imageIdealIso_hom_inclusion, spectralIdealFrame_inclusion]

end Affine

section Congruence

/-- Transport the actual affine frame together with its inclusion equation. Keeping the
equation with the frame avoids reducing a dependent kernel cast at every consumer. -/
def affineCentreFrameDataOfEq (S : Type u) [CommRing S] (J : Ideal S) (eJ : S ≃ₗ[S] J)
    (K : (Spec (.of S)).IdealSheafData) (h : K = affineCenter S J) :
    {e : SheafOfModules.unit (Spec (.of S)).ringCatSheaf ≅ idealModule K.subschemeι //
      e.hom ≫ idealInclusion K.subschemeι =
        tilde.map (ModuleCat.ofHom (J.subtype.comp eJ.toLinearMap))} := by
  subst K
  exact ⟨affineCentreFrame S J eJ, affineCentreFrame_inclusion S J eJ⟩

/-- The affine frame transported through an equality of actual centre ideals. -/
def affineCentreFrameOfEq (S : Type u) [CommRing S] (J : Ideal S) (eJ : S ≃ₗ[S] J)
    (K : (Spec (.of S)).IdealSheafData) (h : K = affineCenter S J) :
    SheafOfModules.unit (Spec (.of S)).ringCatSheaf ≅ idealModule K.subschemeι :=
  (affineCentreFrameDataOfEq S J eJ K h).val

theorem affineCentreFrameOfEq_inclusion (S : Type u) [CommRing S]
    (J : Ideal S) (eJ : S ≃ₗ[S] J) (K : (Spec (.of S)).IdealSheafData)
    (h : K = affineCenter S J) :
    (affineCentreFrameOfEq S J eJ K h).hom ≫ idealInclusion K.subschemeι =
      tilde.map (ModuleCat.ofHom (J.subtype.comp eJ.toLinearMap)) :=
  (affineCentreFrameDataOfEq S J eJ K h).property

end Congruence

section Blowup

variable {A : Type u} [CommRing A] {I : Ideal A} (B : BlowupDatum (affineCenter A I))

/-- The actual inverse-image-centre ideal of the supplied native universal blowup. -/
def centreIdeal : B.Y.IdealSheafData := (affineCenter A I).comap B.map

/-- The actual inclusion whose kernel ideal is framed below. -/
abbrev centreι : (centreIdeal B).subscheme ⟶ B.Y := (centreIdeal B).subschemeι

/-- The original saturated affine atlas map of the same universal blowup. -/
abbrev chartMap (a : I) : Spec (.of (affineBlowupAlgebra A I a)) ⟶ B.Y :=
  (affineAtlas B).chart a

/-- The literal inverse-image-centre ideal on an original saturated chart. -/
def chartCentreIdeal (a : I) := (centreIdeal B).comap (chartMap B a)

/-- The chart inverse image is the actual scalar image of the original ring ideal. -/
theorem chartCentreIdeal_eq (a : I) :
    chartCentreIdeal B a = affineCenter (affineBlowupAlgebra A I a)
      (I.map (algebraMap A (affineBlowupAlgebra A I a))) := by
  rw [chartCentreIdeal, centreIdeal, ← Scheme.IdealSheafData.comap_comp]
  rw [(affineAtlas B).triangle, affineChartMap, BaseChange.affineCenter_comap]

/-- The original map from the chart centre to the blowup centre. -/
def chartCentreMap (a : I) : (chartCentreIdeal B a).subscheme ⟶ (centreIdeal B).subscheme :=
  (chartCentreIdeal B a).subschemeMap (centreIdeal B) (chartMap B a)
    ((centreIdeal B).le_map_comap (chartMap B a))

@[reassoc]
theorem chartCentreMap_ι (a : I) :
    chartCentreMap B a ≫ centreι B = (chartCentreIdeal B a).subschemeι ≫ chartMap B a :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _

theorem chartCentre_isPullback (a : I) :
    IsPullback (chartCentreMap B a) (chartCentreIdeal B a).subschemeι
      (centreι B) (chartMap B a) :=
  (isPullback_of_isClosedImmersion (chartCentreIdeal B a).subschemeι (centreι B)
    (chartCentreMap B a) (chartMap B a) (chartCentreMap_ι B a).symm
    (by simp [centreι, chartCentreIdeal])).flip

/-- The canonical ideal comparison along the actual open chart. -/
def chartIdealPullbackMap (a : I) :
    (Scheme.Modules.pullback (chartMap B a)).obj (idealModule (centreι B)) ⟶
      idealModule (chartCentreIdeal B a).subschemeι :=
  idealPullbackMap (centreι B) (chartCentreIdeal B a).subschemeι
    (chartMap B a) (chartCentreMap B a) (chartCentreMap_ι B a)

instance chartIdealPullbackMapIsIso (a : I) : IsIso (chartIdealPullbackMap B a) := by
  let := (affineAtlas B).openImmersion a
  exact idealPullbackMap_isIso_of_isOpenImmersion _ _ _ _ _ (chartCentre_isPullback B a)

/-- The original denominator frames the actual kernel ideal pulled back to its open chart. -/
def chartFrame (a : I) :
    SheafOfModules.unit (Spec (.of (affineBlowupAlgebra A I a))).ringCatSheaf ≅
      (Scheme.Modules.pullback (chartMap B a)).obj (idealModule (centreι B)) :=
  affineCentreFrameOfEq (affineBlowupAlgebra A I a)
      (I.map (algebraMap A (affineBlowupAlgebra A I a))) (chartIdealEquiv I a)
      (chartCentreIdeal B a) (chartCentreIdeal_eq B a) ≪≫
    (asIso (chartIdealPullbackMap B a)).symm

/-- The frame's image in the actual chart structure module is multiplication by the original
denominator. Only the ideal comparison along the open chart is inverted. -/
@[reassoc]
theorem chartFrame_inclusion (a : I) :
    (chartFrame B a).hom ≫ (Scheme.Modules.pullback (chartMap B a)).map
        (idealInclusion (centreι B)) ≫
        (pullbackUnitIso (chartMap B a)).hom =
      tilde.map (ModuleCat.ofHom
        (LinearMap.mulLeft (affineBlowupAlgebra A I a)
          (algebraMap A (affineBlowupAlgebra A I a) a))) := by
  have hmap := idealPullbackMap_inclusion (centreι B) (chartCentreIdeal B a).subschemeι
    (chartMap B a) (chartCentreMap B a) (chartCentreMap_ι B a)
  change chartIdealPullbackMap B a ≫ idealInclusion (chartCentreIdeal B a).subschemeι =
    (Scheme.Modules.pullback (chartMap B a)).map (idealInclusion (centreι B)) ≫
      (pullbackUnitIso (chartMap B a)).hom at hmap
  rw [← hmap]
  simp only [chartFrame, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Category.assoc, IsIso.inv_hom_id_assoc]
  rw [affineCentreFrameOfEq_inclusion]
  have he :
      (I.map (algebraMap A (affineBlowupAlgebra A I a))).subtype.comp
          (chartIdealEquiv I a).toLinearMap =
        LinearMap.mulLeft (affineBlowupAlgebra A I a)
          (algebraMap A (affineBlowupAlgebra A I a) a) := by
    rfl
  rw [he]

end Blowup

end AlgebraicGeometry.Scheme.Blowup.IdealFrames

namespace AlgebraicGeometry.Scheme.Blowup.IdealFrames

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Hom Scheme.Modules

/-- Original multiplication on an affine structure module. -/
def affineMultiplication (S : Type u) [CommRing S] (s : S) :
    (show (Spec (.of S)).Modules from SheafOfModules.unit (Spec (.of S)).ringCatSheaf) ⟶
      (show (Spec (.of S)).Modules from SheafOfModules.unit (Spec (.of S)).ringCatSheaf) :=
  tilde.map (ModuleCat.ofHom (LinearMap.mulLeft S s))

@[reassoc]
theorem affineMultiplication_comp (S : Type u) [CommRing S] (s t : S) :
    affineMultiplication S s ≫ affineMultiplication S t = affineMultiplication S (s * t) := by
  rw [affineMultiplication, affineMultiplication, affineMultiplication, ← tilde.map_comp]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change t * (s * x) = (s * t) * x
  ac_rfl

open Opposite

private theorem unitMul_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Γ(Y, ⊤)) :
    (Scheme.Modules.pullback f).map (unitMul Y s) ≫ (pullbackUnitIso f).hom =
      (pullbackUnitIso f).hom ≫ unitMul X (f.appTop s) := by
  apply ((pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    pullbackUnitIso_homEquiv]
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change Γ(Y, U) at x
  change f.app U (x * Y.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s) =
    f.app U x * X.presheaf.map (homOfLE le_top : f ⁻¹ᵁ U ⟶ ⊤).op (f.appTop s)
  rw [map_mul]
  congr 1
  exact ConcreteCategory.congr_hom
    (f.toLRSHom.c.naturality (homOfLE (show U ≤ ⊤ from le_top)).op) s

private theorem tildeUnit_toOpen_top (S : Type u) [CommRing S] (s : S) :
    tilde.toOpen (R := .of S) (ModuleCat.of S S) ⊤ s =
      (Scheme.ΓSpecIso (.of S)).inv s := rfl

private theorem affineMultiplication_top_one (S : Type u) [CommRing S] (s : S) :
    (affineMultiplication S s).val.app (op ⊤) (1 : Γ(Spec (.of S), ⊤)) =
      (Scheme.ΓSpecIso (.of S)).inv s := by
  have h := ConcreteCategory.congr_hom
    (tilde.toOpen_map_app (R := .of S) (M := ModuleCat.of S S)
      (N := ModuleCat.of S S) (ModuleCat.ofHom (LinearMap.mulLeft S s)) ⊤) (1 : S)
  change (affineMultiplication S s).val.app (op ⊤)
      (tilde.toOpen (R := .of S) (ModuleCat.of S S) ⊤ (1 : S)) =
    tilde.toOpen (R := .of S) (ModuleCat.of S S) ⊤ (s * 1) at h
  rw [mul_one] at h
  have h1 : tilde.toOpen (R := .of S) (ModuleCat.of S S) ⊤ (1 : S) =
      (1 : Γ(Spec (.of S), ⊤)) :=
    (tildeUnit_toOpen_top S 1).trans (map_one (Scheme.ΓSpecIso (.of S)).inv.hom)
  exact (congrArg
    (fun x : Γ(Spec (.of S), ⊤) => (affineMultiplication S s).val.app (op ⊤) x)
      h1.symm).trans (h.trans (tildeUnit_toOpen_top S s))

/-- The original affine scalar map is multiplication by its original structure-sheaf section. -/
theorem affineMultiplication_eq_unitMul (S : Type u) [CommRing S] (s : S) :
    affineMultiplication S s = unitMul (Spec (.of S)) ((Scheme.ΓSpecIso (.of S)).inv s) := by
  apply (unitHomGlobalSectionsEquiv (Spec (.of S))
    (SheafOfModules.unit (Spec (.of S)).ringCatSheaf)).injective
  change (affineMultiplication S s).val.app (op ⊤) (1 : Γ(Spec (.of S), ⊤)) = _
  rw [affineMultiplication_top_one]
  change (Scheme.ΓSpecIso (.of S)).inv s =
    1 * (Spec (.of S)).presheaf.map (𝟙 (op (⊤ : (Spec (.of S)).Opens)))
      ((Scheme.ΓSpecIso (.of S)).inv s)
  rw [CategoryTheory.Functor.map_id]
  exact (one_mul _).symm

/-- Native affine pullback carries the original multiplication map to its image coefficient. -/
theorem affineMultiplication_pullback {S T : Type u} [CommRing S] [CommRing T]
    (φ : S →+* T) (s : S) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).map
        (affineMultiplication S s) ≫ (pullbackUnitIso (Spec.map (CommRingCat.ofHom φ))).hom =
      (pullbackUnitIso (Spec.map (CommRingCat.ofHom φ))).hom ≫
        affineMultiplication T (φ s) := by
  have hc : (Spec.map (CommRingCat.ofHom φ)).appTop ((Scheme.ΓSpecIso (.of S)).inv s) =
      (Scheme.ΓSpecIso (.of T)).inv (φ s) :=
    congrArg (fun q : CommRingCat.of S ⟶ Γ(Spec (.of T), ⊤) => q s)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm
  simp only [affineMultiplication_eq_unitMul]
  rw [unitMul_pullback, hc]

/-- Original inclusion equations determine the scalar transition of two frames over an
equal pair of maps, whenever the pulled inclusion is monic. -/
theorem frame_transition {X : Scheme.{u}} (T : Type u) [CommRing T]
    (M : X.Modules) (ι : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (j k : Spec (.of T) ⟶ X) (h : j = k)
    [Mono ((Scheme.Modules.pullback j).map ι)]
    (e : SheafOfModules.unit (Spec (.of T)).ringCatSheaf ≅ (Scheme.Modules.pullback j).obj M)
    (d : SheafOfModules.unit (Spec (.of T)).ringCatSheaf ≅ (Scheme.Modules.pullback k).obj M)
    (s t r : T)
    (he : e.hom ≫ (Scheme.Modules.pullback j).map ι ≫ (pullbackUnitIso j).hom =
      affineMultiplication T s)
    (hd : d.hom ≫ (Scheme.Modules.pullback k).map ι ≫ (pullbackUnitIso k).hom =
      affineMultiplication T t)
    (hr : t = r * s) :
    d.hom ≫ (pullbackCongr h.symm).hom.app M = affineMultiplication T r ≫ e.hom := by
  apply (cancel_mono ((Scheme.Modules.pullback j).map ι)).mp
  apply (cancel_mono (pullbackUnitIso j).hom).mp
  have hn := (pullbackCongr h.symm).hom.naturality ι
  simp only [Category.assoc]
  rw [← reassoc_of% hn, pullbackUnitIso_congr, hd, he, affineMultiplication_comp, hr]

variable {A : Type u} [CommRing A] {I : Ideal A}
  (B : BlowupDatum (affineCenter A I))

/-- The actual chart frame pulled through a displayed affine chart-ring map. -/
def chartFrameAfterMap (a : I) (T : Type u) [CommRing T]
    (φ : affineBlowupAlgebra A I a →+* T) :
    SheafOfModules.unit (Spec (.of T)).ringCatSheaf ≅
      (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ) ≫ chartMap B a)).obj
        (idealModule (centreι B)) :=
  (pullbackUnitIso (Spec.map (CommRingCat.ofHom φ))).symm ≪≫
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).mapIso (chartFrame B a) ≪≫
    (pullbackComp _ _).app (idealModule (centreι B))

/-- The pulled frame retains original denominator multiplication, including after reduction. -/
@[reassoc]
theorem chartFrameAfterMap_inclusion (a : I) (T : Type u) [CommRing T]
    (φ : affineBlowupAlgebra A I a →+* T) :
    (chartFrameAfterMap B a T φ).hom ≫
        (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ) ≫ chartMap B a)).map
          (idealInclusion (centreι B)) ≫
        (pullbackUnitIso (Spec.map (CommRingCat.ofHom φ) ≫ chartMap B a)).hom =
      affineMultiplication T (φ (algebraMap A (affineBlowupAlgebra A I a) a)) := by
  let f := Spec.map (CommRingCat.ofHom φ)
  let j := chartMap B a
  have hn := (pullbackComp f j).hom.naturality (idealInclusion (centreι B))
  simp only [CategoryTheory.Functor.comp_map] at hn
  simp only [chartFrameAfterMap, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rw [← reassoc_of% hn, pullbackUnitIso_comp]
  rw [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc]
  have hf : ((chartFrame B a).hom ≫ (Scheme.Modules.pullback j).map
      (idealInclusion (centreι B))) ≫ (pullbackUnitIso j).hom =
      affineMultiplication (affineBlowupAlgebra A I a)
        (algebraMap A (affineBlowupAlgebra A I a) a) :=
    (Category.assoc _ _ _).trans (chartFrame_inclusion B a)
  rw [hf]
  change (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map
      (affineMultiplication (affineBlowupAlgebra A I a)
        (algebraMap A (affineBlowupAlgebra A I a) a)) ≫ (pullbackUnitIso f).hom = _
  rw [affineMultiplication_pullback, Iso.inv_hom_id_assoc]

/-- Pullback along an actual open immersion preserves the actual ideal inclusion. -/
theorem idealInclusion_pullback_mono {Z : Scheme.{u}} (j : Z ⟶ B.Y) [IsOpenImmersion j] :
    Mono ((Scheme.Modules.pullback j).map (idealInclusion (centreι B))) := by
  have : (Scheme.Modules.pullback j).PreservesMonomorphisms :=
    CategoryTheory.Functor.PreservesMonomorphisms.of_iso (restrictFunctorIsoPullback j)
  infer_instance

/-- The two original parameter frames have the original scalar transition on an actual
open overlap. The monomorphism is used before the closed-fibre specialization. -/
theorem chartFrameAfterMap_transition (a b : I) (T : Type u) [CommRing T]
    (φ : affineBlowupAlgebra A I a →+* T) (ψ : affineBlowupAlgebra A I b →+* T)
    (h : Spec.map (CommRingCat.ofHom φ) ≫ chartMap B a =
      Spec.map (CommRingCat.ofHom ψ) ≫ chartMap B b)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ) ≫ chartMap B a)]
    (r : T)
    (hr : ψ (algebraMap A (affineBlowupAlgebra A I b) b) =
      r * φ (algebraMap A (affineBlowupAlgebra A I a) a)) :
    (chartFrameAfterMap B b T ψ).hom ≫
        (pullbackCongr h.symm).hom.app (idealModule (centreι B)) =
      affineMultiplication T r ≫ (chartFrameAfterMap B a T φ).hom := by
  have := idealInclusion_pullback_mono B (Spec.map (CommRingCat.ofHom φ) ≫ chartMap B a)
  exact frame_transition T (idealModule (centreι B)) (idealInclusion (centreι B))
    _ _ h (chartFrameAfterMap B a T φ) (chartFrameAfterMap B b T ψ)
    _ _ r (chartFrameAfterMap_inclusion B a T φ) (chartFrameAfterMap_inclusion B b T ψ) hr

end AlgebraicGeometry.Scheme.Blowup.IdealFrames
