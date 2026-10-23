/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveBundle.RankTwoExtension.Conormal
public import Aglib.AlgebraicGeometry.IdealSheaf.Modules.ConormalMap
public import Aglib.AlgebraicGeometry.Modules.InternalHom.Refinement
public import Aglib.AlgebraicGeometry.Descent.Modules.RestrictPullback
public import Aglib.AlgebraicGeometry.Modules.Restriction.Unit
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit

/-!
# Compatibility of the original quotient conormal frames

Restriction compatibility is checked on the original affine frames refining
both opens. The comparisons below retain the native restriction composition
and equality isomorphisms.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Scheme.Modules Scheme.Modules.Differentials Scheme.Hom Scheme.ProjectiveLine
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveBundle.RankTwoExtension

variable {X : Scheme.{u}} {E : X.Modules}
variable (g : E ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))

/-- The native comparison from an original frame restriction to its iterated restriction. -/
def frameRestrictionIso (M : X.Modules) {a b : AffineFrame g} (h : a ≤ b) :
    M.restrict a.U.1.ι ≅ (M.restrict b.U.1.ι).restrict (X.homOfLE (show a.U.1 ≤ b.U.1 from h)) :=
  (restrictFunctorCongr (X.homOfLE_ι (show a.U.1 ≤ b.U.1 from h)).symm).app M ≪≫
    (restrictFunctorComp (X.homOfLE (show a.U.1 ≤ b.U.1 from h)) b.U.1.ι).app M

/-- A whole-arrow refinement square identifies the literal original Hom sections. -/
theorem frameHomSection_restrict (M N : X.Modules)
    (f : ∀ a : AffineFrame g, M.restrict a.U.1.ι ⟶ N.restrict a.U.1.ι)
    {a b : AffineFrame g} (h : a ≤ b)
    (hf : (frameRestrictionIso g M h).hom ≫
      (Scheme.Modules.restrictFunctor
        (X.homOfLE (show a.U.1 ≤ b.U.1 from h))).map (f b) =
      f a ≫ (frameRestrictionIso g N h).hom) :
    (InternalHom.sheaf X M N).val.presheaf.map
        (homOfLE (show a.U.1.ι.opensRange ≤ b.U.1.ι.opensRange from by
          simpa only [Scheme.Opens.opensRange_ι] using (show a.U.1 ≤ b.U.1 from h))).op
          (InternalHom.restrictionHomEquiv b.U.1.ι M N (f b)) =
      InternalHom.restrictionHomEquiv a.U.1.ι M N (f a) := by
  exact canonicalRestrictionHomEquiv_refinement b.U.1.ι a.U.1.ι
    (X.homOfLE (show a.U.1 ≤ b.U.1 from h))
      (X.homOfLE_ι (show a.U.1 ≤ b.U.1 from h)).symm M N (f b) (f a) hf

/-- Native refinement compatibility on the original affine frames implies compatibility
on each actual pullback overlap. -/
theorem frameHomCompatible_of_refinement [Epi g] (M N : X.Modules)
    (f : ∀ a : AffineFrame g, M.restrict a.U.1.ι ⟶ N.restrict a.U.1.ι)
    (hf : ∀ {a b : AffineFrame g} (h : a ≤ b),
      (frameRestrictionIso g M h).hom ≫
        (Scheme.Modules.restrictFunctor
          (X.homOfLE (show a.U.1 ≤ b.U.1 from h))).map (f b) =
        f a ≫ (frameRestrictionIso g N h).hom) :
    InternalHom.RestrictionHomCompatible (fun a : AffineFrame g => a.U.1.ι) M N f := by
  apply canonicalRestrictionHomCompatible_of_sections
    (fun a : AffineFrame g => a.U.1.toScheme) (fun a => a.U.1.ι)
  intro a b
  let H := InternalHom.sheaf X M N
  change H.val.presheaf.map (homOfLE inf_le_left).op
      (InternalHom.restrictionHomEquiv a.U.1.ι M N (f a)) =
    H.val.presheaf.map (homOfLE inf_le_right).op
      (InternalHom.restrictionHomEquiv b.U.1.ι M N (f b))
  have hcover : a.U.1.ι.opensRange ⊓ b.U.1.ι.opensRange ≤
      ⨆ c : FrameOn g (a.U.1 ⊓ b.U.1), c.val.U.1.ι.opensRange := by
    simp only [Scheme.Opens.opensRange_ι]
    intro x hx
    obtain ⟨c, hxc, hc⟩ := exists_frame_le g (a.U.1 ⊓ b.U.1) x hx
    exact Opens.mem_iSup.mpr ⟨⟨c, hc⟩, hxc⟩
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨H.val.presheaf, H.isSheaf⟩
    (fun c : FrameOn g (a.U.1 ⊓ b.U.1) => c.val.U.1.ι.opensRange) _
    (fun c => homOfLE (by simpa only [Scheme.Opens.opensRange_ι] using c.property)) hcover
  intro c
  have hca : c.val ≤ a := c.property.trans inf_le_left
  have hcb : c.val ≤ b := c.property.trans inf_le_right
  simp only [← Functor.map_comp_apply, ← op_comp]
  exact (frameHomSection_restrict g M N f hca (hf hca)).trans
    (frameHomSection_restrict g M N f hcb (hf hcb)).symm

variable (i : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ E)
  (hig : i ≫ g = 0) (hS : (extensionComplex i g hig).ShortExact)

/-- The precise refinement equation for the actual conormal frames. -/
def QuotientConormalFramesRefine
    (g : E ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (i : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ E)
    (hig : i ≫ g = 0) (hS : (extensionComplex i g hig).ShortExact) : Prop :=
  ∀ {a b : AffineFrame g} (h : a ≤ b),
    (frameRestrictionIso g
      ((Modules.pullback (quotientSection i g hig hS)).obj
        (idealModule (quotientSection i g hig hS))) h).hom ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE (show a.U.1 ≤ b.U.1 from h))).map
        (quotientConormalRestrictionIso i g hig hS b).hom =
    (quotientConormalRestrictionIso i g hig hS a).hom ≫
      (frameRestrictionIso g (SheafOfModules.unit X.ringCatSheaf) h).hom

/-- The actual frame-refinement equation gives the required native pullback-overlap equation. -/
theorem quotientConormalFramesCompatible_of_refine
    (href : QuotientConormalFramesRefine g i hig hS) :
    QuotientConormalFramesCompatible i g hig hS := by
  let : Epi g := hS.epi_g
  exact frameHomCompatible_of_refinement g _ _
    (fun a => (quotientConormalRestrictionIso i g hig hS a).hom) href

namespace Conormal

private theorem conormalMap_ambient_congr {D Y Z : Scheme.{u}}
    (s : D ⟶ Y) (s' : D ⟶ Z) {b b' : Z ⟶ Y} (hb : b = b')
    (h : s = s' ≫ b) (h' : s = s' ≫ b') :
    Scheme.Hom.conormalMap s s' b h = Scheme.Hom.conormalMap s s' b' h' := by
  cases hb
  rfl

private theorem conormalSquareMap_ambient_congr {D D' Y Z : Scheme.{u}}
    (s : D ⟶ Y) (s' : D' ⟶ Z) (a : D' ⟶ D) {b b' : Z ⟶ Y} (hb : b = b')
    (h : a ≫ s = s' ≫ b) (h' : a ≫ s = s' ≫ b') :
    conormalSquareMap s s' b a h = conormalSquareMap s s' b' a h' := by
  cases hb
  rfl

variable (R : Type u) [CommRing R]

/-- The actual unipotent projective-line automorphism acts trivially on the conormal
of its original infinity section. -/
theorem infinityConormal_translation (t : R) :
    Scheme.Hom.conormalMap (Sections.infinity R) (Sections.infinity R)
        (LinearChange.matrixMap R (Sections.translationMatrix R t))
        (Sections.infinity_translation R t).symm = 𝟙 _ := by
  let s := Sections.infinity R
  let z := coordinateSection R
  let w := overlapZeroSection R t
  let c := chart R 1
  let q := Spec.map (CommRingCat.ofHom (algebraMap R[X] (overlapRing R t)))
  let q' := Spec.map (CommRingCat.ofHom (Sections.translationOverlapMap R t))
  let T := LinearChange.matrixMap R (Sections.translationMatrix R t)
  have hT : s = s ≫ T := (Sections.infinity_translation R t).symm
  have hsz : s = z ≫ c := rfl
  have hzq : z = w ≫ q := (overlapZeroSection_chart R t).symm
  have hzq' : z = w ≫ q' := (overlapZeroSection_changedChart R t).symm
  have hsw : s = w ≫ (q ≫ c) := by rw [hsz, hzq, Category.assoc]
  have hqT : (q ≫ c) ≫ T = q' ≫ c :=
    (Category.assoc q c T).trans (Sections.chart_one_translation_overlap R t)
  let k := Scheme.Hom.conormalMap s w (q ≫ c) hsw
  let : IsIso k := conormalMap_isIso_of_isOpenImmersion s w (q ≫ c) hsw
  change Scheme.Hom.conormalMap s s T hT = 𝟙 _
  apply (cancel_mono k).1
  rw [Category.id_comp]
  change Scheme.Hom.conormalMap s s T hT ≫ Scheme.Hom.conormalMap s w (q ≫ c) hsw =
    Scheme.Hom.conormalMap s w (q ≫ c) hsw
  have htotal : s = w ≫ ((q ≫ c) ≫ T) := by
    calc
      s = s ≫ T := hT
      _ = (w ≫ (q ≫ c)) ≫ T := congrArg (fun k => k ≫ T) hsw
      _ = _ := Category.assoc _ _ _
  have hchanged : s = w ≫ (q' ≫ c) := by rw [hsz, hzq', Category.assoc]
  rw [conormalMap_comp]
  refine (conormalMap_ambient_congr s w hqT htotal hchanged).trans ?_
  rw [← conormalMap_comp s z w c q' hsz hzq',
    ← conormalMap_comp s z w c q hsz hzq]
  exact congrArg (fun f => Scheme.Hom.conormalMap s z c hsz ≫ f) (overlapConormalMaps_equal R t)

end Conormal

namespace Conormal

private theorem pullbackComp_hom_unit_top {D X Y : Scheme.{u}}
    (f : D ⟶ X) (g : X ⟶ Y) (M : Y.Modules) (m : Γ(M, ⊤)) :
    ((pullbackComp f g).hom.app M).val.app (op ⊤)
        (((pullbackPushforwardAdjunction f).unit.app ((Modules.pullback g).obj M)).val.app
          (op ⊤) (((pullbackPushforwardAdjunction g).unit.app M).val.app (op ⊤) m)) =
      ((pullbackPushforwardAdjunction (f ≫ g)).unit.app M).val.app (op ⊤) m := by
  rw [← Diagonal.pullbackComp_inv_unit_top]
  exact congrArg (fun q => q.val.app (op ⊤)
    (((pullbackPushforwardAdjunction (f ≫ g)).unit.app M).val.app (op ⊤) m))
      ((pullbackComp f g).inv_hom_id_app M)

/-- The actual square map carries an original ideal section to its original pulled-back class. -/
theorem conormalSquareMap_unit_top {D D' X Y : Scheme.{u}}
    (i : D ⟶ X) (i' : D' ⟶ Y) (b : Y ⟶ X) (a : D' ⟶ D)
    (h : a ≫ i = i' ≫ b) (m : Γ(idealModule i, ⊤)) :
    (conormalSquareMap i i' b a h).val.app (op ⊤)
      (((pullbackPushforwardAdjunction a).unit.app
        ((Modules.pullback i).obj (idealModule i))).val.app (op ⊤) (conormalElement i m)) =
      conormalElement i' ((idealPushforwardMap i i' b a h).val.app (op ⊤) m) := by
  dsimp only [conormalSquareMap, conormalElement]
  change ((Modules.pullback i').map (idealPullbackMap i i' b a h)).val.app (op ⊤)
    (((pullbackComp i' b).inv.app (idealModule i)).val.app (op ⊤)
      (((pullbackCongr h).hom.app (idealModule i)).val.app (op ⊤)
        (((pullbackComp a i).hom.app (idealModule i)).val.app (op ⊤)
          (((pullbackPushforwardAdjunction a).unit.app
            ((Modules.pullback i).obj (idealModule i))).val.app (op ⊤)
              (((pullbackPushforwardAdjunction i).unit.app (idealModule i)).val.app
                (op ⊤) m))))) = _
  rw [pullbackComp_hom_unit_top, Diagonal.pullbackCongr_unit_top,
    Diagonal.pullbackComp_inv_unit_top, Diagonal.pullback_map_unit_top,
    Diagonal.idealPullbackMap_unit_top]

private theorem pullbackUnitIso_unit_top {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : Γ(Y, ⊤)) :
    (pullbackUnitIso f).hom.val.app (op ⊤)
      (((pullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.unit Y.ringCatSheaf)).val.app (op ⊤) r) = f.appTop r := by
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun q => q.val.app (op ⊤) r) h

private theorem pullbackFrame_generator {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules} (e : M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (m : Γ(M, ⊤)) (he : e.hom.val.app (op ⊤) m = (1 : Γ(Y, ⊤))) :
    ((Modules.pullback f).mapIso e ≪≫ pullbackUnitIso f).hom.val.app (op ⊤)
      (((pullbackPushforwardAdjunction f).unit.app M).val.app (op ⊤) m) =
        (1 : Γ(X, ⊤)) := by
  change (pullbackUnitIso f).hom.val.app (op ⊤)
    (((Modules.pullback f).map e.hom).val.app (op ⊤)
      (((pullbackPushforwardAdjunction f).unit.app M).val.app (op ⊤) m)) = _
  rw [Diagonal.pullback_map_unit_top, he, pullbackUnitIso_unit_top, map_one]

/-- The actual conormal-map/frame equation, with its module objects retained explicitly. -/
def FrameMapCompatible {D D' : Scheme.{u}} {M : D.Modules} {N : D'.Modules}
    (a : D' ⟶ D) (e : M ≅ SheafOfModules.unit D.ringCatSheaf)
    (e' : N ≅ SheafOfModules.unit D'.ringCatSheaf)
    (q : (Modules.pullback a).obj M ⟶ N) : Prop :=
  q ≫ e'.hom = (Modules.pullback a).map e.hom ≫ (pullbackUnitIso a).hom

private def FrameGenerator {D : Scheme.{u}} {M : D.Modules}
    (e : M ≅ SheafOfModules.unit D.ringCatSheaf) (m : M.val.obj (op ⊤)) : Prop :=
  e.hom.val.app (op ⊤) m = (1 : Γ(D, ⊤))

private def IdealSectionImage {D D' Y Z : Scheme.{u}}
    (s : D ⟶ Y) (s' : D' ⟶ Z) (b : Z ⟶ Y) (a : D' ⟶ D)
    (h : a ≫ s = s' ≫ b) (m : (idealModule s).val.obj (op ⊤))
    (n : (idealModule s').val.obj (op ⊤)) : Prop :=
  (idealPushforwardMap s s' b a h).val.app (op ⊤) m = n

private theorem affineIdealElement_image {A B C D : CommRingCat.{u}}
    (σ : A ⟶ B) (τ : C ⟶ D) (b : A ⟶ C) (a : Spec D ⟶ Spec B)
    (h : a ≫ Spec.map σ = Spec.map τ ≫ Spec.map b)
    (x : RingHom.ker σ.hom) (y : RingHom.ker τ.hom) (hy : y.val = b x.val) :
    IdealSectionImage (Spec.map σ) (Spec.map τ) (Spec.map b) a h
      (affineIdealElement σ x) (affineIdealElement τ y) :=
  affineIdealElement_map σ τ b a h x y hy

private theorem frameMapCompatible_of_ideal_generators {D D' Y Z : Scheme.{u}}
    (s : D ⟶ Y) (s' : D' ⟶ Z) (b : Z ⟶ Y) (a : D' ⟶ D)
    (h : a ≫ s = s' ≫ b)
    (e : (Modules.pullback s).obj (idealModule s) ≅ SheafOfModules.unit D.ringCatSheaf)
    (e' : (Modules.pullback s').obj (idealModule s') ≅ SheafOfModules.unit D'.ringCatSheaf)
    (m : (idealModule s).val.obj (op ⊤)) (n : (idealModule s').val.obj (op ⊤))
    (he : FrameGenerator e (conormalElement s m))
    (he' : FrameGenerator e' (conormalElement s' n))
    (hm : IdealSectionImage s s' b a h m n) :
    FrameMapCompatible a e e' (conormalSquareMap s s' b a h) := by
  let ep := (Modules.pullback a).mapIso e ≪≫ pullbackUnitIso a
  let v := ((pullbackPushforwardAdjunction a).unit.app
    ((Modules.pullback s).obj (idealModule s))).val.app (op ⊤) (conormalElement s m)
  have hv : ep.hom.val.app (op ⊤) v = (1 : Γ(D', ⊤)) :=
    pullbackFrame_generator a e (conormalElement s m) he
  unfold FrameMapCompatible
  apply hom_ext_of_globalUnitFrame ep v hv
  change e'.hom.val.app (op ⊤)
    ((conormalSquareMap s s' b a h).val.app (op ⊤) v) = ep.hom.val.app (op ⊤) v
  dsimp only [v]
  rw [conormalSquareMap_unit_top]
  change (idealPushforwardMap s s' b a h).val.app (op ⊤) m = n at hm
  rw [hm]
  exact (show e'.hom.val.app (op ⊤) (conormalElement s' n) = (1 : Γ(D', ⊤)) from he').trans hv.symm

private theorem coordinateFrame_generator (R : Type u) [CommRing R] :
    FrameGenerator (coordinateConormalIso R)
      (affineConormalElement (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
        ⟨Polynomial.X, by simp⟩) := coordinateConormalIso_generator R

private theorem frameMapCompatible_of_charts
    {D D' Y Y' Z Z' : Scheme.{u}}
    (s : D ⟶ Y) (s' : D' ⟶ Y') (z : D ⟶ Z) (z' : D' ⟶ Z')
    (c : Z ⟶ Y) (c' : Z' ⟶ Y') (hs : s = z ≫ c) (hs' : s' = z' ≫ c')
    (a : D' ⟶ D) (b : Y' ⟶ Y) (d : Z' ⟶ Z)
    (hb : a ≫ s = s' ≫ b) (hd : a ≫ z = z' ≫ d) (hc : c' ≫ b = d ≫ c)
    (e : (Modules.pullback s).obj (idealModule s) ≅ SheafOfModules.unit D.ringCatSheaf)
    (e' : (Modules.pullback s').obj (idealModule s') ≅ SheafOfModules.unit D'.ringCatSheaf)
    (f : (Modules.pullback z).obj (idealModule z) ≅ SheafOfModules.unit D.ringCatSheaf)
    (f' : (Modules.pullback z').obj (idealModule z') ≅ SheafOfModules.unit D'.ringCatSheaf)
    (he : e.hom = Scheme.Hom.conormalMap s z c hs ≫ f.hom)
    (he' : e'.hom = Scheme.Hom.conormalMap s' z' c' hs' ≫ f'.hom)
    (hf : FrameMapCompatible a f f' (conormalSquareMap z z' d a hd)) :
    FrameMapCompatible a e e' (conormalSquareMap s s' b a hb) := by
  have hL : a ≫ s = z' ≫ (c' ≫ b) := by rw [hb, hs', Category.assoc]
  have hR : a ≫ s = z' ≫ (d ≫ c) := by rw [hs, ← Category.assoc, hd, Category.assoc]
  have hmap : conormalSquareMap s s' b a hb ≫ Scheme.Hom.conormalMap s' z' c' hs' =
      (Modules.pullback a).map (Scheme.Hom.conormalMap s z c hs) ≫
        conormalSquareMap z z' d a hd := by
    rw [conormalSquareMap_comp_ambient, conormalMap_comp_square]
    exact conormalSquareMap_ambient_congr s z' a hc hL hR
  unfold FrameMapCompatible at hf ⊢
  rw [he, he', Functor.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc, hmap]
  simp only [Category.assoc]
  rw [hf]

private theorem frameMapCompatible_comp_ambient {D D' Y Y' : Scheme.{u}}
    (s : D ⟶ Y) (s' : D' ⟶ Y') (a : D' ⟶ D) (b : Y' ⟶ Y)
    (h : a ≫ s = s' ≫ b) (T : Y' ⟶ Y') (hT : s' = s' ≫ T)
    (e : (Modules.pullback s).obj (idealModule s) ≅ SheafOfModules.unit D.ringCatSheaf)
    (e' : (Modules.pullback s').obj (idealModule s') ≅ SheafOfModules.unit D'.ringCatSheaf)
    (hmap : Scheme.Hom.conormalMap s' s' T hT = 𝟙 _)
    (hf : FrameMapCompatible a e e' (conormalSquareMap s s' b a h)) :
    FrameMapCompatible a e e'
      (conormalSquareMap s s' (T ≫ b) a
        ((h.trans (congrArg (fun q => q ≫ b) hT)).trans (Category.assoc s' T b))) := by
  unfold FrameMapCompatible at hf ⊢
  rw [← conormalSquareMap_comp_ambient s s' s' a b T h hT, hmap, Category.comp_id]
  exact hf

/-- Pullback-frame refinement using the original base triangle and native comparisons. -/
def PullbackFrameRefinement {X U V : Scheme.{u}}
    (r : U ⟶ V) (u : U ⟶ X) (v : V ⟶ X) (hr : r ≫ v = u) (M : X.Modules)
    (eU : (Modules.pullback u).obj M ≅ SheafOfModules.unit U.ringCatSheaf)
    (eV : (Modules.pullback v).obj M ≅ SheafOfModules.unit V.ringCatSheaf) : Prop :=
  (Modules.pullback r).map eV.hom ≫ (pullbackUnitIso r).hom =
    (pullbackComp r v).hom.app M ≫ (pullbackCongr hr).hom.app M ≫ eU.hom

private theorem frameRefinement_of_conormal_squares
    {D₀ D₁ D₂ Y₀ Y₁ Y₂ : Scheme.{u}}
    (s₀ : D₀ ⟶ Y₀) (s₁ : D₁ ⟶ Y₁) (s₂ : D₂ ⟶ Y₂)
    (a₁ : D₁ ⟶ D₀) (a₂ : D₂ ⟶ D₁) (a₀ : D₂ ⟶ D₀)
    (b₁ : Y₁ ⟶ Y₀) (b₂ : Y₂ ⟶ Y₁) (b₀ : Y₂ ⟶ Y₀)
    (h₁ : a₁ ≫ s₀ = s₁ ≫ b₁) (h₂ : a₂ ≫ s₁ = s₂ ≫ b₂)
    (h₀ : a₀ ≫ s₀ = s₂ ≫ b₀) (ha : a₂ ≫ a₁ = a₀) (hb : b₂ ≫ b₁ = b₀)
    (l₁ : (Modules.pullback s₁).obj (idealModule s₁) ≅ SheafOfModules.unit D₁.ringCatSheaf)
    (l₂ : (Modules.pullback s₂).obj (idealModule s₂) ≅ SheafOfModules.unit D₂.ringCatSheaf)
    (e₁ : (Modules.pullback a₁).obj ((Modules.pullback s₀).obj (idealModule s₀)) ≅
      SheafOfModules.unit D₁.ringCatSheaf)
    (e₀ : (Modules.pullback a₀).obj ((Modules.pullback s₀).obj (idealModule s₀)) ≅
      SheafOfModules.unit D₂.ringCatSheaf)
    (he₁ : e₁.hom = conormalSquareMap s₀ s₁ b₁ a₁ h₁ ≫ l₁.hom)
    (he₀ : e₀.hom = conormalSquareMap s₀ s₂ b₀ a₀ h₀ ≫ l₂.hom)
    (hl : FrameMapCompatible a₂ l₁ l₂ (conormalSquareMap s₁ s₂ b₂ a₂ h₂)) :
    PullbackFrameRefinement a₂ a₀ a₁ ha
      ((Modules.pullback s₀).obj (idealModule s₀)) e₀ e₁ := by
  have ht : (a₂ ≫ a₁) ≫ s₀ = s₂ ≫ (b₂ ≫ b₁) := by
    rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc]
  have ht' : (a₂ ≫ a₁) ≫ s₀ = s₂ ≫ b₀ := by rw [ha, h₀]
  have H : (Modules.pullback a₂).map (conormalSquareMap s₀ s₁ b₁ a₁ h₁) ≫
      conormalSquareMap s₁ s₂ b₂ a₂ h₂ =
      (pullbackComp a₂ a₁).hom.app ((Modules.pullback s₀).obj (idealModule s₀)) ≫
        (pullbackCongr ha).hom.app ((Modules.pullback s₀).obj (idealModule s₀)) ≫
          conormalSquareMap s₀ s₂ b₀ a₀ h₀ :=
    (conormalSquareMap_comp s₀ s₁ s₂ a₁ a₂ b₁ b₂ h₁ h₂).trans
      (congrArg (fun q => (pullbackComp a₂ a₁).hom.app
        ((Modules.pullback s₀).obj (idealModule s₀)) ≫ q)
        ((conormalSquareMap_ambient_congr s₀ s₂ (a₂ ≫ a₁) hb ht ht').trans
          (conormalSquareMap_source_congr s₀ s₂ b₀ ha ht' h₀).symm))
  unfold FrameMapCompatible at hl
  unfold PullbackFrameRefinement
  rw [he₁, he₀, Functor.map_comp]
  simp only [Category.assoc]
  rw [← hl, reassoc_of% H]

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The original zero sections retain the literal polynomial coefficient square. -/
theorem coordinateSection_coefficient (f : R →+* S) :
    Spec.map (CommRingCat.ofHom f) ≫ coordinateSection R =
      coordinateSection S ≫ Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) := by
  simp only [coordinateSection, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    simp
  · simp

/-- The actual coordinate conormal frame is natural under every coefficient homomorphism. -/
theorem coordinateConormal_coefficient (f : R →+* S) :
    FrameMapCompatible (Spec.map (CommRingCat.ofHom f))
      (coordinateConormalIso R) (coordinateConormalIso S)
      (conormalSquareMap (coordinateSection R) (coordinateSection S)
        (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)))
        (Spec.map (CommRingCat.ofHom f)) (coordinateSection_coefficient f)) := by
  exact frameMapCompatible_of_ideal_generators (coordinateSection R) (coordinateSection S)
    (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)))
    (Spec.map (CommRingCat.ofHom f)) (coordinateSection_coefficient f)
    (coordinateConormalIso R) (coordinateConormalIso S)
    (affineIdealElement (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
      ⟨Polynomial.X, by simp⟩)
    (affineIdealElement (CommRingCat.ofHom (Polynomial.evalRingHom (0 : S)))
      ⟨Polynomial.X, by simp⟩)
    (coordinateFrame_generator R) (coordinateFrame_generator S)
    (affineIdealElement_image
      (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
      (CommRingCat.ofHom (Polynomial.evalRingHom (0 : S)))
      (CommRingCat.ofHom (Polynomial.mapRingHom f)) (Spec.map (CommRingCat.ofHom f))
      (coordinateSection_coefficient f) ⟨Polynomial.X, by simp⟩ ⟨Polynomial.X, by simp⟩
      (by simp))

end Conormal

namespace Conormal

variable {R S : Type u} [CommRing R] [CommRing S]

attribute [local instance] MvPolynomial.gradedAlgebra

private def coefficientChartRingMap (f : R →+* S) (j : Fin 2) :
    chartRing R j →+* chartRing S j :=
  HomogeneousLocalization.map (MvPolynomial.gradedMap f) (by
    rintro p ⟨n, rfl⟩
    exact ⟨n, by simp only [MvPolynomial.gradedMap_apply, map_pow, MvPolynomial.map_X]⟩)

private theorem coefficientChartRingMap_constant (f : R →+* S) (j : Fin 2) (r : R) :
    coefficientChartRingMap f j (chartConstant R j r) = chartConstant S j (f r) := by
  apply HomogeneousLocalization.val_injective
  change (HomogeneousLocalization.map (MvPolynomial.gradedMap f) _
    (HomogeneousLocalization.mk ⟨0, constToGradeZero R r, 1, one_mem _⟩)).val = _
  rw [HomogeneousLocalization.map_mk]
  simp only [HomogeneousLocalization.val_mk]
  change Localization.mk (MvPolynomial.map f (MvPolynomial.C r))
    ⟨MvPolynomial.map f (1 : MvPolynomial (Fin 2) R), _⟩ =
      Localization.mk (MvPolynomial.C (f r)) ⟨1, _⟩
  simp only [MvPolynomial.map_C, map_one]

private theorem coefficientChartRingMap_ratio (f : R →+* S) (j : Fin 2) :
    coefficientChartRingMap f j (chartRatio R j) = chartRatio S j := by
  apply HomogeneousLocalization.val_injective
  simp only [coefficientChartRingMap, chartRatio, HomogeneousLocalization.Away.mk,
    HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]
  change Localization.mk (MvPolynomial.map f (MvPolynomial.X j.rev))
      ⟨MvPolynomial.map f ((MvPolynomial.X j) ^ 1), _⟩ =
    Localization.mk (MvPolynomial.X j.rev) ⟨(MvPolynomial.X j) ^ 1, _⟩
  simp only [MvPolynomial.map_X, map_pow]

private theorem coefficientChartRingMap_dehomogenize (f : R →+* S) (j : Fin 2) :
    (dehomogenize S j).comp (coefficientChartRingMap f j) =
      (Polynomial.mapRingHom f).comp (dehomogenize R j) := by
  apply chartRing_hom_ext R j
  · intro r
    simp only [RingHom.comp_apply, coefficientChartRingMap_constant,
      dehomogenize_chartConstant, Polynomial.coe_mapRingHom, Polynomial.map_C]
  · simp only [RingHom.comp_apply, coefficientChartRingMap_ratio,
      dehomogenize_chartRatio, Polynomial.coe_mapRingHom, Polynomial.map_X]

private theorem homogeneousChart_map_of_image
    (φ : grading R →+*ᵍ grading S)
    (hφ : HomogeneousIdeal.irrelevant (grading S) ≤
      (HomogeneousIdeal.irrelevant (grading R)).map φ)
    (j : Fin 2) (t : MvPolynomial (Fin 2) S) (ht : t ∈ grading S 1)
    (he : φ (MvPolynomial.X j) = t) :
    Proj.awayι (grading S) t ht Nat.zero_lt_one ≫ Proj.map φ hφ =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.map φ
        (P := Submonoid.powers (MvPolynomial.X j)) (Q := Submonoid.powers t)
        (by rintro p ⟨n, rfl⟩; exact ⟨n, by rw [map_pow, he]⟩))) ≫
        Proj.awayι (grading R) (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j)
          Nat.zero_lt_one := by
  subst t
  exact Proj.awayι_comp_map φ hφ Nat.zero_lt_one (MvPolynomial.X j)
    (MvPolynomial.isHomogeneous_X R j)

private theorem coefficientChartRingMap_away (f : R →+* S) (j : Fin 2) :
    Proj.awayι (grading S) (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X S j)
        Nat.zero_lt_one ≫ LinearChange.coefficientMap f =
      Spec.map (CommRingCat.ofHom (coefficientChartRingMap f j)) ≫
        Proj.awayι (grading R) (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j)
          Nat.zero_lt_one :=
  homogeneousChart_map_of_image (MvPolynomial.gradedMap (ι := Fin 2) f)
    (by rw [MvPolynomial.irrelevant_map_gradedMap]) j (MvPolynomial.X j)
    (MvPolynomial.isHomogeneous_X S j) (MvPolynomial.map_X f j)

/-- Each original polynomial chart respects the literal projective coefficient map. -/
@[reassoc] theorem chart_coefficient (f : R →+* S) (j : Fin 2) :
    chart S j ≫ LinearChange.coefficientMap f =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) ≫ chart R j := by
  calc
    _ = Spec.map (CommRingCat.ofHom (dehomogenize S j)) ≫
        Spec.map (CommRingCat.ofHom (coefficientChartRingMap f j)) ≫
          Proj.awayι (grading R) (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j)
            Nat.zero_lt_one := by
      rw [chart, Category.assoc, coefficientChartRingMap_away]
    _ = _ := by
      simp only [chart, ← Category.assoc, ← Spec.map_comp]
      congr 2
      exact congrArg CommRingCat.ofHom (coefficientChartRingMap_dehomogenize f j)

end Conormal

namespace Conormal

private theorem infinityConormalIso_hom (R : Type u) [CommRing R] :
    (infinityConormalIso R).hom =
      Scheme.Hom.conormalMap (Sections.infinity R) (coordinateSection R) (chart R 1) rfl ≫
        (coordinateConormalIso R).hom := by
  rfl

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The original infinity conormal frame retains the actual coefficient morphism. -/
theorem infinityConormal_coefficient (f : R →+* S) :
    FrameMapCompatible (Spec.map (CommRingCat.ofHom f))
      (infinityConormalIso R) (infinityConormalIso S)
      (conormalSquareMap (Sections.infinity R) (Sections.infinity S)
        (LinearChange.coefficientMap f) (Spec.map (CommRingCat.ofHom f))
        (Sections.infinity_coefficient f).symm) :=
  frameMapCompatible_of_charts (Sections.infinity R) (Sections.infinity S)
    (coordinateSection R) (coordinateSection S) (chart R 1) (chart S 1) rfl rfl
    (Spec.map (CommRingCat.ofHom f)) (LinearChange.coefficientMap f)
    (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)))
    (Sections.infinity_coefficient f).symm (coordinateSection_coefficient f)
    (chart_coefficient f 1) (infinityConormalIso R) (infinityConormalIso S)
    (coordinateConormalIso R) (coordinateConormalIso S)
    (infinityConormalIso_hom R) (infinityConormalIso_hom S) (coordinateConormal_coefficient f)

/-- The original infinity frame respects the actual unipotent transition and coefficient map. -/
theorem infinityConormal_transition (f : R →+* S) (t : S) :
    FrameMapCompatible (Spec.map (CommRingCat.ofHom f))
      (infinityConormalIso R) (infinityConormalIso S)
      (conormalSquareMap (Sections.infinity R) (Sections.infinity S)
        (LinearChange.matrixMap S (Sections.translationMatrix S t) ≫
          LinearChange.coefficientMap f) (Spec.map (CommRingCat.ofHom f))
        (by rw [← Category.assoc, Sections.infinity_translation, Sections.infinity_coefficient])) :=
  frameMapCompatible_comp_ambient (Sections.infinity R) (Sections.infinity S)
    (Spec.map (CommRingCat.ofHom f)) (LinearChange.coefficientMap f)
    (Sections.infinity_coefficient f).symm
    (LinearChange.matrixMap S (Sections.translationMatrix S t))
    (Sections.infinity_translation S t).symm (infinityConormalIso R) (infinityConormalIso S)
    (infinityConormal_translation S t) (infinityConormal_coefficient f)

end Conormal

namespace Conormal

private def transportedFrame {D B : Scheme.{u}} (j : D ⟶ B)
    {M : B.Modules} {N : D.Modules} (k : (Modules.pullback j).obj M ≅ N)
    (e : M ≅ SheafOfModules.unit B.ringCatSheaf) :
    N ≅ SheafOfModules.unit D.ringCatSheaf :=
  k.symm ≪≫ (Modules.pullback j).mapIso e ≪≫ pullbackUnitIso j

private def FrameTransportSquare {D₀ D₁ B₀ B₁ : Scheme.{u}}
    (j₀ : D₀ ⟶ B₀) (j₁ : D₁ ⟶ B₁) (a : D₁ ⟶ D₀) (f : B₁ ⟶ B₀)
    (hj : j₁ ≫ f = a ≫ j₀) {M₀ : B₀.Modules} {M₁ : B₁.Modules}
    {N₀ : D₀.Modules} {N₁ : D₁.Modules}
    (k₀ : (Modules.pullback j₀).obj M₀ ≅ N₀)
    (k₁ : (Modules.pullback j₁).obj M₁ ≅ N₁)
    (q : (Modules.pullback f).obj M₀ ⟶ M₁)
    (q' : (Modules.pullback a).obj N₀ ⟶ N₁) : Prop :=
  (Modules.pullback a).map k₀.hom ≫ q' =
    (pullbackComp a j₀).hom.app M₀ ≫ (pullbackCongr hj).inv.app M₀ ≫
      (pullbackComp j₁ f).inv.app M₀ ≫ (Modules.pullback j₁).map q ≫ k₁.hom

private def PullbackFrameTransport {D₀ D₁ B₀ B₁ : Scheme.{u}}
    (j₀ : D₀ ⟶ B₀) (j₁ : D₁ ⟶ B₁) (a : D₁ ⟶ D₀) (f : B₁ ⟶ B₀)
    (hj : j₁ ≫ f = a ≫ j₀) (M : B₀.Modules)
    (e : M ≅ SheafOfModules.unit B₀.ringCatSheaf) : Prop :=
  (pullbackComp a j₀).hom.app M ≫ (pullbackCongr hj).inv.app M ≫
      (pullbackComp j₁ f).inv.app M ≫
        (Modules.pullback j₁).map ((Modules.pullback f).map e.hom) ≫
        (Modules.pullback j₁).map (pullbackUnitIso f).hom ≫ (pullbackUnitIso j₁).hom =
    (Modules.pullback a).map ((Modules.pullback j₀).map e.hom) ≫
      (Modules.pullback a).map (pullbackUnitIso j₀).hom ≫ (pullbackUnitIso a).hom

private theorem pullbackFrameTransport {D₀ D₁ B₀ B₁ : Scheme.{u}}
    (j₀ : D₀ ⟶ B₀) (j₁ : D₁ ⟶ B₁) (a : D₁ ⟶ D₀) (f : B₁ ⟶ B₀)
    (hj : j₁ ≫ f = a ≫ j₀) (M : B₀.Modules)
    (e : M ≅ SheafOfModules.unit B₀.ringCatSheaf) :
    PullbackFrameTransport j₀ j₁ a f hj M e := by
  unfold PullbackFrameTransport
  have hn₁ := (pullbackComp j₁ f).inv.naturality e.hom
  dsimp only [Functor.comp_map] at hn₁
  erw [← reassoc_of% hn₁, ← pullbackUnitIso_comp j₁ f]
  simp only [Iso.inv_hom_id_app_assoc]
  have hn₂ := (pullbackCongr hj).inv.naturality e.hom
  erw [← reassoc_of% hn₂, ← pullbackUnitIso_congr hj]
  simp only [Iso.inv_hom_id_app_assoc]
  have hn₃ := (pullbackComp a j₀).hom.naturality e.hom
  dsimp only [Functor.comp_map] at hn₃
  erw [← reassoc_of% hn₃]
  exact congrArg
    (fun q => (Modules.pullback a).map ((Modules.pullback j₀).map e.hom) ≫ q)
    (pullbackUnitIso_comp a j₀)

private theorem frameMapCompatible_transport {D₀ D₁ B₀ B₁ : Scheme.{u}}
    (j₀ : D₀ ⟶ B₀) (j₁ : D₁ ⟶ B₁) (a : D₁ ⟶ D₀) (f : B₁ ⟶ B₀)
    (hj : j₁ ≫ f = a ≫ j₀) {M₀ : B₀.Modules} {M₁ : B₁.Modules}
    {N₀ : D₀.Modules} {N₁ : D₁.Modules}
    (k₀ : (Modules.pullback j₀).obj M₀ ≅ N₀)
    (k₁ : (Modules.pullback j₁).obj M₁ ≅ N₁)
    (q : (Modules.pullback f).obj M₀ ⟶ M₁)
    (q' : (Modules.pullback a).obj N₀ ⟶ N₁)
    (e₀ : M₀ ≅ SheafOfModules.unit B₀.ringCatSheaf)
    (e₁ : M₁ ≅ SheafOfModules.unit B₁.ringCatSheaf)
    (hsq : FrameTransportSquare j₀ j₁ a f hj k₀ k₁ q q')
    (he : FrameMapCompatible f e₀ e₁ q) :
    FrameMapCompatible a (transportedFrame j₀ k₀ e₀) (transportedFrame j₁ k₁ e₁) q' := by
  unfold FrameMapCompatible at he ⊢
  unfold FrameTransportSquare at hsq
  apply (cancel_epi ((Modules.pullback a).map k₀.hom)).1
  change (Modules.pullback a).map k₀.hom ≫ q' ≫ k₁.inv ≫
      (Modules.pullback j₁).map e₁.hom ≫ (pullbackUnitIso j₁).hom =
    (Modules.pullback a).map k₀.hom ≫
      (Modules.pullback a).map (k₀.inv ≫ (Modules.pullback j₀).map e₀.hom ≫
        (pullbackUnitIso j₀).hom) ≫ (pullbackUnitIso a).hom
  simp only [Functor.map_comp, Category.assoc]
  have hk₀ := ((Modules.pullback a).mapIso k₀).hom_inv_id
  change (Modules.pullback a).map k₀.hom ≫ (Modules.pullback a).map k₀.inv = 𝟙 _ at hk₀
  rw [reassoc_of% hk₀, reassoc_of% hsq]
  simp only [Iso.hom_inv_id_assoc]
  rw [← (Modules.pullback j₁).map_comp_assoc, he, Functor.map_comp]
  simp only [Category.assoc]
  change PullbackFrameTransport j₀ j₁ a f hj M₀ e₀
  exact pullbackFrameTransport j₀ j₁ a f hj M₀ e₀

private def sourceConormalIso {D B Y : Scheme.{u}} (s : B ⟶ Y) (j : D ⟶ B) [IsIso j] :
    (Modules.pullback j).obj ((Modules.pullback s).obj (idealModule s)) ≅
      (Modules.pullback (j ≫ s)).obj (idealModule (j ≫ s)) := by
  let h : j ≫ s = (j ≫ s) ≫ 𝟙 Y := by simp only [Category.comp_id]
  let : IsIso (idealPullbackMap s (j ≫ s) (𝟙 Y) j h) :=
    idealPullbackMap_isIso_of_iso_square s (j ≫ s) (𝟙 Y) j h
  let : IsIso (conormalSquareMap s (j ≫ s) (𝟙 Y) j h) := by
    dsimp only [conormalSquareMap]
    infer_instance
  exact asIso (conormalSquareMap s (j ≫ s) (𝟙 Y) j h)

private theorem sourceConormalIso_hom {D B Y : Scheme.{u}} (s : B ⟶ Y)
    (j : D ⟶ B) [IsIso j] (h : j ≫ s = (j ≫ s) ≫ 𝟙 Y) :
    (sourceConormalIso s j).hom = conormalSquareMap s (j ≫ s) (𝟙 Y) j h := rfl

private def sourceConormalFrame {D B Y : Scheme.{u}} (s : B ⟶ Y) (j : D ⟶ B) [IsIso j]
    (e : (Modules.pullback s).obj (idealModule s) ≅ SheafOfModules.unit B.ringCatSheaf) :
    (Modules.pullback (j ≫ s)).obj (idealModule (j ≫ s)) ≅
      SheafOfModules.unit D.ringCatSheaf :=
  transportedFrame j (sourceConormalIso s j) e

private theorem sourceConormalFrame_square
    {D₀ D₁ B₀ B₁ Y₀ Y₁ : Scheme.{u}}
    (s₀ : B₀ ⟶ Y₀) (s₁ : B₁ ⟶ Y₁)
    (j₀ : D₀ ⟶ B₀) (j₁ : D₁ ⟶ B₁) [IsIso j₀] [IsIso j₁]
    (a : D₁ ⟶ D₀) (f : B₁ ⟶ B₀) (b : Y₁ ⟶ Y₀)
    (hf : f ≫ s₀ = s₁ ≫ b) (hj : j₁ ≫ f = a ≫ j₀) :
    FrameTransportSquare j₀ j₁ a f hj (sourceConormalIso s₀ j₀) (sourceConormalIso s₁ j₁)
      (conormalSquareMap s₀ s₁ b f hf)
      (conormalSquareMap (j₀ ≫ s₀) (j₁ ≫ s₁) b a
        (by rw [← Category.assoc, ← hj, Category.assoc, hf, Category.assoc])) := by
  unfold FrameTransportSquare
  let K₀ := sourceConormalIso s₀ j₀
  let K₁ := sourceConormalIso s₁ j₁
  let hs₀ : j₀ ≫ s₀ = (j₀ ≫ s₀) ≫ 𝟙 Y₀ := by simp only [Category.comp_id]
  let hs₁ : j₁ ≫ s₁ = (j₁ ≫ s₁) ≫ 𝟙 Y₁ := by simp only [Category.comp_id]
  let hlocal : a ≫ (j₀ ≫ s₀) = (j₁ ≫ s₁) ≫ b := by
    rw [← Category.assoc, ← hj, Category.assoc, hf, Category.assoc]
  let hright : (j₁ ≫ f) ≫ s₀ = (j₁ ≫ s₁) ≫ b := by
    rw [Category.assoc, hf, Category.assoc]
  let hleft : (a ≫ j₀) ≫ s₀ = (j₁ ≫ s₁) ≫ b := by
    rw [Category.assoc, hlocal]
  let Q := conormalSquareMap s₀ s₁ b f hf
  let Qlocal := conormalSquareMap (j₀ ≫ s₀) (j₁ ≫ s₁) b a hlocal
  let Qright := conormalSquareMap s₀ (j₁ ≫ s₁) b (j₁ ≫ f) hright
  let Qleft := conormalSquareMap s₀ (j₁ ≫ s₁) b (a ≫ j₀) hleft
  have hl : (Modules.pullback a).map K₀.hom ≫ Qlocal =
      (pullbackComp a j₀).hom.app ((Modules.pullback s₀).obj (idealModule s₀)) ≫ Qleft := by
    dsimp only [K₀, Qlocal, Qleft]
    rw [sourceConormalIso_hom s₀ j₀ hs₀]
    simpa only [Category.comp_id] using
      conormalSquareMap_comp s₀ (j₀ ≫ s₀) (j₁ ≫ s₁) j₀ a (𝟙 Y₀) b hs₀ hlocal
  have hr : (Modules.pullback j₁).map Q ≫ K₁.hom =
      (pullbackComp j₁ f).hom.app ((Modules.pullback s₀).obj (idealModule s₀)) ≫ Qright := by
    dsimp only [Q, K₁, Qright]
    rw [sourceConormalIso_hom s₁ j₁ hs₁]
    simpa only [Category.id_comp] using
      conormalSquareMap_comp s₀ s₁ (j₁ ≫ s₁) f j₁ b (𝟙 Y₁) hf hs₁
  have hg := conormalSquareMap_source_congr s₀ (j₁ ≫ s₁) b hj hright hleft
  have htransport : Qleft =
      (pullbackCongr hj).inv.app ((Modules.pullback s₀).obj (idealModule s₀)) ≫
        (pullbackComp j₁ f).inv.app ((Modules.pullback s₀).obj (idealModule s₀)) ≫
          (Modules.pullback j₁).map Q ≫ K₁.hom := by
    rw [hr, Iso.inv_hom_id_app_assoc]
    exact (((pullbackCongr hj).app _).inv_comp_eq.mpr hg.symm).symm
  change (Modules.pullback a).map K₀.hom ≫ Qlocal =
    (pullbackComp a j₀).hom.app ((Modules.pullback s₀).obj (idealModule s₀)) ≫
      (pullbackCongr hj).inv.app ((Modules.pullback s₀).obj (idealModule s₀)) ≫
        (pullbackComp j₁ f).inv.app ((Modules.pullback s₀).obj (idealModule s₀)) ≫
          (Modules.pullback j₁).map Q ≫ K₁.hom
  exact hl.trans (congrArg (fun q => (pullbackComp a j₀).hom.app
    ((Modules.pullback s₀).obj (idealModule s₀)) ≫ q) htransport)

private theorem sourceConormalFrame_naturality
    {D₀ D₁ B₀ B₁ Y₀ Y₁ : Scheme.{u}}
    (s₀ : B₀ ⟶ Y₀) (s₁ : B₁ ⟶ Y₁)
    (j₀ : D₀ ⟶ B₀) (j₁ : D₁ ⟶ B₁) [IsIso j₀] [IsIso j₁]
    (a : D₁ ⟶ D₀) (f : B₁ ⟶ B₀) (b : Y₁ ⟶ Y₀)
    (hf : f ≫ s₀ = s₁ ≫ b) (hj : j₁ ≫ f = a ≫ j₀)
    (e₀ : (Modules.pullback s₀).obj (idealModule s₀) ≅ SheafOfModules.unit B₀.ringCatSheaf)
    (e₁ : (Modules.pullback s₁).obj (idealModule s₁) ≅ SheafOfModules.unit B₁.ringCatSheaf)
    (he : FrameMapCompatible f e₀ e₁ (conormalSquareMap s₀ s₁ b f hf)) :
    FrameMapCompatible a (sourceConormalFrame s₀ j₀ e₀) (sourceConormalFrame s₁ j₁ e₁)
      (conormalSquareMap (j₀ ≫ s₀) (j₁ ≫ s₁) b a
        (by rw [← Category.assoc, ← hj, Category.assoc, hf, Category.assoc])) :=
  frameMapCompatible_transport j₀ j₁ a f hj (sourceConormalIso s₀ j₀) (sourceConormalIso s₁ j₁)
    (conormalSquareMap s₀ s₁ b f hf)
    (conormalSquareMap (j₀ ≫ s₀) (j₁ ≫ s₁) b a
      (by rw [← Category.assoc, ← hj, Category.assoc, hf, Category.assoc]))
    e₀ e₁ (sourceConormalFrame_square s₀ s₁ j₀ j₁ a f b hf hj) he

end Conormal

namespace Conormal

private def sourceIdealIso {D B Y : Scheme.{u}} (s : B ⟶ Y) (j : D ⟶ B) [IsIso j] :
    idealModule (j ≫ s) ≅ idealModule s := by
  let h : j ≫ s = (j ≫ s) ≫ 𝟙 Y := by simp only [Category.comp_id]
  let : IsIso (idealPullbackMap s (j ≫ s) (𝟙 Y) j h) :=
    idealPullbackMap_isIso_of_iso_square s (j ≫ s) (𝟙 Y) j h
  exact (asIso (idealPullbackMap s (j ≫ s) (𝟙 Y) j h)).symm ≪≫
    (pullbackId Y).app (idealModule s)

private theorem sourceConormalFrame_eq {D B Y : Scheme.{u}} (s : B ⟶ Y)
    (j : D ⟶ B) [IsIso j]
    (e : (Modules.pullback s).obj (idealModule s) ≅ SheafOfModules.unit B.ringCatSheaf) :
    (Modules.pullback (j ≫ s)).mapIso (sourceIdealIso s j) ≪≫
      ((pullbackComp j s).app (idealModule s)).symm ≪≫
      (Modules.pullback j).mapIso e ≪≫ pullbackUnitIso j = sourceConormalFrame s j e := by
  apply Iso.ext
  apply (cancel_epi (sourceConormalIso s j).hom).1
  let h : j ≫ s = (j ≫ s) ≫ 𝟙 Y := by simp only [Category.comp_id]
  let k := idealPullbackMap s (j ≫ s) (𝟙 Y) j h
  let : IsIso k := idealPullbackMap_isIso_of_iso_square s (j ≫ s) (𝟙 Y) j h
  change conormalSquareMap s (j ≫ s) (𝟙 Y) j h ≫
      (Modules.pullback (j ≫ s)).map ((asIso k).inv ≫ (pullbackId Y).hom.app (idealModule s)) ≫
      (pullbackComp j s).inv.app (idealModule s) ≫
      (Modules.pullback j).map e.hom ≫ (pullbackUnitIso j).hom =
    (sourceConormalIso s j).hom ≫ (sourceConormalIso s j).inv ≫
      (Modules.pullback j).map e.hom ≫ (pullbackUnitIso j).hom
  rw [Iso.hom_inv_id_assoc]
  dsimp only [conormalSquareMap]
  simp only [Functor.map_comp, Category.assoc]
  have hk := ((Modules.pullback (j ≫ s)).mapIso (asIso k)).hom_inv_id
  change (Modules.pullback (j ≫ s)).map k ≫
      (Modules.pullback (j ≫ s)).map (asIso k).inv = 𝟙 _ at hk
  rw [reassoc_of% hk]
  have hu := congrArg (fun q => q.app (idealModule s))
    (Scheme.Modules.pseudofunctor_left_unitality (j ≫ s))
  have hu' : (pullbackComp (j ≫ s) (𝟙 Y)).inv.app (idealModule s) ≫
      (Modules.pullback (j ≫ s)).map ((pullbackId Y).hom.app (idealModule s)) =
    (pullbackCongr (Category.comp_id (j ≫ s))).hom.app (idealModule s) := by
    simpa [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
      Category.assoc, pullbackCongr] using hu
  rw [reassoc_of% hu']
  have hc : (pullbackCongr h).hom.app (idealModule s) ≫
      (pullbackCongr (Category.comp_id (j ≫ s))).hom.app (idealModule s) = 𝟙 _ := by
    simp [pullbackCongr]
  rw [reassoc_of% hc, Iso.hom_inv_id_app_assoc]

end Conormal

private theorem localQuotientConormalIso_eq_sourceFrame (a : AffineFrame g) :
    localQuotientConormalIso g a =
      Conormal.sourceConormalFrame (Sections.infinity Γ(X, a.U.1)) a.isoSpec.hom
        (Conormal.infinityConormalIso Γ(X, a.U.1)) :=
  Conormal.sourceConormalFrame_eq (Sections.infinity Γ(X, a.U.1)) a.isoSpec.hom
    (Conormal.infinityConormalIso Γ(X, a.U.1))

/-- The actual source-spectrum maps respect the original affine-open inclusion. -/
private theorem frame_isoSpec_refinement {a b : AffineFrame g} (h : a ≤ b) :
    a.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
      (scalarRestriction (show a.U.1 ≤ b.U.1 from h))) =
      X.homOfLE (show a.U.1 ≤ b.U.1 from h) ≫ b.isoSpec.hom :=
  a.U.1.toSpecΓ_SpecMap_presheaf_map b.U.1 h

/-- The local quotient-section square for the original frame transition. -/
theorem localQuotientSection_refinement {a b : AffineFrame g} (h : a ≤ b) :
    X.homOfLE (show a.U.1 ≤ b.U.1 from h) ≫ localQuotientSection g b =
      localQuotientSection g a ≫ chartMap i g hig hS h := by
  apply (cancel_mono (chartInclusion i g hig hS b)).1
  calc
    _ = X.homOfLE (show a.U.1 ≤ b.U.1 from h) ≫ (b.U.1.ι ≫ quotientSection i g hig hS) := by
      rw [Category.assoc, quotientSection_chart]
    _ = a.U.1.ι ≫ quotientSection i g hig hS := by
      rw [← Category.assoc, X.homOfLE_ι]
    _ = localQuotientSection g a ≫ chartInclusion i g hig hS a :=
      quotientSection_chart i g hig hS a
    _ = _ := by rw [Category.assoc, chartMap_chartInclusion]

/-- The actual local conormal frames respect every original affine-frame transition. -/
theorem localQuotientConormalIso_refinement {a b : AffineFrame g} (h : a ≤ b) :
    Conormal.FrameMapCompatible (X.homOfLE (show a.U.1 ≤ b.U.1 from h))
      (localQuotientConormalIso g b) (localQuotientConormalIso g a)
      (conormalSquareMap (localQuotientSection g b) (localQuotientSection g a)
        (chartMap i g hig hS h) (X.homOfLE (show a.U.1 ≤ b.U.1 from h))
        (localQuotientSection_refinement g i hig hS h)) := by
  rw [localQuotientConormalIso_eq_sourceFrame, localQuotientConormalIso_eq_sourceFrame]
  exact Conormal.sourceConormalFrame_naturality
    (Sections.infinity Γ(X, b.U.1)) (Sections.infinity Γ(X, a.U.1))
    b.isoSpec.hom a.isoSpec.hom (X.homOfLE (show a.U.1 ≤ b.U.1 from h))
    (Spec.map (CommRingCat.ofHom (scalarRestriction (show a.U.1 ≤ b.U.1 from h))))
    (chartMap i g hig hS h)
    (by rw [chartMap, ← Category.assoc, Sections.infinity_translation,
      Sections.infinity_coefficient])
    (frame_isoSpec_refinement g h) (Conormal.infinityConormalIso Γ(X, b.U.1))
    (Conormal.infinityConormalIso Γ(X, a.U.1))
    (Conormal.infinityConormal_transition
      (scalarRestriction (show a.U.1 ≤ b.U.1 from h)) (transition i g hig hS h))

private theorem frameRestrictionIso_pullback (M : X.Modules)
    {a b : AffineFrame g} (h : a ≤ b) :
    (frameRestrictionIso g M h).hom ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE (show a.U.1 ≤ b.U.1 from h))).map
        ((restrictFunctorIsoPullback b.U.1.ι).hom.app M) ≫
        (restrictFunctorIsoPullback (X.homOfLE (show a.U.1 ≤ b.U.1 from h))).hom.app
          ((Modules.pullback b.U.1.ι).obj M) =
      (restrictFunctorIsoPullback a.U.1.ι).hom.app M ≫
        (pullbackCongr (X.homOfLE_ι (show a.U.1 ≤ b.U.1 from h)).symm).hom.app M ≫
          (pullbackComp (X.homOfLE (show a.U.1 ≤ b.U.1 from h)) b.U.1.ι).inv.app M := by
  simp only [frameRestrictionIso, Iso.trans_hom, Iso.app_hom, Category.assoc]
  rw [← restrictFunctorIsoPullback_comp_hom_app]
  rw [← reassoc_of% (restrictFunctorIsoPullback_congr_hom_app
    (X.homOfLE_ι (show a.U.1 ≤ b.U.1 from h)).symm M)]

private theorem restrictPullbackUnit_hom {U V : Scheme.{u}} (f : U ⟶ V)
    [IsOpenImmersion f] :
    (restrictFunctorIsoPullback f).hom.app
        (show V.Modules from SheafOfModules.unit V.ringCatSheaf) ≫
      (pullbackUnitIso f).hom = (restrictUnitIso f).hom :=
  Scheme.Modules.restrictFunctorIsoPullback_hom_unit f

private theorem frameRestrictionIso_unit {a b : AffineFrame g} (h : a ≤ b) :
    (frameRestrictionIso g (SheafOfModules.unit X.ringCatSheaf) h).hom ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE (show a.U.1 ≤ b.U.1 from h))).map
        (restrictUnitIso b.U.1.ι).hom ≫
        (restrictUnitIso (X.homOfLE (show a.U.1 ≤ b.U.1 from h))).hom =
      (restrictUnitIso a.U.1.ι).hom := by
  rw [← restrictPullbackUnit_hom b.U.1.ι,
    ← restrictPullbackUnit_hom (X.homOfLE (show a.U.1 ≤ b.U.1 from h))]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (restrictFunctorIsoPullback (X.homOfLE (show a.U.1 ≤ b.U.1 from h))).hom.naturality
    (pullbackUnitIso b.U.1.ι).hom
  rw [reassoc_of% hn]
  rw [reassoc_of% (frameRestrictionIso_pullback g (SheafOfModules.unit X.ringCatSheaf) h)]
  rw [← pullbackUnitIso_comp (X.homOfLE (show a.U.1 ≤ b.U.1 from h)) b.U.1.ι]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [pullbackUnitIso_congr, restrictPullbackUnit_hom]

private theorem frameRestriction_refines_of_pullback (M : X.Modules)
    (e : ∀ a : AffineFrame g, (Modules.pullback a.U.1.ι).obj M ≅
      SheafOfModules.unit a.U.1.toScheme.ringCatSheaf)
    {a b : AffineFrame g} (h : a ≤ b)
    (he : Conormal.PullbackFrameRefinement
      (X.homOfLE (show a.U.1 ≤ b.U.1 from h)) a.U.1.ι b.U.1.ι
      (X.homOfLE_ι (show a.U.1 ≤ b.U.1 from h)) M (e a) (e b)) :
    (frameRestrictionIso g M h).hom ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE (show a.U.1 ≤ b.U.1 from h))).map
        (((restrictFunctorIsoPullback b.U.1.ι).app M ≪≫ e b ≪≫
          (restrictUnitIso b.U.1.ι).symm).hom) =
      (((restrictFunctorIsoPullback a.U.1.ι).app M ≪≫ e a ≪≫
        (restrictUnitIso a.U.1.ι).symm).hom) ≫
          (frameRestrictionIso g (SheafOfModules.unit X.ringCatSheaf) h).hom := by
  unfold Conormal.PullbackFrameRefinement at he
  apply (cancel_mono ((Scheme.Modules.restrictFunctor
    (X.homOfLE (show a.U.1 ≤ b.U.1 from h))).map (restrictUnitIso b.U.1.ι).hom ≫
      (restrictUnitIso (X.homOfLE (show a.U.1 ≤ b.U.1 from h))).hom)).1
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.map_comp, Category.assoc]
  have hmap := ((Scheme.Modules.restrictFunctor
    (X.homOfLE (show a.U.1 ≤ b.U.1 from h))).mapIso (restrictUnitIso b.U.1.ι)).inv_hom_id
  change (Scheme.Modules.restrictFunctor (X.homOfLE (show a.U.1 ≤ b.U.1 from h))).map
      (restrictUnitIso b.U.1.ι).inv ≫
    (Scheme.Modules.restrictFunctor (X.homOfLE (show a.U.1 ≤ b.U.1 from h))).map
      (restrictUnitIso b.U.1.ι).hom = 𝟙 _ at hmap
  rw [reassoc_of% hmap, frameRestrictionIso_unit]
  erw [(restrictUnitIso a.U.1.ι).inv_hom_id, Category.comp_id]
  rw [← restrictPullbackUnit_hom (X.homOfLE (show a.U.1 ≤ b.U.1 from h))]
  have hn := (restrictFunctorIsoPullback
    (X.homOfLE (show a.U.1 ≤ b.U.1 from h))).hom.naturality (e b).hom
  rw [reassoc_of% hn]
  rw [reassoc_of% (frameRestrictionIso_pullback g M h), he]
  simp only [Iso.inv_hom_id_app_assoc]
  have hcongr : (pullbackCongr (X.homOfLE_ι (show a.U.1 ≤ b.U.1 from h)).symm).hom.app M ≫
      (pullbackCongr (X.homOfLE_ι (show a.U.1 ≤ b.U.1 from h))).hom.app M = 𝟙 _ := by
    simp [pullbackCongr]
  rw [reassoc_of% hcongr]

private theorem quotientConormalChartIso_hom (a : AffineFrame g) :
    (quotientConormalChartIso i g hig hS a).hom =
      conormalSquareMap (quotientSection i g hig hS) (localQuotientSection g a)
        (chartInclusion i g hig hS a) a.U.1.ι (quotientSection_chart i g hig hS a) ≫
          (localQuotientConormalIso g a).hom := by
  rfl

/-- The actual quotient conormal frames respect the native pullback comparison on a refinement. -/
theorem quotientConormalChartIso_refinement {a b : AffineFrame g} (h : a ≤ b) :
    Conormal.PullbackFrameRefinement
      (X.homOfLE (show a.U.1 ≤ b.U.1 from h)) a.U.1.ι b.U.1.ι
      (X.homOfLE_ι (show a.U.1 ≤ b.U.1 from h))
      ((Modules.pullback (quotientSection i g hig hS)).obj
        (idealModule (quotientSection i g hig hS)))
      (quotientConormalChartIso i g hig hS a) (quotientConormalChartIso i g hig hS b) :=
  Conormal.frameRefinement_of_conormal_squares (quotientSection i g hig hS)
    (localQuotientSection g b) (localQuotientSection g a) b.U.1.ι
    (X.homOfLE (show a.U.1 ≤ b.U.1 from h)) a.U.1.ι
    (chartInclusion i g hig hS b) (chartMap i g hig hS h) (chartInclusion i g hig hS a)
    (quotientSection_chart i g hig hS b) (localQuotientSection_refinement g i hig hS h)
    (quotientSection_chart i g hig hS a) (X.homOfLE_ι (show a.U.1 ≤ b.U.1 from h))
    (chartMap_chartInclusion i g hig hS h)
    (localQuotientConormalIso g b) (localQuotientConormalIso g a)
    (quotientConormalChartIso i g hig hS b) (quotientConormalChartIso i g hig hS a)
    (quotientConormalChartIso_hom g i hig hS b) (quotientConormalChartIso_hom g i hig hS a)
    (localQuotientConormalIso_refinement g i hig hS h)

/-- The actual short exact extension supplies the literal native refinement squares. -/
theorem quotientConormalFramesRefine : QuotientConormalFramesRefine g i hig hS := by
  intro a b h
  exact frameRestriction_refines_of_pullback g _ (quotientConormalChartIso i g hig hS) h
    (quotientConormalChartIso_refinement g i hig hS h)

/-- The original quotient conormal frames agree on every actual pullback overlap. -/
theorem quotientConormalFramesCompatible : QuotientConormalFramesCompatible i g hig hS :=
  quotientConormalFramesCompatible_of_refine g i hig hS
    (quotientConormalFramesRefine g i hig hS)

/-- The actual conormal of the quotient section of the original short exact extension
is canonically trivialized by its original coordinate-class frames. -/
def quotientConormalIso :
    (Modules.pullback (quotientSection i g hig hS)).obj (idealModule (quotientSection i g hig hS)) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  quotientConormalIsoOfCompatibleFrames i g hig hS
    (quotientConormalFramesCompatible g i hig hS)

/-- The canonical global conormal isomorphism retains every original local frame. -/
theorem quotientConormalIso_hom_restrict (a : AffineFrame g) :
    (Scheme.Modules.restrictFunctor a.U.1.ι).map (quotientConormalIso g i hig hS).hom =
      (quotientConormalRestrictionIso i g hig hS a).hom := by
  let : Epi g := hS.epi_g
  exact InternalHom.glueRestrictionIso_hom_restrict (fun a : AffineFrame g => a.U.1.toScheme)
    (fun a => a.U.1.ι) (fun x => (frameCover g).exists_eq x) _ _
    (quotientConormalRestrictionIso i g hig hS) (quotientConormalFramesCompatible g i hig hS) a

end AlgebraicGeometry.Scheme.ProjectiveBundle.RankTwoExtension
