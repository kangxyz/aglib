/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.Ring.FilteredPullback
public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.OpenLocalizationRange
public import Aglib.RingTheory.Localization.PullbackAway
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Actual pullback-ring overlap diagrams

Compatible pairs of denominators determine elements of the native categorical ring pullbacks.
The spectrum diagram has the prescribed affine limit. Its original overlap maps are open
immersions with exact principal-open images. Cartesian scheme squares are proved from those
images and the actual structural equations, not by claiming that spectrum preserves ring
pullbacks.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits Opposite

universe u

namespace CommRingCat.FilteredPullback

variable {J : Type u} [Category.{u} J] {F : J ⥤ CommRingCat.{u}}
variable (c : Cocone F) {B : CommRingCat.{u}} (s : B ⟶ c.pt)

/-- The element of the actual categorical pullback determined by a compatible pair. -/
def pairedElement (j : J) (x : B) (y : F.obj j)
    (h : s.hom x = (c.ι.app j).hom y) : (ringDiagram c s).obj j :=
  Classical.choose (Types.exists_of_isPullback
    ((forget CommRingCat).map_isPullback (isPullback c s j)) x y h)

@[simp] theorem pairedElement_fst (j : J) (x : B) (y : F.obj j)
    (h : s.hom x = (c.ι.app j).hom y) :
    (pullback.fst s (c.ι.app j)).hom (pairedElement c s j x y h) = x :=
  (Classical.choose_spec (Types.exists_of_isPullback
    ((forget CommRingCat).map_isPullback (isPullback c s j)) x y h)).1

@[simp] theorem pairedElement_snd (j : J) (x : B) (y : F.obj j)
    (h : s.hom x = (c.ι.app j).hom y) :
    (pullback.snd s (c.ι.app j)).hom (pairedElement c s j x y h) = y :=
  (Classical.choose_spec (Types.exists_of_isPullback
    ((forget CommRingCat).map_isPullback (isPullback c s j)) x y h)).2

/-- Naturality of the native compatible-pair element, not an independent choice of a lift. -/
theorem map_pairedElement {i j : J} (q : i ⟶ j) (x : B)
    (y : F.obj i) (z : F.obj j)
    (hy : s.hom x = (c.ι.app i).hom y) (hz : s.hom x = (c.ι.app j).hom z)
    (hyz : (F.map q).hom y = z) :
    ((ringDiagram c s).map q).hom (pairedElement c s i x y hy) =
      pairedElement c s j x z hz := by
  apply Types.ext_of_isPullback
    ((forget CommRingCat).map_isPullback (isPullback c s j))
  · change (pullback.fst s (c.ι.app j)).hom _ =
      (pullback.fst s (c.ι.app j)).hom _
    exact (ringDiagram_map_fst_apply c s q (pairedElement c s i x y hy)).trans
      ((pairedElement_fst c s i x y hy).trans (pairedElement_fst c s j x z hz).symm)
  · change (pullback.snd s (c.ι.app j)).hom _ =
      (pullback.snd s (c.ι.app j)).hom _
    exact (ringDiagram_map_snd_apply c s q (pairedElement c s i x y hy)).trans
      ((congrArg (F.map q).hom (pairedElement_snd c s i x y hy)).trans
        (hyz.trans (pairedElement_snd c s j x z hz).symm))

end CommRingCat.FilteredPullback

namespace AlgebraicGeometry.Scheme.FinitePresentationEnvelope.OverlapPullback

variable {I : Type u} [Category.{u} I] (F : Iᵒᵖ ⥤ CommRingCat.{u})
variable (c : Cocone F) {B : CommRingCat.{u}} (s : B ⟶ c.pt)

/-- The actual pullback-ring spectrum diagram. -/
abbrev affine : I ⥤ Scheme.{u} :=
  (CommRingCat.FilteredPullback.ringDiagram c s).rightOp ⋙ Scheme.Spec

/-- Its original cone at `Spec B`, using the native first projections. -/
def affineCone : Cone (affine F c s) :=
  Scheme.Spec.mapCone
    (coneRightOpOfCocone (CommRingCat.FilteredPullback.ringCocone c s))

@[simp] theorem affineCone_π_app (i : I) :
    (affineCone F c s).π.app i = Spec.map (pullback.fst s (c.ι.app (op i))) := rfl

/-- The spectrum cone is a native limit when the original ring cocone is a filtered colimit. -/
def affineConeIsLimit [IsCofiltered I] (hc : IsColimit c) :
    IsLimit (affineCone F c s) :=
  isLimitOfPreserves Scheme.Spec (isLimitConeRightOpOfCocone _
    (CommRingCat.FilteredPullback.ringCoconeIsColimit c s hc))

variable {L : Type u} (g : L → B) (r : ∀ i : I, L → F.obj (op i))
variable (w : ∀ i l, s.hom (g l) = (c.ι.app (op i)).hom (r i l))

/-- The same denominator pair in every actual pullback ring. -/
def denominator (i : I) (l : L) :
    (CommRingCat.FilteredPullback.ringDiagram c s).obj (op i) :=
  CommRingCat.FilteredPullback.pairedElement c s (op i) (g l) (r i l) (w i l)

@[simp] theorem denominator_fst (i : I) (l : L) :
    (pullback.fst s (c.ι.app (op i))).hom (denominator F c s g r w i l) = g l :=
  CommRingCat.FilteredPullback.pairedElement_fst c s (op i) (g l) (r i l) (w i l)

@[simp] theorem denominator_snd (i : I) (l : L) :
    (pullback.snd s (c.ι.app (op i))).hom (denominator F c s g r w i l) = r i l :=
  CommRingCat.FilteredPullback.pairedElement_snd c s (op i) (g l) (r i l) (w i l)

/-- Exact principal-image equality for the native first projection. -/
theorem denominator_principal_fst (i : I) :
    (⨆ l, PrimeSpectrum.basicOpen
      ((pullback.fst s (c.ι.app (op i))).hom (denominator F c s g r w i l))) =
      ⨆ l, PrimeSpectrum.basicOpen (g l) :=
  congrArg (fun t : L → B => ⨆ l, PrimeSpectrum.basicOpen (t l))
    (funext (denominator_fst F c s g r w i))

/-- Exact principal-image equality for the native second projection. -/
theorem denominator_principal_snd (i : I) :
    (⨆ l, PrimeSpectrum.basicOpen
      ((pullback.snd s (c.ι.app (op i))).hom (denominator F c s g r w i l))) =
      ⨆ l, PrimeSpectrum.basicOpen (r i l) :=
  congrArg (fun t : L → F.obj (op i) => ⨆ l, PrimeSpectrum.basicOpen (t l))
    (funext (denominator_snd F c s g r w i))

/-- Compatible original sections give natural denominators through the native ring maps. -/
theorem denominator_naturality
    (hr : ∀ {i j : I} (q : i ⟶ j) l, (F.map q.op).hom (r j l) = r i l)
    {i j : I} (q : i ⟶ j) (l : L) :
    ((CommRingCat.FilteredPullback.ringDiagram c s).map q.op).hom
        (denominator F c s g r w j l) = denominator F c s g r w i l :=
  CommRingCat.FilteredPullback.map_pairedElement c s q.op (g l) (r j l) (r i l)
    (w j l) (w i l) (hr q l)

variable (W : I ⥤ Scheme.{u}) (e : W ⟶ F.rightOp ⋙ Scheme.Spec)

/-- The actual overlap transformation is composed with the native second ring projections. -/
def toAffine : W ⟶ affine F c s :=
  e ≫ Functor.whiskerRight
    (NatTrans.rightOp (CommRingCat.FilteredPullback.toOriginal c s)) Scheme.Spec

@[simp] theorem toAffine_app (i : I) :
    (toAffine F c s W e).app i =
      e.app i ≫ Spec.map (pullback.snd s (c.ι.app (op i))) := rfl

/-- Localization of each native second projection is bijective. -/
theorem denominator_awayMap_bijective
    (hs : ∀ l, Function.Bijective (Localization.awayMap s.hom (g l))) (i : I) (l : L) :
    Function.Bijective (Localization.awayMap
      (pullback.snd s (c.ι.app (op i))).hom (denominator F c s g r w i l)) := by
  apply IsLocalization.Away.map_bijective_of_isPullback
    (pullback.fst s (c.ι.app (op i))) (pullback.snd s (c.ι.app (op i)))
    s (c.ι.app (op i)) (.of_hasPullback _ _)
  change Function.Bijective (Localization.awayMap s.hom
    ((pullback.fst s (c.ι.app (op i))).hom (denominator F c s g r w i l)))
  rw [denominator_fst]
  exact hs l

include w in
/-- The original overlap schemes map openly into the actual pullback-ring spectra. -/
theorem toAffine_isOpenImmersion [∀ i, IsOpenImmersion (e.app i)]
    (he : ∀ i, (e.app i).opensRange = ⨆ l, PrimeSpectrum.basicOpen (r i l))
    (hs : ∀ l, Function.Bijective (Localization.awayMap s.hom (g l))) (i : I) :
    IsOpenImmersion ((toAffine F c s W e).app i) := by
  apply Scheme.isOpenImmersion_comp_of_awayMap_bijective (e.app i)
    (pullback.snd s (c.ι.app (op i))) (denominator F c s g r w i)
  · exact (he i).trans (denominator_principal_snd F c s g r w i).symm
  · exact denominator_awayMap_bijective F c s g r w hs i

/-- The exact open images are the unions of the constructed principal opens. -/
theorem toAffine_opensRange [∀ i, IsOpenImmersion (e.app i)]
    (he : ∀ i, (e.app i).opensRange = ⨆ l, PrimeSpectrum.basicOpen (r i l))
    (hs : ∀ l, Function.Bijective (Localization.awayMap s.hom (g l))) (i : I)
    [IsOpenImmersion ((toAffine F c s W e).app i)] :
    ((toAffine F c s W e).app i).opensRange =
      ⨆ l, PrimeSpectrum.basicOpen (denominator F c s g r w i l) := by
  exact Scheme.opensRange_comp_of_awayMap_bijective (e.app i)
    (pullback.snd s (c.ι.app (op i))) (denominator F c s g r w i)
    ((he i).trans (denominator_principal_snd F c s g r w i).symm)
    (denominator_awayMap_bijective F c s g r w hs i)

/-- The original structural equations give the actual cone-square commutativity. -/
theorem cone_square_commutes {Z : Scheme.{u}} (a : Z ⟶ Spec c.pt)
    (v : Z ⟶ Spec B) (hv : v = a ≫ Spec.map s) (i : I) (p : Z ⟶ W.obj i)
    (hp : p ≫ e.app i = a ≫ Spec.map (c.ι.app (op i))) :
    v ≫ (affineCone F c s).π.app i = p ≫ (toAffine F c s W e).app i := by
  change v ≫ Spec.map (pullback.fst s (c.ι.app (op i))) =
    p ≫ (e.app i ≫ Spec.map (pullback.snd s (c.ι.app (op i))))
  rw [hv, ← Category.assoc, hp]
  rw [Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    pullback.condition]

include w in
/-- The original open-cone square is cartesian by exact images, not ring-pullback duality. -/
theorem isPullback_cone_square [∀ i, IsOpenImmersion (e.app i)]
    (he : ∀ i, (e.app i).opensRange = ⨆ l, PrimeSpectrum.basicOpen (r i l))
    (hs : ∀ l, Function.Bijective (Localization.awayMap s.hom (g l)))
    {Z : Scheme.{u}} (a : Z ⟶ Spec c.pt) (v : Z ⟶ Spec B) [IsOpenImmersion v]
    (hv : v = a ≫ Spec.map s)
    (hvRange : v.opensRange = ⨆ l, PrimeSpectrum.basicOpen (g l))
    (i : I) (p : Z ⟶ W.obj i)
    (hp : p ≫ e.app i = a ≫ Spec.map (c.ι.app (op i))) :
    IsPullback p v ((toAffine F c s W e).app i) ((affineCone F c s).π.app i) := by
  have : IsOpenImmersion ((toAffine F c s W e).app i) :=
    toAffine_isOpenImmersion F c s g r w W e he hs i
  apply Scheme.isPullback_of_principal_opensRange p v ((toAffine F c s W e).app i)
    (pullback.fst s (c.ι.app (op i))) (denominator F c s g r w i)
    (cone_square_commutes F c s W e a v hv i p hp)
  · exact toAffine_opensRange F c s g r w W e he hs i
  · exact hvRange.trans (denominator_principal_fst F c s g r w i).symm

/-- The canonical affinization transformation, retaining all original scheme maps. -/
def affinization (D : I ⥤ Scheme.{u}) : D ⟶ (D.op ⋙ Scheme.Γ).rightOp ⋙ Scheme.Spec where
  app i := (D.obj i).toSpecΓ
  naturality _i _j q := Scheme.toSpecΓ_naturality (D.map q)

/-- The actual section cocone of the original scheme cone. -/
abbrev sectionCocone (D : I ⥤ Scheme.{u}) (d : Cone D) : Cocone (D.op ⋙ Scheme.Γ) :=
  Scheme.Γ.mapCocone d.op

/-- The original cone maps satisfy the required canonical affinization square. -/
theorem affinization_cone_square (D : I ⥤ Scheme.{u}) (d : Cone D) (i : I) :
    d.π.app i ≫ (affinization D).app i =
      d.pt.toSpecΓ ≫ Spec.map ((sectionCocone D d).ι.app (op i)) :=
  Scheme.toSpecΓ_naturality (d.π.app i)

end AlgebraicGeometry.Scheme.FinitePresentationEnvelope.OverlapPullback
