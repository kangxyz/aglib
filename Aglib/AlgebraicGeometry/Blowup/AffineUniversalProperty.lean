/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AffineLiftingCover
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Universal factorization through the actual affine Rees Proj

The local maps use the original saturated chart inclusions. Regular cancellation
compares them on the actual chart overlaps, including nonreduced test schemes.
This file contains new proofs; the original blowup interface and chart providers
are unchanged.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Blowup

/-- A map to an actual saturated chart is forced by its original base map when the pivot
has regular image. -/
lemma affineChartHom_ext {A S : Type u} [CommRing A] [CommRing S]
    (I : Ideal A) (a : I) (f : A →+* S) (hreg : IsRegular (f a))
    (g h : Spec (.of S) ⟶ Spec (.of (affineBlowupAlgebra A I a)))
    (hg : g ≫ affineChartMap A I a = Spec.map (CommRingCat.ofHom f))
    (hh : h ≫ affineChartMap A I a = Spec.map (CommRingCat.ofHom f)) : g = h := by
  obtain ⟨γ, rfl⟩ := Spec.map_surjective g
  obtain ⟨η, rfl⟩ := Spec.map_surjective h
  rw [affineChartMap, ← Spec.map_comp] at hg hh
  have hγ := congrArg CommRingCat.Hom.hom (Spec.map_injective hg)
  have hη := congrArg CommRingCat.Hom.hom (Spec.map_injective hh)
  exact congrArg (fun k => Spec.map (CommRingCat.ofHom k))
    (Localization.Away.SaturatedChart.ringHom_ext I a f hreg γ.hom η.hom hγ hη)

/-- A map into any original chart lands in the chart of a regular generator of the actual
image ideal. The unit determining the overlap is proved by regular cancellation. -/
lemma affineChartHom_range_pivot {A S : Type u} [CommRing A] [CommRing S]
    (I : Ideal A) (a b : I) (f : A →+* S) (hreg : IsRegular (f a))
    (hdiv : ∀ c : I, f a ∣ f c)
    (g : Spec (.of S) ⟶ Spec (.of (affineBlowupAlgebra A I b)))
    (hg : g ≫ affineChartMap A I b = Spec.map (CommRingCat.ofHom f)) :
    Set.range (g ≫ affineProjChart I b) ⊆ Set.range (affineProjChart I a) := by
  obtain ⟨γ, rfl⟩ := Spec.map_surjective g
  rw [affineChartMap, ← Spec.map_comp] at hg
  have hγ := congrArg CommRingCat.Hom.hom (Spec.map_injective hg)
  have hγbase (c : A) : γ.hom (algebraMap A (affineBlowupAlgebra A I b) c) = f c :=
    DFunLike.congr_fun hγ c
  have hratio : f b * γ.hom (ratio A I b a) = f a := by
    have h := congrArg γ.hom
      (Localization.Away.SaturatedChart.fractionElement_mul I b a)
    change γ.hom (algebraMap A (affineBlowupAlgebra A I b) b * ratio A I b a) =
      γ.hom (algebraMap A (affineBlowupAlgebra A I b) a) at h
    simpa only [map_mul, hγbase] using h
  obtain ⟨q, hq⟩ := hdiv b
  have hunit : IsUnit (γ.hom (ratio A I b a)) := by
    apply IsUnit.of_mul_eq_one_right q
    apply hreg.left
    simpa only [mul_one, ← mul_assoc, ← hq] using hratio
  rintro z ⟨s, rfl⟩
  change (Spec.map γ ≫ affineProjChart I b) s ∈ (affineProjChart I a).opensRange
  rw [affineProjChart_opensRange]
  change Spec.map γ s ∈ (affineProjChart I b) ⁻¹ᵁ
    Proj.basicOpen (reesAlgebra.grading I) (reesAlgebra.degreeOne I a)
  rw [affineProjChart_preimage]
  change γ.hom (ratio A I b a) ∉ s.asIdeal
  intro hs
  exact s.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem s.asIdeal hs hunit)

private lemma regular_map_of_flat {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : φ.Flat) {r : R} (hr : IsRegular r) : IsRegular (φ r) := by
  let : Algebra R S := φ.toAlgebra
  let : Module.Flat R S := hφ
  exact (Commute.isRegular_iff (Commute.all (φ r))).mpr
    (hr.left.isSMulRegular.of_flat (S := S)).isLeftRegular

/-- Every map from an affine scheme over the base lands in the chart of a regular pivot
which divides all centre images. No factorization or cover is assumed as input. -/
lemma affineProjHom_range_pivot {A S : Type u} [CommRing A] [CommRing S]
    (I : Ideal A) (a : I) (f : A →+* S) (hreg : IsRegular (f a))
    (hdiv : ∀ b : I, f a ∣ f b) (g : Spec (.of S) ⟶ affineProj I)
    (hg : g ≫ affineProjMap I = Spec.map (CommRingCat.ofHom f)) :
    Set.range g ⊆ Set.range (affineProjChart I a) := by
  let W := (affineProjCover I).openCover.pullback₁ g
  let V := OpenCover.affineRefinement W
  rintro y ⟨x, rfl⟩
  obtain ⟨p, z, hz⟩ := V.openCover.exists_eq x
  let d := V.f p
  let k := (W.X p.1).affineCover.f p.2 ≫ (affineProjCover I).openCover.pullbackHom g p.1
  have hk : k ≫ affineProjChart I p.1 = d ≫ g := by
    change ((W.X p.1).affineCover.f p.2 ≫
      pullback.snd g (affineProjChart I p.1)) ≫ affineProjChart I p.1 =
      ((W.X p.1).affineCover.f p.2 ≫ pullback.fst g (affineProjChart I p.1)) ≫ g
    simp only [Category.assoc, pullback.condition]
  let φ := (Spec.preimage d).hom
  have hφ : φ.Flat := Flat.SpecMap_iff.mp (by
    rw [Spec.map_preimage]
    infer_instance)
  let f' := φ.comp f
  have ha' : IsRegular (f' a) := regular_map_of_flat φ hφ hreg
  have hdiv' (b : I) : f' a ∣ f' b := map_dvd φ (hdiv b)
  have hbase : k ≫ affineChartMap A I (show I from p.1).val =
      Spec.map (CommRingCat.ofHom f') := by
    rw [← affineProjChart_map, ← Category.assoc, hk, Category.assoc, hg,
      ← Spec.map_preimage d, ← Spec.map_comp]
    rfl
  have hrange := affineChartHom_range_pivot I a p.1 f' ha' hdiv' k hbase
  apply hrange
  refine ⟨z, ?_⟩
  rw [hk]
  change g (d z) = g x
  exact congrArg g hz

/-- Two maps from an affine pivot chart to the actual Rees Proj agree over the original
base. The assertion applies to arbitrary commutative rings, including nonreduced rings. -/
lemma affineProjHom_ext_of_pivot {A S : Type u} [CommRing A] [CommRing S]
    (I : Ideal A) (a : I) (f : A →+* S) (hreg : IsRegular (f a))
    (hdiv : ∀ b : I, f a ∣ f b) (g h : Spec (.of S) ⟶ affineProj I)
    (hg : g ≫ affineProjMap I = Spec.map (CommRingCat.ofHom f))
    (hh : h ≫ affineProjMap I = Spec.map (CommRingCat.ofHom f)) : g = h := by
  let γ := IsOpenImmersion.lift (affineProjChart I a) g
    (affineProjHom_range_pivot I a f hreg hdiv g hg)
  let η := IsOpenImmersion.lift (affineProjChart I a) h
    (affineProjHom_range_pivot I a f hreg hdiv h hh)
  have hγ : γ ≫ affineChartMap A I a = Spec.map (CommRingCat.ofHom f) := by
    rw [← affineProjChart_map, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact hg
  have hη : η ≫ affineChartMap A I a = Spec.map (CommRingCat.ofHom f) := by
    rw [← affineProjChart_map, ← Category.assoc, IsOpenImmersion.lift_fac]
    exact hh
  have heq := affineChartHom_ext I a f hreg γ η hγ hη
  calc
    g = γ ≫ affineProjChart I a := (IsOpenImmersion.lift_fac _ _ _).symm
    _ = η ≫ affineProjChart I a := by rw [heq]
    _ = h := IsOpenImmersion.lift_fac _ _ _

/-- Cartier inverse image persists on every open subscheme. The comparison is the actual
pullback map of the image ideal; no tensor ideal is substituted for its image. -/
lemma cartierPullback_comp_of_isOpenImmersion {X T W : Scheme.{u}}
    (I : X.IdealSheafData) (f : T ⟶ X) (hf : cartierPullback I f)
    (e : W ⟶ T) [IsOpenImmersion e] : cartierPullback I (e ≫ f) := by
  let J := I.comap f
  let i := J.subschemeι
  let i' := (J.comap e).subschemeι
  let a := (J.comap e).subschemeMap J e (J.le_map_comap e)
  have h : a ≫ i = i' ≫ e := Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  have H : IsPullback a i' i e :=
    (isPullback_of_isClosedImmersion i' i a e h.symm (by simp [i, i'])).flip
  have : IsIso (Scheme.Hom.idealPullbackMap i i' e a h) :=
    Scheme.Hom.idealPullbackMap_isIso_of_isOpenImmersion i i' e a h H
  unfold cartierPullback
  rw [Scheme.IdealSheafData.comap_comp]
  exact Scheme.Modules.Invertible.isLocallyRankOne_of_iso _
    (asIso (Scheme.Hom.idealPullbackMap i i' e a h))
    (Scheme.Modules.Invertible.pullback_locallyRankOne e _ hf)

/-- The actual affine Rees Proj map has at most one factorization of any scheme map whose
literal inverse-image centre is Cartier. -/
theorem affineProjHom_ext {A : Type u} [CommRing A] (I : Ideal A)
    {T : Scheme.{u}} (f : T ⟶ Spec (.of A))
    (hf : cartierPullback (affineCenter A I) f) (g h : T ⟶ affineProj I)
    (hg : g ≫ affineProjMap I = f) (hh : h ≫ affineProjMap I = f) : g = h := by
  apply Cover.hom_ext (affineLiftingCover I f hf).openCover
  intro p
  apply affineProjHom_ext_of_pivot I p.1.2 (affineBaseMap f p.1.1) p.2.1 p.2.2
  · rw [Category.assoc, hg, spec_affineBaseMap]
    rfl
  · rw [Category.assoc, hh, spec_affineBaseMap]
    rfl

/-- The constructed local maps agree on the literal pullbacks of source-cover maps. -/
lemma affineLiftingCoverLift_compat {A : Type u} [CommRing A] (I : Ideal A)
    {T : Scheme.{u}} (f : T ⟶ Spec (.of A))
    (hf : cartierPullback (affineCenter A I) f)
    (p q : (affineLiftingCover I f hf).I₀) :
    pullback.fst ((affineLiftingCover I f hf).f p) ((affineLiftingCover I f hf).f q) ≫
        affineLiftingCoverLift I f hf p =
      pullback.snd _ _ ≫ affineLiftingCoverLift I f hf q := by
  let C := affineLiftingCover I f hf
  let e := pullback.fst (C.f p) (C.f q) ≫ C.f p
  have he : cartierPullback (affineCenter A I) (e ≫ f) :=
    cartierPullback_comp_of_isOpenImmersion (affineCenter A I) f hf e
  apply affineProjHom_ext I (e ≫ f) he
  · rw [Category.assoc, affineLiftingCoverLift_map]
    rfl
  · rw [Category.assoc, affineLiftingCoverLift_map]
    simpa only [e, Category.assoc] using
      (congrArg (fun k => k ≫ f) (pullback.condition (f := C.f p) (g := C.f q))).symm

/-- Factorization through the original affine Rees Proj, constructed by gluing the actual
saturated-chart lifts on the produced affine pivot cover. -/
def affineProjLift {A : Type u} [CommRing A] (I : Ideal A)
    {T : Scheme.{u}} (f : T ⟶ Spec (.of A))
    (hf : cartierPullback (affineCenter A I) f) : T ⟶ affineProj I :=
  (affineLiftingCover I f hf).openCover.glueMorphisms (affineLiftingCoverLift I f hf)
    (affineLiftingCoverLift_compat I f hf)

lemma affineLiftingCover_affineProjLift {A : Type u} [CommRing A] (I : Ideal A)
    {T : Scheme.{u}} (f : T ⟶ Spec (.of A))
    (hf : cartierPullback (affineCenter A I) f) (p : (affineLiftingCover I f hf).I₀) :
    (affineLiftingCover I f hf).f p ≫ affineProjLift I f hf =
      affineLiftingCoverLift I f hf p :=
  Cover.ι_glueMorphisms (affineLiftingCover I f hf).openCover
    (affineLiftingCoverLift I f hf) (affineLiftingCoverLift_compat I f hf) p

@[reassoc (attr := simp)]
lemma affineProjLift_map {A : Type u} [CommRing A] (I : Ideal A)
    {T : Scheme.{u}} (f : T ⟶ Spec (.of A))
    (hf : cartierPullback (affineCenter A I) f) :
    affineProjLift I f hf ≫ affineProjMap I = f := by
  apply Cover.hom_ext (affineLiftingCover I f hf).openCover
  intro p
  change ((affineLiftingCover I f hf).f p ≫ affineProjLift I f hf) ≫ affineProjMap I =
    (affineLiftingCover I f hf).f p ≫ f
  rw [affineLiftingCover_affineProjLift, affineLiftingCoverLift_map]

/-- The final-object property of the actual affine blowup map, on every scheme over
`Spec A` with Cartier literal inverse-image centre. No finiteness or Noetherian hypothesis
is used. -/
theorem affineProjMap_universal {A : Type u} [CommRing A] (I : Ideal A)
    (T : Scheme.{u}) (f : T ⟶ Spec (.of A))
    (hf : cartierPullback (affineCenter A I) f) :
    ∃! g : T ⟶ affineProj I, g ≫ affineProjMap I = f :=
  ⟨affineProjLift I f hf, affineProjLift_map I f hf, fun g hg =>
    affineProjHom_ext I f hf g _ hg (affineProjLift_map I f hf)⟩

/-- The existing blowup interface is now realized by the original native Rees Proj and
its original map, with the proved universal property. -/
def affineProjBlowupDatum {A : Type u} [CommRing A] (I : Ideal A) :
    BlowupDatum (affineCenter A I) where
  Y := affineProj I
  map := affineProjMap I
  cartier := affineProjMap_cartier I
  universal := affineProjMap_universal I

end AlgebraicGeometry.Scheme.Blowup
