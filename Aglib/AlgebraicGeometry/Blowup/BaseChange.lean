/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.UniversalProperty
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
Source: `R5Lab.Aglib.AlgebraicGeometry.Blowup.BaseChange`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `32097d8828df8b51e0982d39f4271633f1fac6947a5716fc0536d8e17a56befd`.
Actual maps and mathematical hypotheses are retained. Conditional family
definitions do not supply blowup existence, properness, base change or an atlas.
-/

@[expose] public section

/-!
# Canonical blowup maps, cartesian flat base change and exact affine centre pullback.

The declarations retain their original qualified interfaces and mathematical
inputs; the source-coverage comments below retain their original boundaries.
-/

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
universe u

section AlgebraicGeometry.Scheme.Blowup.BaseChange


/-!
# Canonical maps between actual blowups

Every centre compatibility below is an equality of actual ideal sheaves.
The map is constructed from the final-object universal property. Flat base
change is used only to prove that this already constructed map is cartesian.
-/
noncomputable section
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup
namespace AlgebraicGeometry.Scheme.Blowup.BaseChange
variable {X X' X'' : Scheme.{u}}
variable {I : X.IdealSheafData} {I' : X'.IdealSheafData} {I'' : X''.IdealSheafData}

lemma cartier_composite (f : X' ⟶ X) (hI : I.comap f = I')
    (B' : BlowupDatum I') : cartierPullback I (B'.map ≫ f) := by
  unfold cartierPullback
  rw [Scheme.IdealSheafData.comap_comp, hI]
  exact B'.cartier

/-- Canonical base map, defined even without flatness; exact centre equality
makes the actual inverse-image ideal Cartier on the source blowup. -/
def map (f : X' ⟶ X) (hI : I.comap f = I')
    (B : BlowupDatum I) (B' : BlowupDatum I') : B'.Y ⟶ B.Y :=
  B.lift (B'.map ≫ f) (cartier_composite f hI B')

@[reassoc (attr := simp)] lemma map_triangle (f : X' ⟶ X) (hI : I.comap f = I')
    (B : BlowupDatum I) (B' : BlowupDatum I') :
    map f hI B B' ≫ B.map = B'.map ≫ f := B.lift_map _ _

lemma map_unique (f : X' ⟶ X) (hI : I.comap f = I')
    (B : BlowupDatum I) (B' : BlowupDatum I') (g : B'.Y ⟶ B.Y)
    (hg : g ≫ B.map = B'.map ≫ f) : g = map f hI B B' :=
  B.hom_ext (cartier_composite f hI B') hg (map_triangle f hI B B')

@[simp] lemma map_id (B : BlowupDatum I) :
    map (𝟙 X) (I.comap_id) B B = 𝟙 B.Y := by
  symm
  apply map_unique
  simp

/-- Functoriality requires the second actual ideal square as well as the first. -/
lemma map_comp (f : X' ⟶ X) (g : X'' ⟶ X')
    (hI : I.comap f = I') (hI' : I'.comap g = I'')
    (B : BlowupDatum I) (B' : BlowupDatum I') (B'' : BlowupDatum I'') :
    map g hI' B' B'' ≫ map f hI B B' =
      map (g ≫ f) (by simp only [Scheme.IdealSheafData.comap_comp, hI, hI']) B B'' := by
  apply map_unique
  simp only [Category.assoc, map_triangle, map_triangle_assoc]

lemma map_identity_base (B C : BlowupDatum I) :
    map (𝟙 X) I.comap_id B C = (C.comparisonIso B).hom := by
  symm
  apply map_unique
  simp

/-- The universal reviewed flat-base-change family proves cartesianness of
our canonical map. No specialized blowup/resolution comparison is assumed. -/
lemma isPullback (hbc : BlowupFlatBaseChange.{u})
    (f : X' ⟶ X) (hf : Flat f) (hI : I.comap f = I')
    (B : BlowupDatum I) (B' : BlowupDatum I') :
    IsPullback (map f hI B B') B'.map B.map f := by
  subst I'
  obtain ⟨g, hg⟩ := hbc X X' f hf I B B'
  have heq := map_unique f rfl B B' g hg.w
  simpa only [heq] using hg

/-- The comparison is an actual isomorphism to the literal fibre product. -/
def isoPullback (hbc : BlowupFlatBaseChange.{u})
    (f : X' ⟶ X) (hf : Flat f) (hI : I.comap f = I')
    (B : BlowupDatum I) (B' : BlowupDatum I') : B'.Y ≅ pullback B.map f :=
  (isPullback hbc f hf hI B B').isoPullback

@[reassoc (attr := simp)] lemma isoPullback_hom_fst (hbc : BlowupFlatBaseChange.{u})
    (f : X' ⟶ X) (hf : Flat f) (hI : I.comap f = I')
    (B : BlowupDatum I) (B' : BlowupDatum I') :
    (isoPullback hbc f hf hI B B').hom ≫ pullback.fst B.map f = map f hI B B' :=
  (isPullback hbc f hf hI B B').isoPullback_hom_fst

@[reassoc (attr := simp)] lemma isoPullback_hom_snd (hbc : BlowupFlatBaseChange.{u})
    (f : X' ⟶ X) (hf : Flat f) (hI : I.comap f = I')
    (B : BlowupDatum I) (B' : BlowupDatum I') :
    (isoPullback hbc f hf hI B B').hom ≫ pullback.snd B.map f = B'.map :=
  (isPullback hbc f hf hI B B').isoPullback_hom_snd

lemma proper (hbc : BlowupFlatBaseChange.{u})
    (f : X' ⟶ X) (hf : Flat f) (hI : I.comap f = I')
    (B : BlowupDatum I) (B' : BlowupDatum I') [IsProper B.map] : IsProper B'.map :=
  MorphismProperty.of_isPullback (P := @IsProper) (isPullback hbc f hf hI B B') inferInstance

lemma flat (hbc : BlowupFlatBaseChange.{u})
    (f : X' ⟶ X) (hf : Flat f) (hI : I.comap f = I')
    (B : BlowupDatum I) (B' : BlowupDatum I') : Flat (map f hI B B') :=
  MorphismProperty.of_isPullback (P := @Flat) (isPullback hbc f hf hI B B').flip hf

lemma etale (hbc : BlowupFlatBaseChange.{u})
    (f : X' ⟶ X) (hf : Etale f) (hI : I.comap f = I')
    (B : BlowupDatum I) (B' : BlowupDatum I') : Etale (map f hI B B') := by
  let := hf
  exact MorphismProperty.of_isPullback (P := @Etale)
    (isPullback hbc f inferInstance hI B B').flip hf

end AlgebraicGeometry.Scheme.Blowup.BaseChange

end
end AlgebraicGeometry.Scheme.Blowup.BaseChange

section AffineCenterBaseChange


/-! # Literal pullback of the ideal sheaf belonging to an affine ideal -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup
namespace AlgebraicGeometry.Scheme.Blowup.BaseChange
variable {A S : Type u} [CommRing A] [CommRing S]

/-- The ordinary quotient square is a pushout, with the mapped ideal, including
all nilpotent scheme structure rather than only equality of supports. -/
lemma quotient_isPushout (f : A →+* S) (I : Ideal A) :
    IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (Ideal.Quotient.mk (I.map f)))
      (CommRingCat.ofHom (Ideal.quotientMap (I.map f) f (Ideal.le_comap_map))) := by
  have hw : CommRingCat.ofHom f ≫ CommRingCat.ofHom (Ideal.Quotient.mk (I.map f)) =
      CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
        CommRingCat.ofHom (Ideal.quotientMap (I.map f) f Ideal.le_comap_map) := by
    ext a
    simp
  refine ⟨⟨hw⟩, ⟨PushoutCocone.IsColimit.mk _ (fun c => ?_) ?_ ?_ ?_⟩⟩
  · exact CommRingCat.ofHom (Ideal.Quotient.lift (I.map f) c.inl.hom (by
      change I.map f ≤ RingHom.ker c.inl.hom
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change c.inl.hom (f a) = 0
      have h := congrArg (fun k : CommRingCat.of A ⟶ c.pt => k.hom a) c.condition
      change c.inl.hom (f a) = c.inr.hom (Ideal.Quotient.mk I a) at h
      simpa only [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero] using h))
  · intro c
    ext s
    rfl
  · intro c
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext a
    simpa using congrArg (fun k : CommRingCat.of A ⟶ c.pt => k.hom a) c.condition
  · intro c m hm _
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    exact congrArg CommRingCat.Hom.hom hm

/-- The affine centre pulls back to the literal mapped ideal. -/
lemma affineCenter_comap (f : A →+* S) (I : Ideal A) :
    (affineCenter A I).comap (Spec.map (CommRingCat.ofHom f)) =
      affineCenter S (I.map f) := by
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  let H := isPullback_SpecMap_of_isPushout _ _ _ _ (quotient_isPushout f I)
  change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap _ = _
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  rw [← Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom]
  rw [H.isoPullback_hom_fst]
  rfl

end AlgebraicGeometry.Scheme.Blowup.BaseChange

end
end AffineCenterBaseChange
