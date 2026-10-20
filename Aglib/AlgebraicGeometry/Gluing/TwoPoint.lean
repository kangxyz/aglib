/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Limits

/-!
# Two complementary rational open charts and the field-product spectrum

Source: `R5Lab.Aglib.AlgebraicGeometry.Gluing.TwoPoint`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `d86d1d8fcd9d500ec4e5ce87a2254b4da94af2267dc9005d9f69d42bae0a0f15`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

section AlgebraicGeometry.Scheme.TwoPoint.DisjointOpenGluing

/-! Two actual disjoint covering open residue points determine the actual
split two-point scheme, retaining the original residue-field structure. -/
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.TwoPoint.DisjointOpenGluing
variable (k : Type u) [Field k] {X : Scheme.{u}}
  (a b : Spec (.of k) ⟶ X) [IsOpenImmersion a] [IsOpenImmersion b]
  (h : IsCompl a.opensRange b.opensRange)

/-- The colimit structure for two complementary rational open charts on `X`. -/
def cofan : IsColimit (BinaryCofan.mk a b) :=
  (nonempty_isColimit_binaryCofanMk_of_isCompl a b h).some

/-- The isomorphism from a scheme with two complementary rational open charts to the coproduct
of the two field spectra. -/
def coproductIso : X ≅ Spec (.of k) ⨿ Spec (.of k) :=
  (cofan k a b h).coconePointUniqueUpToIso (colimit.isColimit (pair _ _))

@[reassoc (attr := simp)] lemma left_coproductIso :
    a ≫ (coproductIso k a b h).hom = coprod.inl :=
  (cofan k a b h).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (pair _ _)) ⟨.left⟩

@[reassoc (attr := simp)] lemma right_coproductIso :
    b ≫ (coproductIso k a b h).hom = coprod.inr :=
  (cofan k a b h).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (pair _ _)) ⟨.right⟩

/-- The isomorphism identifying a scheme with two complementary rational open charts with `Spec
(k × k)`. -/
def iso : X ≅ Spec (.of (k × k)) :=
  (coproductIso k a b h).trans (asIso (coprodSpec k k))

@[reassoc (attr := simp)] lemma left_iso : a ≫ (iso k a b h).hom =
    Spec.map (CommRingCat.ofHom (RingHom.fst k k)) := by
  simp [iso]

@[reassoc (attr := simp)] lemma right_iso : b ≫ (iso k a b h).hom =
    Spec.map (CommRingCat.ofHom (RingHom.snd k k)) := by
  simp [iso]

/-- The structure morphism from `Spec (k × k)` induced by the diagonal ring map from `k`. -/
def structureMap : Spec (.of (k × k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom ((RingHom.id k).prod (RingHom.id k)))

lemma iso_over (s : X ⟶ Spec (.of k)) (ha : a ≫ s = 𝟙 _) (hb : b ≫ s = 𝟙 _) :
    (iso k a b h).hom ≫ structureMap k = s := by
  apply (cofan k a b h).hom_ext
  rintro ⟨(_ | _)⟩
  · simpa [structureMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp] using ha.symm
  · simpa [structureMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp] using hb.symm

/-- The isomorphism over `Spec k` determined by complementary open charts that are sections of
the given structure map. -/
def overIso (s : X ⟶ Spec (.of k)) (ha : a ≫ s = 𝟙 _) (hb : b ≫ s = 𝟙 _) :
    Over.mk s ≅ Over.mk (structureMap k) :=
  Over.isoMk (iso k a b h) (iso_over k a b h s ha hb)
end AlgebraicGeometry.Scheme.TwoPoint.DisjointOpenGluing

end -- noncomputable section
end AlgebraicGeometry.Scheme.TwoPoint.DisjointOpenGluing

namespace AlgebraicGeometry.Scheme.TwoPoint


/-- The first rational point of `Spec (k × k)`, induced by the first ring projection. -/
def productPoint0 (k : Type u) [Field k] : Spec (.of k) ⟶ Spec (.of (k × k)) :=
  Spec.map (CommRingCat.ofHom (RingHom.fst k k))

/-- The second rational point of `Spec (k × k)`, induced by the second ring projection. -/
def productPoint1 (k : Type u) [Field k] : Spec (.of k) ⟶ Spec (.of (k × k)) :=
  Spec.map (CommRingCat.ofHom (RingHom.snd k k))

lemma productPoints_ne (k : Type u) [Field k] : productPoint0 k ≠ productPoint1 k := by
  intro h
  have hring := Spec.map_injective h
  have hvalue := congrArg
    (fun f : CommRingCat.of (k × k) ⟶ CommRingCat.of k => f (1, 0)) hring
  simp at hvalue

@[reassoc] lemma productPoint0_over (k : Type u) [Field k] :
    productPoint0 k ≫ Spec.map (CommRingCat.ofHom (algebraMap k (k × k))) = 𝟙 _ := by
  unfold productPoint0
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap k (k × k)) ≫
      CommRingCat.ofHom (RingHom.fst k k) = 𝟙 (CommRingCat.of k) := by
    exact CommRingCat.hom_ext (RingHom.ext (fun x => rfl))
  rw [h, Spec.map_id]

@[reassoc] lemma productPoint1_over (k : Type u) [Field k] :
    productPoint1 k ≫ Spec.map (CommRingCat.ofHom (algebraMap k (k × k))) = 𝟙 _ := by
  unfold productPoint1
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap k (k × k)) ≫
      CommRingCat.ofHom (RingHom.snd k k) = 𝟙 (CommRingCat.of k) := by
    exact CommRingCat.hom_ext (RingHom.ext (fun x => rfl))
  rw [h, Spec.map_id]

lemma productPoints_hom_ext (k : Type u) [Field k] {T : Scheme.{u}}
    (f g : Spec (.of (k × k)) ⟶ T)
    (h0 : productPoint0 k ≫ f = productPoint0 k ≫ g)
    (h1 : productPoint1 k ≫ f = productPoint1 k ≫ g) : f = g := by
  rw [← cancel_epi (coprodSpec k k)]
  apply coprod.hom_ext
  · simpa only [coprodSpec_inl_assoc, productPoint0] using h0
  · simpa only [coprodSpec_inr_assoc, productPoint1] using h1

@[reassoc] lemma productPoint0_coprodSpecIso (k : Type u) [Field k] :
    productPoint0 k ≫ (asIso (coprodSpec k k)).inv = coprod.inl := by
  rw [productPoint0, ← coprodSpec_inl, Category.assoc]
  change coprod.inl ≫ (asIso (coprodSpec k k)).hom ≫
    (asIso (coprodSpec k k)).inv = coprod.inl
  simp

@[reassoc] lemma productPoint1_coprodSpecIso (k : Type u) [Field k] :
    productPoint1 k ≫ (asIso (coprodSpec k k)).inv = coprod.inr := by
  rw [productPoint1, ← coprodSpec_inr, Category.assoc]
  change coprod.inr ≫ (asIso (coprodSpec k k)).hom ≫
    (asIso (coprodSpec k k)).inv = coprod.inr
  simp

end AlgebraicGeometry.Scheme.TwoPoint
