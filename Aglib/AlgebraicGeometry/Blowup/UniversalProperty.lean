/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.Basic
public import Aglib.RingTheory.Localization.Away.SaturatedChart
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
Source: `R5Lab.Aglib.AlgebraicGeometry.Blowup.UniversalProperty`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `7845a6ec33be0accfd9fc43aa65208319c6609fd31244c68c27a6ee28a6a23dd`.
Actual maps and mathematical hypotheses are retained. Conditional family
definitions do not supply blowup existence, properness, base change or an atlas.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (IsLocallyRankOne isLocallyRankOne_iff_local_unit isLocallyRankOne_of_iso)

/-!
# Saturated affine blowup algebras, universal-property blowup data and affine atlases, with
uniqueness and away-from-centre isomorphisms.

The declarations retain their original qualified interfaces and mathematical
inputs; the source-coverage comments below retain their original boundaries.
-/

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
universe u

section AlgebraicGeometry.Scheme.Blowup


/-!
# Ordinary blowup interfaces and uniqueness

The four named general theorem families below are proposition
TYPES, not axioms or proved existence theorems. They require independent source
review before any application assumes them.

Source translation: `cartierPullback` means local rank one of the kernel module
of the actual closed immersion belonging to `I.comap f`. The kernel section
identification and the pullback closed subscheme are actual library objects.
The identification of this local-rank-one predicate with the invertible ideal
in Stacks 01WQ/01WR is an explicit mathematical source translation, not a newly
proved equivalence with a separate Lean effective-Cartier definition. In
particular, this is the image ideal in O_Y, not the possibly noninjective tensor
pullback of I.

The affine algebra is the generated subalgebra of A[1/a], so denominator torsion
is killed. It is never an unsaturated polynomial quotient.
-/

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Blowup

section AffineAlgebra
variable (A : Type u) [CommRing A]

/-- The saturated affine blowup algebra A[I/a] inside A[1/a]. -/
abbrev affineBlowupAlgebra (I : Ideal A) (a : A) :
    Subalgebra A (Localization.Away a) :=
  Localization.Away.saturatedChart A I a

/-- The fraction b/a in the saturated affine blowup chart indexed by a. -/
def ratio (I : Ideal A) (a b : I) : affineBlowupAlgebra A I a :=
  ⟨algebraMap A (Localization.Away (a : A)) b * IsLocalization.Away.invSelf (a : A),
    Algebra.subset_adjoin ⟨b, b.property, rfl⟩⟩

/-- The ideal sheaf cutting out Spec(A/I) inside Spec(A), given by its actual kernel. -/
def affineCenter (I : Ideal A) : (Spec (.of A)).IdealSheafData :=
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker

/-- The structure morphism of the saturated affine blowup algebra over Spec(A). -/
def affineChartMap (I : Ideal A) (a : A) :
    Spec (.of (affineBlowupAlgebra A I a)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (affineBlowupAlgebra A I a)))

/-- The principal-open inclusion obtained by inverting b/a in the a-chart. -/
def affineOverlapMap (I : Ideal A) (a b : I) :
    Spec (.of (Localization.Away (ratio A I a b))) ⟶
      Spec (.of (affineBlowupAlgebra A I a)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (affineBlowupAlgebra A I a) (Localization.Away (ratio A I a b))))

instance affineOverlapMap_isOpenImmersion (A : Type u) [CommRing A]
    (I : Ideal A) (a b : I) : IsOpenImmersion (affineOverlapMap A I a b) := by
  dsimp [affineOverlapMap]
  infer_instance

end AffineAlgebra

/-- Local rank one of the actual inverse-image ideal as an O_Y-module. -/
def cartierPullback {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : Y ⟶ X) : Prop :=
  IsLocallyRankOne Y (idealModule (I.comap f).subschemeι)

/-- The module in the definition has precisely the inverse-image ideal on
an affine open, as opposed to an arbitrary supplied line bundle. -/
theorem inverseImageIdeal_kernel {X Y : Scheme.{u}} (I : X.IdealSheafData)
    (f : Y ⟶ X) (U : Y.affineOpens) :
    RingHom.ker ((I.comap f).subschemeι.app U).hom = (I.comap f).ideal U :=
  (I.comap f).ker_subschemeι_app U

/-- The image-ideal predicate is precisely the existing native Cartier predicate
on the actual inverse-image closed subscheme; closedness is canonical. -/
theorem cartierPullback_iff_isEffectiveCartier {X Y : Scheme.{u}}
    (I : X.IdealSheafData) (f : Y ⟶ X) :
    cartierPullback I f ↔ Scheme.Hom.IsEffectiveCartier (I.comap f).subschemeι :=
  ⟨fun h => ⟨inferInstance, h⟩, fun h => h.isLocallyRankOne⟩

/-- The ordinary final-object universal property, Stacks 0806. -/
structure BlowupDatum {X : Scheme.{u}} (I : X.IdealSheafData) where
  /-- The scheme supplied as the representative of this blowup universal property. -/
  Y : Scheme.{u}
  /-- The supplied morphism from the blowup representative to its original scheme. -/
  map : Y ⟶ X
  cartier : cartierPullback I map
  universal : ∀ (T : Scheme.{u}) (f : T ⟶ X), cartierPullback I f →
    ∃! g : T ⟶ Y, g ≫ map = f

namespace BlowupDatum
variable {X : Scheme.{u}} {I : X.IdealSheafData}

/-- The unique map to the blowup, with its actual base triangle. -/
def lift (B : BlowupDatum I) {T : Scheme.{u}} (f : T ⟶ X)
    (hf : cartierPullback I f) : T ⟶ B.Y :=
  Classical.choose (B.universal T f hf)

@[reassoc (attr := simp)] theorem lift_map (B : BlowupDatum I)
    {T : Scheme.{u}} (f : T ⟶ X) (hf : cartierPullback I f) :
    B.lift f hf ≫ B.map = f :=
  (Classical.choose_spec (B.universal T f hf)).1

theorem hom_ext (B : BlowupDatum I) {T : Scheme.{u}} {f : T ⟶ X}
    (hf : cartierPullback I f) {g h : T ⟶ B.Y}
    (hg : g ≫ B.map = f) (hh : h ≫ B.map = f) : g = h := by
  obtain ⟨k, _, hk⟩ := B.universal T f hf
  exact (hk g hg).trans (hk h hh).symm

/-- Uniqueness is proved only from the displayed universal properties. -/
def comparisonIso (B C : BlowupDatum I) : B.Y ≅ C.Y where
  hom := C.lift B.map B.cartier
  inv := B.lift C.map C.cartier
  hom_inv_id := B.hom_ext B.cartier (by simp) (by simp)
  inv_hom_id := C.hom_ext C.cartier (by simp) (by simp)

@[reassoc (attr := simp)] theorem comparisonIso_hom_map (B C : BlowupDatum I) :
    (B.comparisonIso C).hom ≫ C.map = B.map := by
  exact C.lift_map B.map B.cartier

@[reassoc (attr := simp)] theorem comparisonIso_inv_map (B C : BlowupDatum I) :
    (B.comparisonIso C).inv ≫ B.map = C.map := by
  exact B.lift_map C.map C.cartier

theorem comparisonIso_unique (B C : BlowupDatum I) (e : B.Y ≅ C.Y)
    (he : e.hom ≫ C.map = B.map) : e = B.comparisonIso C := by
  apply Iso.ext
  exact C.hom_ext B.cartier he (comparisonIso_hom_map B C)

@[simp] theorem comparisonIso_refl (B : BlowupDatum I) :
    B.comparisonIso B = Iso.refl B.Y := by
  exact (B.comparisonIso_unique B (Iso.refl B.Y) (by simp)).symm

@[simp] theorem comparisonIso_trans (B C D : BlowupDatum I) :
    B.comparisonIso C ≪≫ C.comparisonIso D = B.comparisonIso D := by
  apply B.comparisonIso_unique D
  simp

/-- Properness of one universal representative transfers to every other one. -/
theorem proper_of_comparison (B C : BlowupDatum I) [IsProper B.map] :
    IsProper C.map := by
  rw [← comparisonIso_hom_map C B]
  infer_instance

theorem proper_iff (B C : BlowupDatum I) : IsProper B.map ↔ IsProper C.map := by
  constructor
  · intro h; let := h; exact proper_of_comparison B C
  · intro h; let := h; exact proper_of_comparison C B

/-- Blowing up an ideal already Cartier on X gives X itself. No separate
away-from-centre isomorphism premise is used. -/
def cartierIso (B : BlowupDatum I) (hI : cartierPullback I (𝟙 X)) : B.Y ≅ X where
  hom := B.map
  inv := B.lift (𝟙 X) hI
  hom_inv_id := B.hom_ext B.cartier (by simp) (by simp)
  inv_hom_id := B.lift_map (𝟙 X) hI

@[simp] theorem cartierIso_hom (B : BlowupDatum I)
    (hI : cartierPullback I (𝟙 X)) : (B.cartierIso hI).hom = B.map := rfl

end BlowupDatum

/-- An actual atlas with literal saturated rings, base triangles, full coverage,
and the usual D_+(a) intersection described as localization at b/a. -/
structure AffineAtlas (A : Type u) [CommRing A] (I : Ideal A)
    (B : BlowupDatum (affineCenter A I)) where
  /-- The supplied chart morphisms from the literal saturated blowup algebras. -/
  chart : ∀ a : I, Spec (.of (affineBlowupAlgebra A I a)) ⟶ B.Y
  openImmersion : ∀ a, IsOpenImmersion (chart a)
  triangle : ∀ a, chart a ≫ B.map = affineChartMap A I a
  covers : ∀ y : B.Y, ∃ a : I, y ∈ Set.range (chart a)
  overlap : ∀ a b : I, Set.range (affineOverlapMap A I a b ≫ chart a) =
    Set.range (chart a) ∩ Set.range (chart b)

namespace AffineAtlas
variable {A : Type u} [CommRing A] {I : Ideal A}
variable {B C D : BlowupDatum (affineCenter A I)}

/-- Each atlas overlap is an actual open subscheme. -/
instance overlapComposite_isOpenImmersion (H : AffineAtlas A I B) (a b : I) :
    IsOpenImmersion (affineOverlapMap A I a b ≫ H.chart a) := by
  let := H.openImmersion a
  infer_instance

/-- The two literal localization descriptions of an intersection are actually
isomorphic schemes over the blowup, not merely sets of equal cardinality. -/
def overlapIso (H : AffineAtlas A I B) (a b : I) :
    Spec (.of (Localization.Away (ratio A I a b))) ≅
      Spec (.of (Localization.Away (ratio A I b a))) :=
  IsOpenImmersion.isoOfRangeEq
    (affineOverlapMap A I a b ≫ H.chart a)
    (affineOverlapMap A I b a ≫ H.chart b)
    (by rw [H.overlap, H.overlap, Set.inter_comm])

@[reassoc (attr := simp)] theorem overlapIso_hom_triangle
    (H : AffineAtlas A I B) (a b : I) :
    (H.overlapIso a b).hom ≫ affineOverlapMap A I b a ≫ H.chart b =
      affineOverlapMap A I a b ≫ H.chart a :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)] theorem overlapIso_inv_triangle
    (H : AffineAtlas A I B) (a b : I) :
    (H.overlapIso a b).inv ≫ affineOverlapMap A I a b ≫ H.chart a =
      affineOverlapMap A I b a ≫ H.chart b :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

private theorem range_comp {V W Z : Scheme.{u}} (f : V ⟶ W) (g : W ⟶ Z) :
    Set.range (f ≫ g) = g '' Set.range f := by
  change Set.range (g ∘ f) = _
  exact Set.range_comp _ _

/-- Transport of the literal charts along the unique comparison over the base.
All chart domains and all overlap-localization maps are preserved literally. -/
def transport (H : AffineAtlas A I B) (C : BlowupDatum (affineCenter A I)) :
    AffineAtlas A I C where
  chart a := H.chart a ≫ (B.comparisonIso C).hom
  openImmersion a := by
    let := H.openImmersion a
    infer_instance
  triangle a := by simp only [Category.assoc, BlowupDatum.comparisonIso_hom_map, H.triangle]
  covers y := by
    obtain ⟨x, hx⟩ := (Scheme.homeoOfIso (B.comparisonIso C)).surjective y
    obtain ⟨a, w, hw⟩ := H.covers x
    refine ⟨a, w, ?_⟩
    change (B.comparisonIso C).hom (H.chart a w) = y
    rw [hw]
    exact hx
  overlap a b := by
    rw [← Category.assoc, range_comp, H.overlap, range_comp, range_comp]
    exact Set.image_inter (Scheme.homeoOfIso (B.comparisonIso C)).injective

@[simp] theorem transport_chart (H : AffineAtlas A I B)
    (C : BlowupDatum (affineCenter A I)) (a : I) :
    (H.transport C).chart a = H.chart a ≫ (B.comparisonIso C).hom := rfl

/-- The transported chart's triangle with the original chart is the actual
unique isomorphism between the two blowup representatives. -/
@[reassoc] theorem transport_chart_inv (H : AffineAtlas A I B)
    (C : BlowupDatum (affineCenter A I)) (a : I) :
    (H.transport C).chart a ≫ (B.comparisonIso C).inv = H.chart a := by
  simp [transport_chart]

theorem transport_chart_refl (H : AffineAtlas A I B) (a : I) :
    (H.transport B).chart a = H.chart a := by simp

theorem transport_chart_trans (H : AffineAtlas A I B)
    (C D : BlowupDatum (affineCenter A I)) (a : I) :
    ((H.transport C).transport D).chart a = (H.transport D).chart a := by
  simp only [transport_chart, Category.assoc]
  rw [← Iso.trans_hom, BlowupDatum.comparisonIso_trans]

/-- A canonical atlas for one representative supplies one for every universal
representative, without requiring a second atlas theorem. -/
theorem nonempty_iff (B C : BlowupDatum (affineCenter A I)) :
    Nonempty (AffineAtlas A I B) ↔ Nonempty (AffineAtlas A I C) := by
  constructor
  · rintro ⟨H⟩; exact ⟨H.transport C⟩
  · rintro ⟨H⟩; exact ⟨H.transport B⟩

end AffineAtlas

/-- Candidate: existence for actual quasi-coherent ideals on locally Noetherian
schemes. Sources: Stacks 01OF and 0806. -/
def NoetherianBlowupExistence : Prop :=
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] (I : X.IdealSheafData),
    Nonempty (BlowupDatum I)

/-- Candidate: local Noetherianity gives finite type; Stacks 02NS gives
projectivity, hence properness. General uniqueness transfers the property. -/
def NoetherianBlowupProper : Prop :=
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] (I : X.IdealSheafData)
    (B : BlowupDatum I), IsProper B.map

/-- Candidate: actual cartesian comparison for arbitrary flat maps, 0805. -/
def BlowupFlatBaseChange : Prop :=
  ∀ (X X' : Scheme.{u}) (f : X' ⟶ X), Flat f →
    ∀ (I : X.IdealSheafData) (B : BlowupDatum I) (B' : BlowupDatum (I.comap f)),
      ∃ g : B'.Y ⟶ B.Y, IsPullback g B'.map B.map f

/-- Candidate: the ordinary saturated Rees affine atlas, 0804 and 052Q,
including the standard Proj basic-open intersection identity. -/
def BlowupAffineAtlas : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (B : BlowupDatum (affineCenter A I)), Nonempty (AffineAtlas A I B)

end AlgebraicGeometry.Scheme.Blowup

end
end AlgebraicGeometry.Scheme.Blowup

section BlowupAwayCentre


noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Hom
namespace AlgebraicGeometry.Scheme.Blowup
variable {X Y : Scheme.{u}}

lemma structureModuleMap_eq_zero_of_isEmpty (f : Y ⟶ X) [IsEmpty Y] :
    AlgebraicGeometry.Scheme.Hom.structureModuleMap f = 0 := by
  ext U x
  change f.app U x = 0
  have hU : f ⁻¹ᵁ U = ⊥ := by ext y; exact isEmptyElim y
  let : Subsingleton Γ(Y, f ⁻¹ᵁ U) := by rw [hU]; infer_instance
  exact Subsingleton.elim _ _

lemma idealModule_top_rankOne (X : Scheme.{u}) :
    IsLocallyRankOne X (idealModule (⊤ : X.IdealSheafData).subschemeι) := by
  have hz := structureModuleMap_eq_zero_of_isEmpty (⊤ : X.IdealSheafData).subschemeι
  apply isLocallyRankOne_of_iso X ((kernelIsoOfEq hz) ≪≫ kernelZeroIsoSource).symm
  rw [isLocallyRankOne_iff_local_unit]
  intro x
  exact ⟨⊤, trivial, ⟨Iso.refl _⟩⟩

lemma cartier_of_comap_eq_top (I : X.IdealSheafData) (f : Y ⟶ X)
    (h : I.comap f = ⊤) : cartierPullback I f := by
  unfold cartierPullback
  rw [h]
  exact idealModule_top_rankOne Y

namespace BlowupDatum
variable {I : X.IdealSheafData} (B : BlowupDatum I)

/-- A base change whose actual centre ideal is the unit ideal has trivial
blowup, proved directly from the universal property without a base-change family. -/
def awayPullbackIso (j : Y ⟶ X) (hI : I.comap j = ⊤) : pullback B.map j ≅ Y where
  hom := pullback.snd B.map j
  inv := pullback.lift (B.lift j (cartier_of_comap_eq_top I j hI)) (𝟙 Y) (by simp)
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      apply B.hom_ext (f := pullback.fst B.map j ≫ B.map)
        (cartier_of_comap_eq_top I _ (by
          rw [pullback.condition, Scheme.IdealSheafData.comap_comp, hI,
            Scheme.IdealSheafData.comap_top]))
      · simp only [Category.assoc, B.lift_map, ← pullback.condition]
      · simp
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  inv_hom_id := pullback.lift_snd _ _ _

lemma pullback_snd_isIso_of_comap_eq_top (j : Y ⟶ X) (hI : I.comap j = ⊤) :
    IsIso (pullback.snd B.map j) := (awayPullbackIso B j hI).isIso_hom

lemma comap_eq_top_of_disjoint (U : X.Opens)
    (hU : Disjoint (U : Set X) (I.support : Set X)) : I.comap U.ι = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [Scheme.IdealSheafData.support_comap]
  ext x
  change (x.val ∈ (I.support : Set X)) ↔ False
  exact iff_false_intro (fun hx => Set.disjoint_left.mp hU x.property hx)

lemma restrict_isIso_of_disjoint (U : X.Opens)
    (hU : Disjoint (U : Set X) (I.support : Set X)) : IsIso (B.map ∣_ U) := by
  have hc := comap_eq_top_of_disjoint (I := I) U hU
  let e := awayPullbackIso B U.ι hc
  let : IsIso (pullback.snd B.map U.ι) := e.isIso_hom
  rw [← (isPullback_morphismRestrict B.map U).flip.isoPullback_hom_snd]
  infer_instance

end BlowupDatum
end AlgebraicGeometry.Scheme.Blowup

end
end BlowupAwayCentre
