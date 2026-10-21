/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.IsIso.BaseChangeRestriction
public import Aglib.AlgebraicGeometry.Limits.Range
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.ReducedFactor
public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.FlatOpenBaseChange
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.ExceptionalComparison
public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.StrictTransformClosure`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`5933a29200aaaa2ea2da9f33a05e06372d03ad6b9c19af9a44048bd25fe432c2`.
Source198–536 only: literal cross/outer punctured-branch images, endpoints, flat pullback
  comparisons and exact ranges. Original Weierstrass specialization remains separately selected
  pending actual base-change suppliers.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode
open AlgebraicGeometry.Scheme.Hom.Range AlgebraicGeometry.Scheme.Pullback.Fibre

section CrossStrictClosure

/-! The surviving branch of the literal cross is the scheme-theoretic
closure of its punctured open. This computes the actual defining kernel;
neither a component identification nor a fibre classification is an input. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open PlaneNode _root_.PowerNode.Rees
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution.Cross
variable (k : Type u) [Field k]

/-- The affine line with its coordinate inverted, viewed as a scheme. -/
abbrev puncturedLine : Scheme.{u} := Spec (.of (Localization.Away (Polynomial.X : k[X])))
instance puncturedLine_integral : IsIntegral (puncturedLine k) := by
  let : IsDomain (Localization.Away (Polynomial.X : k[X])) := Localization.Away.isDomain
    Polynomial.X_ne_zero
  infer_instance

/-- The localization morphism from the punctured affine line to the affine line. -/
def puncturedToLine : puncturedLine k ⟶ line k :=
  Spec.map (CommRingCat.ofHom (algebraMap k[X] (Localization.Away (Polynomial.X : k[X]))))
instance puncturedToLine_open : IsOpenImmersion (puncturedToLine k) :=
  IsOpenImmersion.of_isLocalization (Polynomial.X : k[X])

/-- The original U branch with its original zero removed. -/
def puncturedLeft : puncturedLine k ⟶ scheme k := puncturedToLine k ≫ left k

lemma puncturedLeft_eq : puncturedLeft k =
    (Scheme.Spec.mapIso (PlaneNode.Regularity.nodeAwayLaurent (0 :
      k)).toRingEquiv.toCommRingCatIso.op).hom ≫
      AlgebraicGeometry.Scheme.Blowup.Coordinates.awayMap (PlaneNode.U (0 : k)) := by
  change Spec.map (CommRingCat.ofHom (algebraMap k[X] (Localization.Away (Polynomial.X : k[X])))) ≫
    Spec.map (CommRingCat.ofHom (leftHom k).toRingHom) =
    Spec.map (CommRingCat.ofHom (PlaneNode.Regularity.nodeAwayLaurent (0 : k)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (ring k) (Localization.Away (PlaneNode.U (0 : k)))))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  have H : (IsScalarTower.toAlgHom k k[X] (Localization.Away (Polynomial.X : k[X]))).comp (leftHom
    k) =
      (PlaneNode.Regularity.nodeAwayLaurent (0 : k)).toAlgHom.comp
        (IsScalarTower.toAlgHom k (ring k) (Localization.Away (PlaneNode.U (0 : k)))) := by
    apply PlaneNode.hom_ext <;>
      simp [leftHom, PlaneNode.Regularity.nodeAwayLaurent, PlaneNode.Regularity.awayToLaurent_base]
  exact congrArg AlgHom.toRingHom H

instance puncturedLeft_open : IsOpenImmersion (puncturedLeft k) := by
  rw [puncturedLeft_eq]
  infer_instance

instance puncturedToLine_schemeDominant : IsSchemeTheoreticallyDominant (puncturedToLine k) := by
  let : IsDominant (puncturedToLine k) := Scheme.isDominant_of_isOpenImmersion _
  exact IsSchemeTheoreticallyDominant.of_isDominant _

/-- The literal punctured-open kernel is the literal coordinate branch
kernel, retaining the reduced scheme structure of the affine line. -/
lemma puncturedLeft_kernel : (puncturedLeft k).ker = (left k).ker := by
  rw [puncturedLeft, Scheme.Hom.ker_comp,
    Scheme.Hom.ker_eq_bot, Scheme.IdealSheafData.map_bot]

/-- Constructed isomorphism from the actual closure, not a supplied iso. -/
def strictLeftIso : AlgebraicGeometry.Scheme.Hom.image (puncturedLeft k) ≅ line k := by
  have H : (left k).ker = (AlgebraicGeometry.Scheme.Hom.imageι (puncturedLeft k)).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, puncturedLeft_kernel]
  let l := IsClosedImmersion.lift (left k) (AlgebraicGeometry.Scheme.Hom.imageι (puncturedLeft k))
    H.le
  letI : IsIso l := IsClosedImmersion.isIso_lift _ _ H
  exact asIso l

@[reassoc (attr := simp)] lemma strictLeftIso_hom_left :
    (strictLeftIso k).hom ≫ left k = AlgebraicGeometry.Scheme.Hom.imageι (puncturedLeft k) := by
  dsimp only [strictLeftIso, asIso_hom]
  exact IsClosedImmersion.lift_fac ..

@[reassoc (attr := simp)] lemma strictLeftIso_open :
    AlgebraicGeometry.Scheme.Hom.toImage (puncturedLeft k) ≫ (strictLeftIso k).hom =
      puncturedToLine k := by
  apply (cancel_mono (left k)).mp
  simp [puncturedLeft]

/-- The endpoint in this constructed closure is exactly the original
coordinate endpoint, transported through the constructed comparison. -/
def strictLeftEndpoint : Spec (.of k) ⟶ AlgebraicGeometry.Scheme.Hom.image (puncturedLeft k) :=
  endpoint k ≫ (strictLeftIso k).inv

@[reassoc (attr := simp)] lemma strictLeftEndpoint_original :
    strictLeftEndpoint k ≫ (strictLeftIso k).hom = endpoint k := by simp [strictLeftEndpoint]

@[reassoc] lemma strictLeftEndpoint_cross :
    strictLeftEndpoint k ≫ AlgebraicGeometry.Scheme.Hom.imageι (puncturedLeft k) = origin k := by
  rw [← strictLeftIso_hom_left, ← Category.assoc, strictLeftEndpoint_original, left_endpoint]

variable {Z : Scheme.{u}} (t : Z ⟶ scheme k) [Flat t]

/-- In any actual flat chart, the closure of the pulled-back punctured
U branch is its full scheme-theoretic branch pullback. The source of that
pullback is not assumed integral, connected, or an affine line. -/
def flatStrictLeftIso : (pullback.snd (puncturedLeft k) t).image ≅ pullback t (left k) :=
  AlgebraicGeometry.Scheme.Hom.Image.flatBaseChangeIso (puncturedLeft k) t ≪≫
    asIso (pullback.map _ _ _ _ (strictLeftIso k).hom (𝟙 _) (𝟙 _)
      (by simp) (by simp)) ≪≫
    pullbackSymmetry (left k) t

@[reassoc (attr := simp)] lemma flatStrictLeftIso_hom_fst :
    (flatStrictLeftIso k t).hom ≫ pullback.fst t (left k) =
      (pullback.snd (puncturedLeft k) t).imageι := by
  simp [flatStrictLeftIso]

/-- The identification retains the literal map to the original U branch. -/
@[reassoc] lemma flatStrictLeftIso_open_snd :
    (pullback.snd (puncturedLeft k) t).toImage ≫
      (flatStrictLeftIso k t).hom ≫ pullback.snd t (left k) =
        pullback.fst (puncturedLeft k) t ≫ puncturedToLine k := by
  simp [flatStrictLeftIso]

end AlgebraicGeometry.Scheme.PowerNode.Resolution.Cross

end -- noncomputable section
end CrossStrictClosure

section OuterStrictClosure

/-! The actual strict branch in each outer chart of the exponent-reducing
blowup is the actual punctured-open closure, including after full flat common
chart pullback. The same endpoint and outer-fibre maps are retained. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open PlaneNode _root_.PowerNode.Rees
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {π : R} (hπ : Irreducible π)
local notation "k" => IsLocalRing.ResidueField R

/-- The punctured surviving branch inside the literal outer special fibre. -/
def outerStrictPuncture : Cross.puncturedLine k ⟶ outerFibre (π := π) :=
  Cross.puncturedToLine k ≫ outerEndBranch hπ

lemma outerStrictPuncture_eq : outerStrictPuncture hπ =
    Cross.puncturedLeft k ≫ (outerCrossIso hπ).hom := by
  simp only [outerStrictPuncture, outerEndBranch_eq, Cross.puncturedLeft, Category.assoc]

instance outerStrictPuncture_open : IsOpenImmersion (outerStrictPuncture hπ) := by
  rw [outerStrictPuncture_eq]
  infer_instance

lemma outerStrictPuncture_kernel : (outerStrictPuncture hπ).ker = (outerEndBranch hπ).ker := by
  rw [outerStrictPuncture, Scheme.Hom.ker_comp,
    Scheme.Hom.ker_eq_bot, Scheme.IdealSheafData.map_bot]

/-- The original affine-line branch is isomorphic to the genuinely
constructed scheme-theoretic closure in the actual residue outer chart. -/
def outerStrictClosureIso : AlgebraicGeometry.Scheme.Hom.image (outerStrictPuncture hπ) ≅
  Cross.line k := by
  have H : (outerEndBranch hπ).ker =
      (AlgebraicGeometry.Scheme.Hom.imageι (outerStrictPuncture hπ)).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, outerStrictPuncture_kernel]
  let l := IsClosedImmersion.lift (outerEndBranch hπ)
    (AlgebraicGeometry.Scheme.Hom.imageι (outerStrictPuncture hπ)) H.le
  letI : IsIso l := IsClosedImmersion.isIso_lift _ _ H
  exact asIso l

@[reassoc (attr := simp)] lemma outerStrictClosureIso_hom_branch :
    (outerStrictClosureIso hπ).hom ≫ outerEndBranch hπ =
      AlgebraicGeometry.Scheme.Hom.imageι (outerStrictPuncture hπ) := by
  dsimp only [outerStrictClosureIso, asIso_hom]
  exact IsClosedImmersion.lift_fac ..

@[reassoc (attr := simp)] lemma outerStrictClosureIso_open :
    AlgebraicGeometry.Scheme.Hom.toImage (outerStrictPuncture hπ) ≫ (outerStrictClosureIso hπ).hom =
      Cross.puncturedToLine k := by
  apply (cancel_mono (outerEndBranch hπ)).mp
  simp [outerStrictPuncture]

/-- This is the transported original coordinate endpoint, not a new point. -/
def outerStrictEndpoint : Spec (.of k) ⟶
    AlgebraicGeometry.Scheme.Hom.image (outerStrictPuncture hπ) :=
  Cross.endpoint k ≫ (outerStrictClosureIso hπ).inv

@[reassoc (attr := simp)] lemma outerStrictEndpoint_original :
    outerStrictEndpoint hπ ≫ (outerStrictClosureIso hπ).hom = Cross.endpoint k := by
  simp [outerStrictEndpoint]

@[reassoc] lemma outerStrictEndpoint_outer :
    outerStrictEndpoint hπ ≫ AlgebraicGeometry.Scheme.Hom.imageι (outerStrictPuncture hπ) =
      outerNode hπ := by
  rw [← outerStrictClosureIso_hom_branch, ← Category.assoc,
    outerStrictEndpoint_original, outerEndBranch_endpoint]

variable {Z : Scheme.{u}} (t : Z ⟶ outerFibre (π := π)) [Flat t]

/-- The full common-chart strict branch pullback, with its exact scheme
structure, is the image of the literal pulled-back punctured branch. -/
def flatOuterStrictClosureIso :
    (pullback.snd (outerStrictPuncture hπ) t).image ≅ pullback t (outerEndBranch hπ) :=
  AlgebraicGeometry.Scheme.Hom.Image.flatBaseChangeIso (outerStrictPuncture hπ) t ≪≫
    asIso (pullback.map _ _ _ _ (outerStrictClosureIso hπ).hom (𝟙 _) (𝟙 _)
      (by simp) (by simp)) ≪≫
    pullbackSymmetry (outerEndBranch hπ) t

@[reassoc (attr := simp)] lemma flatOuterStrictClosureIso_hom_fst :
    (flatOuterStrictClosureIso hπ t).hom ≫ pullback.fst t (outerEndBranch hπ) =
      (pullback.snd (outerStrictPuncture hπ) t).imageι := by
  simp [flatOuterStrictClosureIso]

@[reassoc] lemma flatOuterStrictClosureIso_open_snd :
    (pullback.snd (outerStrictPuncture hπ) t).toImage ≫
      (flatOuterStrictClosureIso hπ t).hom ≫ pullback.snd t (outerEndBranch hπ) =
        pullback.fst (outerStrictPuncture hπ) t ≫ Cross.puncturedToLine k := by
  simp [flatOuterStrictClosureIso]

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end OuterStrictClosure

section OuterPunctureRange

/-! The literal original-node complement pulls back to the precise D(U)
strict puncture on BOTH first outer residue charts. This computes the open
range needed for the actual closure comparison, before any global cover. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
universe u
namespace AlgebraicGeometry

end AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution.Cross
variable (k : Type u) [Field k]

lemma puncturedLeft_range : Set.range (puncturedLeft k) =
    (PrimeSpectrum.basicOpen (PlaneNode.U (0 : k))).carrier := by
  rw [puncturedLeft_eq, AlgebraicGeometry.Scheme.Hom.Range.range_iso_comp]
  exact PrimeSpectrum.localization_away_comap_range _ _

end AlgebraicGeometry.Scheme.PowerNode.Resolution.Cross
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {π : R} (hπ : Irreducible π) (m : ℕ)
local notation "k" => ResidueField R

/-- Original node coordinates on the actual first left residue chart. -/
def outerLeftOriginal : outerFibre (π := π) ⟶ Spec (.of (node π (m + 2))) :=
  pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π))))
    (residueBase (R := R)) ≫ Spec.map (CommRingCat.ofHom (leftBase π m).toRingHom)

/-- Original node coordinates on the actual first right residue chart. -/
def outerRightOriginal : outerFibre (π := π) ⟶ Spec (.of (node π (m + 2))) :=
  pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π))))
    (residueBase (R := R)) ≫ Spec.map (CommRingCat.ofHom (rightBase π m).toRingHom)

lemma origin_range_coordinates (n : ℕ) (hn : 0 < n) :
    Set.range (NextCenter.origin π hπ n hn) =
      {p | PlaneNode.U (π^n) ∈ p.asIdeal ∧ PlaneNode.V (π^n) ∈ p.asIdeal ∧
        algebraMap R (node π n) π ∈ p.asIdeal} := by
  change Set.range (PrimeSpectrum.comap
    (PlaneNode.residueMap (π^n) (IsDiscreteValuationRing.power_residue_zero π hπ n hn)).toRingHom)
      = _
  rw [range_comap_of_surjective _ _
    (PlaneNode.residueMap_surjective _ _),
    ← PlaneNode.residueCenter_eq_ker,
    PlaneNode.residueCenter_eq_uniformizer_span (π ^ n) π hπ]
  ext p
  change Ideal.span {algebraMap R (node π n) π, PlaneNode.U (π ^ n),
    PlaneNode.V (π ^ n)} ≤ p.asIdeal ↔ _
  rw [Ideal.span_le]
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
  change (algebraMap R (node π n) π ∈ p.asIdeal ∧ PlaneNode.U (π ^ n) ∈ p.asIdeal ∧
    PlaneNode.V (π ^ n) ∈ p.asIdeal) ↔
    (PlaneNode.U (π ^ n) ∈ p.asIdeal ∧ PlaneNode.V (π ^ n) ∈ p.asIdeal ∧
      algebraMap R (node π n) π ∈ p.asIdeal)
  constructor
  · rintro ⟨hScalar, hU, hV⟩
    exact ⟨hU, hV, hScalar⟩
  · rintro ⟨hU, hV, hScalar⟩
    exact ⟨hScalar, hU, hV⟩

lemma cross_left_original_origin_iff (z : Cross.scheme k) :
    (outerCrossIso hπ).hom z ∈ outerLeftOriginal (π := π) m ⁻¹'
      Set.range (NextCenter.origin π hπ (m + 2) (by omega)) ↔
        PlaneNode.U (0 : k) ∈ z.asIdeal := by
  change ((outerCrossIso hπ).hom ≫ outerLeftOriginal (π := π) m) z ∈
    Set.range (NextCenter.origin π hπ (m + 2) (by omega)) ↔ PlaneNode.U (0 : k) ∈ z.asIdeal
  rw [outerLeftOriginal, outerCrossIso_hom_fst_assoc, ← Spec.map_comp,
    origin_range_coordinates]
  change ((nodeSpecializeAt π (0 : k) (residue_uniformizer hπ)).comp (leftBase π m))
      (PlaneNode.U (π^(m + 2))) ∈ z.asIdeal ∧
    ((nodeSpecializeAt π (0 : k) (residue_uniformizer hπ)).comp (leftBase π m))
      (PlaneNode.V (π^(m + 2))) ∈ z.asIdeal ∧
    ((nodeSpecializeAt π (0 : k) (residue_uniformizer hπ)).comp (leftBase π m))
      (algebraMap R _ π) ∈ z.asIdeal ↔ _
  simp [leftBase, nodeSpecializeAt, IsScalarTower.algebraMap_apply R k (Cross.ring k),
    IsDiscreteValuationRing.uniformizer_residue_zero π hπ]

lemma cross_right_original_origin_iff (z : Cross.scheme k) :
    (outerCrossIso hπ).hom z ∈ outerRightOriginal (π := π) m ⁻¹'
      Set.range (NextCenter.origin π hπ (m + 2) (by omega)) ↔
        PlaneNode.U (0 : k) ∈ z.asIdeal := by
  change ((outerCrossIso hπ).hom ≫ outerRightOriginal (π := π) m) z ∈
    Set.range (NextCenter.origin π hπ (m + 2) (by omega)) ↔ PlaneNode.U (0 : k) ∈ z.asIdeal
  rw [outerRightOriginal, outerCrossIso_hom_fst_assoc, ← Spec.map_comp,
    origin_range_coordinates]
  change ((nodeSpecializeAt π (0 : k) (residue_uniformizer hπ)).comp (rightBase π m))
      (PlaneNode.U (π^(m + 2))) ∈ z.asIdeal ∧
    ((nodeSpecializeAt π (0 : k) (residue_uniformizer hπ)).comp (rightBase π m))
      (PlaneNode.V (π^(m + 2))) ∈ z.asIdeal ∧
    ((nodeSpecializeAt π (0 : k) (residue_uniformizer hπ)).comp (rightBase π m))
      (algebraMap R _ π) ∈ z.asIdeal ↔ _
  simp [AlgHom.comp_apply, rightBase_u, rightBase_v, nodeSpecializeAt,
    IsScalarTower.algebraMap_apply R k (Cross.ring k),
    IsDiscreteValuationRing.uniformizer_residue_zero π hπ]

lemma outerStrictPuncture_mem_cross (z : Cross.scheme k) :
    (outerCrossIso hπ).hom z ∈ Set.range (outerStrictPuncture hπ) ↔
      PlaneNode.U (0 : k) ∉ z.asIdeal := by
  rw [outerStrictPuncture_eq]
  rw [map_mem_range_comp_iff _ _ (outerCrossIso hπ).hom.injective,
    Cross.puncturedLeft_range]
  rfl

/-- Exact open range on the left, with the original point and coordinate maps. -/
lemma outerLeftOriginal_puncture_range :
    Set.range (outerStrictPuncture hπ) = outerLeftOriginal (π := π) m ⁻¹'
      (Set.range (NextCenter.origin π hπ (m + 2) (by omega)))ᶜ := by
  ext z
  obtain ⟨q, rfl⟩ := (outerCrossIso hπ).hom.surjective z
  rw [outerStrictPuncture_mem_cross]
  exact not_congr (cross_left_original_origin_iff hπ m q).symm

/-- Exact open range on the right, preserving its distinct original map. -/
lemma outerRightOriginal_puncture_range :
    Set.range (outerStrictPuncture hπ) = outerRightOriginal (π := π) m ⁻¹'
      (Set.range (NextCenter.origin π hπ (m + 2) (by omega)))ᶜ := by
  ext z
  obtain ⟨q, rfl⟩ := (outerCrossIso hπ).hom.surjective z
  rw [outerStrictPuncture_mem_cross]
  exact not_congr (cross_right_original_origin_iff hπ m q).symm

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end OuterPunctureRange
