/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.ProjectiveComponents

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.RecursiveComponents`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`8aa84ab8293d92b462026eda83ef872797d0a8aa43019a9cb5478035336dc5d5`.
Original objects, maps, quantifiers and mathematical hypotheses are retained.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode
open AlgebraicGeometry.Scheme.Hom.Range AlgebraicGeometry.Scheme.Pullback.Fibre

/-!
# Recursive component maps, exponent-two geometry, and contraction

This module preserves the conditional interfaces and source-coverage boundaries
recorded in the individual sections below.
-/

section NodeResolutionEndMaps

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (π : R) (hπ : Irreducible π)
local notation "k" => IsLocalRing.ResidueField R

lemma residue_branch_base (c : R) (_hc : algebraMap R k c = 0)
    (f : PlaneNode.Ring c →ₐ[R] k[X]) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring c))) =
        Spec.map (CommRingCat.ofHom (algebraMap k k[X])) ≫ residueBase := by
  rw [Spec.map_algHom_algebraMap, residueBase, ← Spec.map_comp]
  rfl

/-- Literal exponent-one end maps into the identity resolution's own pullback. -/
def baseLeftEnd : Cross.line k ⟶ sourceSpecialFibre (one π hπ) :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom (residueLeftHom (π ^ 1) (residue_uniformizer_pow hπ 0)).toRingHom))
    (Spec.map (CommRingCat.ofHom (algebraMap k k[X]))) (by
      change _ ≫ (𝟙 _ ≫ base) = _
      rw [Category.id_comp]
      exact residue_branch_base (π ^ 1) (residue_uniformizer_pow hπ 0) _)

/-- The right residue-field affine branch in the exponent-one special fibre. -/
def baseRightEnd : Cross.line k ⟶ sourceSpecialFibre (one π hπ) :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom
      (residueRightHom (π ^ 1) (residue_uniformizer_pow hπ 0)).toRingHom))
    (Spec.map (CommRingCat.ofHom (algebraMap k k[X]))) (by
      change _ ≫ (𝟙 _ ≫ base) = _
      rw [Category.id_comp]
      exact residue_branch_base (π ^ 1) (residue_uniformizer_pow hπ 0) _)

@[reassoc] lemma baseLeftEnd_target :
    baseLeftEnd π hπ ≫ pullback.fst ((one π hπ).map ≫ base) residueBase ≫ (one π hπ).map =
      Spec.map (CommRingCat.ofHom (residueLeftHom (π ^ 1) (residue_uniformizer_pow hπ 0)).toRingHom)
        := by
  rw [baseLeftEnd, pullback.lift_fst_assoc]
  exact Category.comp_id _
@[reassoc] lemma baseRightEnd_target :
    baseRightEnd π hπ ≫ pullback.fst ((one π hπ).map ≫ base) residueBase ≫ (one π hπ).map =
      Spec.map (CommRingCat.ofHom (residueRightHom (π ^ 1) (residue_uniformizer_pow hπ
        0)).toRingHom) := by
  rw [baseRightEnd, pullback.lift_fst_assoc]
  exact Category.comp_id _

@[reassoc] lemma baseLeftEnd_base :
    baseLeftEnd π hπ ≫ pullback.snd ((one π hπ).map ≫ base) residueBase =
      Spec.map (CommRingCat.ofHom (algebraMap k k[X])) := pullback.lift_snd ..
@[reassoc] lemma baseRightEnd_base :
    baseRightEnd π hπ ≫ pullback.snd ((one π hπ).map ≫ base) residueBase =
      Spec.map (CommRingCat.ofHom (algebraMap k k[X])) := pullback.lift_snd ..

instance baseLeftEnd_closedImmersion : IsClosedImmersion (baseLeftEnd π hπ) := by
  let q := pullback.fst ((one π hπ).map ≫ base) residueBase ≫ (one π hπ).map
  let : IsClosedImmersion (baseLeftEnd π hπ ≫ q) := by
    dsimp [q]
    rw [baseLeftEnd_target]
    exact IsClosedImmersion.spec_of_surjective _
      (residueLeftHom_surjective _ (residue_uniformizer_pow hπ 0))
  exact IsClosedImmersion.of_comp (baseLeftEnd π hπ) q
instance baseRightEnd_closedImmersion : IsClosedImmersion (baseRightEnd π hπ) := by
  let q := pullback.fst ((one π hπ).map ≫ base) residueBase ≫ (one π hπ).map
  let : IsClosedImmersion (baseRightEnd π hπ ≫ q) := by
    dsimp [q]
    rw [baseRightEnd_target]
    exact IsClosedImmersion.spec_of_surjective _
      (residueRightHom_surjective _ (residue_uniformizer_pow hπ 0))
  exact IsClosedImmersion.of_comp (baseRightEnd π hπ) q

variable (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (ha : BlowupAffineAtlas.{u})

/-- Actual A1 end morphisms for every positive exponent of the same resolve object. -/
def resolveLeftEnd : (n : ℕ) → Cross.line k ⟶ sourceSpecialFibre (resolve π hπ hex hp ha (n + 1))
  | 0 => baseLeftEnd π hπ
  | m + 1 => stepLeftEnd hπ (OneStepBlowup.ofFamilies π m hex hp ha) (resolve π hπ hex hp ha m)
/-- The right affine end of the recursively resolved special fibre, using the base branch or the
right outer chart. -/
def resolveRightEnd : (n : ℕ) → Cross.line k ⟶ sourceSpecialFibre (resolve π hπ hex hp ha (n + 1))
  | 0 => baseRightEnd π hπ
  | m + 1 => stepRightEnd hπ (OneStepBlowup.ofFamilies π m hex hp ha) (resolve π hπ hex hp ha m)

lemma resolveLeftEnd_target (n : ℕ) :
    resolveLeftEnd π hπ hex hp ha n ≫
      pullback.fst ((resolve π hπ hex hp ha (n + 1)).map ≫ base) residueBase ≫
        (resolve π hπ hex hp ha (n + 1)).map =
      Spec.map (CommRingCat.ofHom (residueLeftHom (π ^ (n + 1)) (residue_uniformizer_pow hπ
        n)).toRingHom) := by
  cases n with
  | zero => exact baseLeftEnd_target π hπ
  | succ m => exact stepLeftEnd_target_triangle hπ _ _
lemma resolveRightEnd_target (n : ℕ) :
    resolveRightEnd π hπ hex hp ha n ≫
      pullback.fst ((resolve π hπ hex hp ha (n + 1)).map ≫ base) residueBase ≫
        (resolve π hπ hex hp ha (n + 1)).map =
      Spec.map (CommRingCat.ofHom (residueRightHom (π ^ (n + 1)) (residue_uniformizer_pow hπ
        n)).toRingHom) := by
  cases n with
  | zero => exact baseRightEnd_target π hπ
  | succ m => exact stepRightEnd_target_triangle hπ _ _

lemma resolveLeftEnd_base (n : ℕ) :
    resolveLeftEnd π hπ hex hp ha n ≫
      pullback.snd ((resolve π hπ hex hp ha (n + 1)).map ≫ base) residueBase =
        Spec.map (CommRingCat.ofHom (algebraMap k k[X])) := by
  cases n with
  | zero => exact baseLeftEnd_base π hπ
  | succ m => exact stepLeftEnd_base hπ _ _
lemma resolveRightEnd_base (n : ℕ) :
    resolveRightEnd π hπ hex hp ha n ≫
      pullback.snd ((resolve π hπ hex hp ha (n + 1)).map ≫ base) residueBase =
        Spec.map (CommRingCat.ofHom (algebraMap k k[X])) := by
  cases n with
  | zero => exact baseRightEnd_base π hπ
  | succ m => exact stepRightEnd_base hπ _ _

instance resolveLeftEnd_closedImmersion (n : ℕ) :
    IsClosedImmersion (resolveLeftEnd π hπ hex hp ha n) := by
  cases n with
  | zero => exact baseLeftEnd_closedImmersion π hπ
  | succ m => exact stepLeftEnd_closedImmersion hπ _ _
instance resolveRightEnd_closedImmersion (n : ℕ) :
    IsClosedImmersion (resolveRightEnd π hπ hex hp ha n) := by
  cases n with
  | zero => exact baseRightEnd_closedImmersion π hπ
  | succ m => exact stepRightEnd_closedImmersion hπ _ _

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeResolutionEndMaps


section NodeRecursiveComponentMaps

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (π : R) (hπ : Irreducible π)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (ha : BlowupAffineAtlas.{u}) (m : ℕ)
local notation "k" => IsLocalRing.ResidueField R

/-- The actual new left projective component at every positive-middle recursive step. -/
def resolveLeftNewP1 : projectiveP1 k ⟶ sourceSpecialFibre (resolve π hπ hex hp ha (m + 3)) :=
  stepLeftCompactification hπ m (OneStepBlowup.ofFamilies π (m + 1) hex hp ha)
    (resolve π hπ hex hp ha (m + 1)) (resolveLeftEnd π hπ hex hp ha m)
    (resolveLeftEnd_target π hπ hex hp ha m) (resolveLeftEnd_base π hπ hex hp ha m)

/-- The actual new right projective component, with the same original resolution object. -/
def resolveRightNewP1 : projectiveP1 k ⟶ sourceSpecialFibre (resolve π hπ hex hp ha (m + 3)) :=
  stepRightCompactification hπ m (OneStepBlowup.ofFamilies π (m + 1) hex hp ha)
    (resolve π hπ hex hp ha (m + 1)) (resolveRightEnd π hπ hex hp ha m)
    (resolveRightEnd_target π hπ hex hp ha m) (resolveRightEnd_base π hπ hex hp ha m)

@[reassoc] lemma resolveLeftNewP1_base :
    resolveLeftNewP1 π hπ hex hp ha m ≫
      pullback.snd ((resolve π hπ hex hp ha (m + 3)).map ≫ base) residueBase = structureMap k :=
  stepLeftCompactification_base ..
@[reassoc] lemma resolveRightNewP1_base :
    resolveRightNewP1 π hπ hex hp ha m ≫
      pullback.snd ((resolve π hπ hex hp ha (m + 3)).map ≫ base) residueBase = structureMap k :=
  stepRightCompactification_base ..

@[reassoc] lemma resolveLeftNewP1_old_chart :
    chart k 0 ≫ resolveLeftNewP1 π hπ hex hp ha m =
      resolveLeftEnd π hπ hex hp ha m ≫
        middleFibreChart (OneStepBlowup.ofFamilies π (m + 1) hex hp ha) hπ
          (resolve π hπ hex hp ha (m + 1)) := stepLeftCompactification_zero_chart ..
@[reassoc] lemma resolveRightNewP1_old_chart :
    chart k 0 ≫ resolveRightNewP1 π hπ hex hp ha m =
      resolveRightEnd π hπ hex hp ha m ≫
        middleFibreChart (OneStepBlowup.ofFamilies π (m + 1) hex hp ha) hπ
          (resolve π hπ hex hp ha (m + 1)) := stepRightCompactification_zero_chart ..

@[reassoc] lemma resolveLeftNewP1_new_chart :
    chart k 1 ≫ resolveLeftNewP1 π hπ hex hp ha m =
      outerExceptionalBranch hπ ≫
        leftFibreChart (OneStepBlowup.ofFamilies π (m + 1) hex hp ha) hπ
          (resolve π hπ hex hp ha (m + 1)) := stepLeftCompactification_infinity_chart ..
@[reassoc] lemma resolveRightNewP1_new_chart :
    chart k 1 ≫ resolveRightNewP1 π hπ hex hp ha m =
      outerExceptionalBranch hπ ≫
        rightFibreChart (OneStepBlowup.ofFamilies π (m + 1) hex hp ha) hπ
          (resolve π hπ hex hp ha (m + 1)) := stepRightCompactification_infinity_chart ..

@[reassoc] lemma resolveLeftNewP1_old_endpoint :
    Reciprocal.zeroSection k ≫ resolveLeftNewP1 π hπ hex hp ha m =
      Cross.endpoint k ≫ resolveLeftEnd π hπ hex hp ha m ≫
        middleFibreChart (OneStepBlowup.ofFamilies π (m + 1) hex hp ha) hπ
          (resolve π hπ hex hp ha (m + 1)) := stepLeftCompactification_old_endpoint ..
@[reassoc] lemma resolveRightNewP1_old_endpoint :
    Reciprocal.zeroSection k ≫ resolveRightNewP1 π hπ hex hp ha m =
      Cross.endpoint k ≫ resolveRightEnd π hπ hex hp ha m ≫
        middleFibreChart (OneStepBlowup.ofFamilies π (m + 1) hex hp ha) hπ
          (resolve π hπ hex hp ha (m + 1)) := stepRightCompactification_old_endpoint ..

@[reassoc] lemma resolveLeftNewP1_new_endpoint :
    Reciprocal.infinitySection k ≫ resolveLeftNewP1 π hπ hex hp ha m =
      outerNode hπ ≫
        leftFibreChart (OneStepBlowup.ofFamilies π (m + 1) hex hp ha) hπ
          (resolve π hπ hex hp ha (m + 1)) := stepLeftCompactification_new_endpoint ..
@[reassoc] lemma resolveRightNewP1_new_endpoint :
    Reciprocal.infinitySection k ≫ resolveRightNewP1 π hπ hex hp ha m =
      outerNode hπ ≫
        rightFibreChart (OneStepBlowup.ofFamilies π (m + 1) hex hp ha) hπ
          (resolve π hπ hex hp ha (m + 1)) := stepRightCompactification_new_endpoint ..

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeRecursiveComponentMaps


section NodeRecursiveComponentEmbeddings

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (π : R) (hπ : Irreducible π)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (ha : BlowupAffineAtlas.{u}) (m : ℕ)
local notation "k" => IsLocalRing.ResidueField R


instance resolveLeftNewP1_closedImmersion :
    IsClosedImmersion (resolveLeftNewP1 π hπ hex hp ha m) :=
  stepLeftCompactification_closedImmersion ..

lemma resolveLeftEnd_newP1_isPullback :
    IsPullback (Cross.endpoint k) (Reciprocal.infinitySection k)
      (resolveLeftEnd π hπ hex hp ha (m + 2)) (resolveLeftNewP1 π hπ hex hp ha m) :=
  stepLeftEnd_compactification_isPullback ..

instance resolveRightNewP1_closedImmersion :
    IsClosedImmersion (resolveRightNewP1 π hπ hex hp ha m) :=
  stepRightCompactification_closedImmersion ..

lemma resolveRightEnd_newP1_isPullback :
    IsPullback (Cross.endpoint k) (Reciprocal.infinitySection k)
      (resolveRightEnd π hπ hex hp ha (m + 2)) (resolveRightNewP1 π hπ hex hp ha m) :=
  stepRightEnd_compactification_isPullback ..

/-- A previously constructed projective component stays a closed component after
its inclusion into the recursive middle chart. Properness comes from literal P1. -/
lemma middle_projective_component_closed {n : ℕ} (B : OneStepBlowup.Data π n)
    (E : Data π n) (c : projectiveP1 k ⟶ sourceSpecialFibre E) [IsClosedImmersion c]
    (hc : c ≫ pullback.snd (E.map ≫ base) residueBase = structureMap k) :
    IsClosedImmersion (c ≫ middleFibreChart B hπ E) := by
  let q := pullback.snd ((step B hπ E).map ≫ base) residueBase
  have ho : (c ≫ middleFibreChart B hπ E) ≫ q = structureMap k := by
    simpa only [q, Category.assoc, middleFibreChart_base_triangle] using hc
  have : IsProper ((c ≫ middleFibreChart B hπ E) ≫ q) := by rw [ho]; infer_instance
  have : IsProper (c ≫ middleFibreChart B hπ E) := IsProper.of_comp _ q
  exact IsClosedImmersion.of_isPreimmersion _
    (c ≫ middleFibreChart B hπ E).isClosedMap.isClosed_range

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeRecursiveComponentEmbeddings


section NodeBaseEndGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (π : R) (hπ : Irreducible π)
local notation "k" => IsLocalRing.ResidueField R

@[reassoc] lemma oneSourceTargetIso_inv_fst :
    (oneSourceTargetIso π hπ).inv ≫ pullback.fst ((one π hπ).map ≫ base) residueBase =
      pullback.fst (base (π := π) (n := 1)) residueBase := by
  dsimp only [oneSourceTargetIso]
  rw [pullback.congrHom_inv]
  change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
  rw [pullback.lift_fst, Category.comp_id]

/-- A coordinate-level cross isomorphism for the same exponent-one source. -/
def baseCrossIso : Cross.scheme k ≅ sourceSpecialFibre (one π hπ) :=
  Scheme.Spec.mapIso (PlaneNode.congr (residue_uniformizer_pow hπ
    0)).toRingEquiv.toCommRingCatIso.op ≪≫
    Scheme.PowerNode.specializationIso (S := k) (π ^ 1) ≪≫ (oneSourceTargetIso π hπ).symm

@[reassoc] lemma baseCrossIso_hom_fst :
    (baseCrossIso π hπ).hom ≫ pullback.fst ((one π hπ).map ≫ base) residueBase =
      Spec.map (CommRingCat.ofHom
        (nodeSpecializeAt (π ^ 1) (0 : k) (residue_uniformizer_pow hπ 0)).toRingHom) := by
  simp only [baseCrossIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    oneSourceTargetIso_inv_fst]
  change Spec.map (CommRingCat.ofHom (PlaneNode.congr (residue_uniformizer_pow hπ 0)).toRingHom) ≫
    (Scheme.PowerNode.specializationIso (S := k) (π ^ 1)).hom ≫ pullback.fst _ _ = _
  rw [Scheme.PowerNode.specializationIso_hom_fst, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  have h : ((PlaneNode.congr (residue_uniformizer_pow hπ 0)).toAlgHom.restrictScalars R).comp
      (PlaneNode.coefficientMap (S := k) (π ^ 1)) = nodeSpecializeAt (π ^ 1) (0 : k)
        (residue_uniformizer_pow hπ 0) := by
    apply PlaneNode.hom_ext
    · rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, PlaneNode.coefficientMap_U,
        nodeSpecializeAt, PlaneNode.lift_U]
      change PlaneNode.congr (residue_uniformizer_pow hπ 0)
        (PlaneNode.U (algebraMap R k (π ^ 1))) = PlaneNode.U (0 : k)
      exact PlaneNode.congr_U _
    · rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, PlaneNode.coefficientMap_V,
        nodeSpecializeAt, PlaneNode.lift_V]
      change PlaneNode.congr (residue_uniformizer_pow hπ 0)
        (PlaneNode.V (algebraMap R k (π ^ 1))) = PlaneNode.V (0 : k)
      exact PlaneNode.congr_V _
  exact congrArg AlgHom.toRingHom h

@[reassoc] lemma baseCrossIso_hom_snd :
    (baseCrossIso π hπ).hom ≫ pullback.snd ((one π hπ).map ≫ base) residueBase =
      Spec.map (CommRingCat.ofHom (algebraMap k (Cross.ring k))) := by
  simp only [baseCrossIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    oneSourceTargetIso_inv_snd]
  change Spec.map (CommRingCat.ofHom (PlaneNode.congr (residue_uniformizer_pow hπ 0)).toRingHom) ≫
    (Scheme.PowerNode.specializationIso (S := k) (π ^ 1)).hom ≫ pullback.snd _ _ = _
  rw [Scheme.PowerNode.specializationIso_hom_snd]
  exact Spec.map_algHom_algebraMap (PlaneNode.congr (residue_uniformizer_pow hπ 0)).toAlgHom

lemma baseLeftEnd_eq : baseLeftEnd π hπ = Cross.left k ≫ (baseCrossIso π hπ).hom := by
  apply pullback.hom_ext
  · rw [baseLeftEnd, pullback.lift_fst, Category.assoc, baseCrossIso_hom_fst]
    rw [Cross.left, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    have h : ((Cross.leftHom k).restrictScalars R).comp
        (nodeSpecializeAt (π ^ 1) (0 : k) (residue_uniformizer_pow hπ 0)) =
          residueLeftHom (π ^ 1) (residue_uniformizer_pow hπ 0) := by
      apply PlaneNode.hom_ext <;> simp [nodeSpecializeAt, Cross.leftHom, residueLeftHom]
    exact (congrArg AlgHom.toRingHom h).symm
  · rw [baseLeftEnd_base, Category.assoc, baseCrossIso_hom_snd]
    exact (Spec.map_algHom_algebraMap (Cross.leftHom k)).symm

lemma baseRightEnd_eq : baseRightEnd π hπ = Cross.right k ≫ (baseCrossIso π hπ).hom := by
  apply pullback.hom_ext
  · rw [baseRightEnd, pullback.lift_fst, Category.assoc, baseCrossIso_hom_fst]
    rw [Cross.right, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    have h : ((Cross.rightHom k).restrictScalars R).comp
        (nodeSpecializeAt (π ^ 1) (0 : k) (residue_uniformizer_pow hπ 0)) =
          residueRightHom (π ^ 1) (residue_uniformizer_pow hπ 0) := by
      apply PlaneNode.hom_ext <;> simp [nodeSpecializeAt, Cross.rightHom, residueRightHom]
    exact (congrArg AlgHom.toRingHom h).symm
  · rw [baseRightEnd_base, Category.assoc, baseCrossIso_hom_snd]
    exact (Spec.map_algHom_algebraMap (Cross.rightHom k)).symm

lemma base_ends_cover (z : sourceSpecialFibre (one π hπ)) :
    z ∈ Set.range (baseLeftEnd π hπ) ∨ z ∈ Set.range (baseRightEnd π hπ) := by
  rw [baseLeftEnd_eq, baseRightEnd_eq]
  exact cover_postcompose (Cross.left k) (Cross.right k) (baseCrossIso π hπ).hom
    (baseCrossIso π hπ).hom.surjective (Cross.components_cover k) z

lemma base_ends_isPullback : IsPullback (Cross.endpoint k) (Cross.endpoint k)
    (baseLeftEnd π hπ) (baseRightEnd π hπ) := by
  rw [baseLeftEnd_eq, baseRightEnd_eq]
  exact (Cross.intersection_isPullback k).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (baseCrossIso π hπ)
    (by simp) (by simp) (by simp) (by simp)

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeBaseEndGeometry


section NodeExponentTwo

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme.PowerNode.BlowupOverlaps AlgebraicGeometry.Scheme.Blowup.Coordinates
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {π : R} (hπ : Irreducible π)
local notation "k" => IsLocalRing.ResidueField R

/-- The middle unit-node parameter compatible with the left exceptional coordinate t. -/
def twoMiddleHom : PlaneNode.Ring (π ^ 0) →ₐ[R] Reciprocal.Laurent k :=
  PlaneNode.lift (π ^ 0) (Reciprocal.invT k) (Reciprocal.t k) (by simp)

/-- The left-overlap residue homomorphism followed by inversion of the Laurent coordinate. -/
def twoLeftOverlapHom : leftOverlap π →ₐ[R] Reciprocal.Laurent k :=
  ((Reciprocal.inversion k).restrictScalars R).comp (overlapResidueHom hπ)

lemma twoLeftOverlap_middle :
    (twoLeftOverlapHom hπ).comp (middleLeftOverlapBase π 0) = twoMiddleHom (π := π) := by
  apply PlaneNode.hom_ext
  · simp [twoLeftOverlapHom, middleLeftOverlapBase, twoMiddleHom]
  · simp [twoLeftOverlapHom, middleLeftOverlapBase, twoMiddleHom, overlapResidueBase]

lemma twoRightOverlap_middle :
    (overlapResidueHom hπ).comp (middleRightOverlapBase π 0) = twoMiddleHom (π := π) := by
  apply PlaneNode.hom_ext <;>
    simp [middleRightOverlapBase, middleLeftOverlapBase, twoMiddleHom, overlapResidueBase]

lemma twoLeftOverlap_outer :
    (twoLeftOverlapHom hπ).comp (IsScalarTower.toAlgHom R (PlaneNode.Ring π) (leftOverlap π)) =
      ((IsScalarTower.toAlgHom k k[X] (Reciprocal.Laurent k)).restrictScalars R).comp
        (residueRightHom π (residue_uniformizer hπ)) := by
  apply PlaneNode.hom_ext <;>
    simp [twoLeftOverlapHom, overlapResidueBase, residueRightHom, Reciprocal.t]

lemma twoRightOverlap_outer :
    (overlapResidueHom hπ).comp (IsScalarTower.toAlgHom R (PlaneNode.Ring π) (leftOverlap π)) =
      ((aeval (Reciprocal.invT k)).restrictScalars R).comp
        (residueRightHom π (residue_uniformizer hπ)) := by
  apply PlaneNode.hom_ext <;> simp [overlapResidueBase, residueRightHom]

variable (B : OneStepBlowup.Data π 0)

@[reassoc] lemma two_middle_left_total :
    Spec.map (CommRingCat.ofHom (twoMiddleHom (π := π)).toRingHom) ≫ middleChartMap B.atlas hπ =
      Reciprocal.toZeroChart k ≫
        Spec.map (CommRingCat.ofHom (residueRightHom π (residue_uniformizer hπ)).toRingHom) ≫
          leftChartMap B.atlas hπ := by
  have h := congrArg (Spec.map (CommRingCat.ofHom (twoLeftOverlapHom hπ).toRingHom) ≫ ·)
    (leftMiddle_explicit_triangle hπ B)
  rw [← Category.assoc, ← Spec.map_comp] at h
  have hm := congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom)) (twoLeftOverlap_middle hπ)
  change Spec.map (CommRingCat.ofHom ((twoLeftOverlapHom hπ).comp (middleLeftOverlapBase π
    0)).toRingHom) ≫ _ = _ at h
  rw [hm] at h
  rw [← Category.assoc, awayMap, ← Spec.map_comp] at h
  have ho := congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom)) (twoLeftOverlap_outer hπ)
  change _ = Spec.map (CommRingCat.ofHom ((twoLeftOverlapHom hπ).comp (IsScalarTower.toAlgHom R
    (PlaneNode.Ring π) (leftOverlap π))).toRingHom) ≫ _ at h
  rw [ho] at h
  rw [Reciprocal.toZeroChart, ← Category.assoc, ← Spec.map_comp]
  exact h

@[reassoc] lemma two_middle_right_total :
    Spec.map (CommRingCat.ofHom (twoMiddleHom (π := π)).toRingHom) ≫ middleChartMap B.atlas hπ =
      Reciprocal.toInfinityChart k ≫
        Spec.map (CommRingCat.ofHom (residueRightHom π (residue_uniformizer hπ)).toRingHom) ≫
          rightChartMap B.atlas hπ := by
  have h := congrArg (Spec.map (CommRingCat.ofHom (overlapResidueHom hπ).toRingHom) ≫ ·)
    (rightMiddle_explicit_triangle hπ B)
  rw [← Category.assoc, ← Spec.map_comp] at h
  have hm := congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom)) (twoRightOverlap_middle
    hπ)
  change Spec.map (CommRingCat.ofHom ((overlapResidueHom hπ).comp (middleRightOverlapBase π
    0)).toRingHom) ≫ _ = _ at h
  rw [hm] at h
  rw [← Category.assoc, awayMap, ← Spec.map_comp] at h
  have ho := congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom)) (twoRightOverlap_outer hπ)
  change _ = Spec.map (CommRingCat.ofHom ((overlapResidueHom hπ).comp (IsScalarTower.toAlgHom R
    (PlaneNode.Ring π) (leftOverlap π))).toRingHom) ≫ _ at h
  rw [ho] at h
  rw [Reciprocal.toInfinityChart, ← Category.assoc, ← Spec.map_comp]
  exact h

/-- Literal Laurent morphism into the actual exponent-zero source fibre. -/
def twoMiddleGm : Reciprocal.gm k ⟶ sourceSpecialFibre (zero π) :=
  pullback.lift (Spec.map (CommRingCat.ofHom (twoMiddleHom (π := π)).toRingHom))
    (Reciprocal.gmBase k) (by
      change _ ≫ (𝟙 _ ≫ base) = _
      rw [Category.id_comp]
      change Spec.map (CommRingCat.ofHom (twoMiddleHom (π := π)).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring (π ^ 0)))) =
        Spec.map (CommRingCat.ofHom (algebraMap k (Reciprocal.Laurent k))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R k))
      rw [Spec.map_algHom_algebraMap, ← Spec.map_comp]
      rfl)

@[reassoc] lemma twoMiddleGm_fst :
    twoMiddleGm (π := π) ≫ pullback.fst ((zero π).map ≫ base) residueBase =
      Spec.map (CommRingCat.ofHom (twoMiddleHom (π := π)).toRingHom) := pullback.lift_fst ..
@[reassoc] lemma twoMiddleGm_snd :
    twoMiddleGm (π := π) ≫ pullback.snd ((zero π).map ≫ base) residueBase =
      Reciprocal.gmBase k := pullback.lift_snd ..

@[reassoc] lemma two_middle_left_fibre :
    twoMiddleGm (π := π) ≫ middleFibreChart B hπ (zero π) =
      Reciprocal.toZeroChart k ≫ outerExceptionalBranch hπ ≫ leftFibreChart B hπ (zero π) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, middleFibreChart_source_triangle, leftFibreChart_source_triangle,
      twoMiddleGm_fst_assoc, outerExceptionalBranch_fst_assoc]
    rw [← Category.assoc]
    apply step_left_chart_agree B hπ (zero π)
    simpa only [zero, Category.id_comp, Category.assoc] using two_middle_left_total hπ B
  · simp only [Category.assoc, middleFibreChart_base_triangle, leftFibreChart_base_triangle,
      outerExceptionalBranch_snd, twoMiddleGm_snd]
    exact (Reciprocal.toZeroChart_over k).symm

@[reassoc] lemma two_middle_right_fibre :
    twoMiddleGm (π := π) ≫ middleFibreChart B hπ (zero π) =
      Reciprocal.toInfinityChart k ≫ outerExceptionalBranch hπ ≫ rightFibreChart B hπ (zero π) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, middleFibreChart_source_triangle, rightFibreChart_source_triangle,
      twoMiddleGm_fst_assoc, outerExceptionalBranch_fst_assoc]
    rw [← Category.assoc]
    apply step_right_chart_agree B hπ (zero π)
    simpa only [zero, Category.id_comp, Category.assoc] using two_middle_right_total hπ B
  · simp only [Category.assoc, middleFibreChart_base_triangle, rightFibreChart_base_triangle,
      outerExceptionalBranch_snd, twoMiddleGm_snd]
    exact (Reciprocal.toInfinityChart_over k).symm

lemma two_exceptional_transition :
    Reciprocal.toZeroChart k ≫ outerExceptionalBranch hπ ≫ leftFibreChart B hπ (zero π) =
      Reciprocal.toInfinityChart k ≫ outerExceptionalBranch hπ ≫ rightFibreChart B hπ (zero π) :=
  (two_middle_left_fibre hπ B).symm.trans (two_middle_right_fibre hπ B)

/-- The actual exceptional projective-line map in the exponent-two resolution. -/
def twoExceptional : projectiveP1 k ⟶ sourceSpecialFibre (step B hπ (zero π)) :=
  Reciprocal.descend k (outerExceptionalBranch hπ ≫ leftFibreChart B hπ (zero π))
    (outerExceptionalBranch hπ ≫ rightFibreChart B hπ (zero π)) (two_exceptional_transition hπ B)

@[reassoc] lemma twoExceptional_left :
    chart k 0 ≫ twoExceptional hπ B = outerExceptionalBranch hπ ≫ leftFibreChart B hπ (zero π) :=
  Reciprocal.chart_zero_descend ..
@[reassoc] lemma twoExceptional_right :
    chart k 1 ≫ twoExceptional hπ B = outerExceptionalBranch hπ ≫ rightFibreChart B hπ (zero π) :=
  Reciprocal.chart_infinity_descend ..
@[reassoc] lemma twoExceptional_base :
    twoExceptional hπ B ≫ pullback.snd ((step B hπ (zero π)).map ≫ base) residueBase =
      structureMap k := by
  apply Reciprocal.descend_over
  · rw [Category.assoc, leftFibreChart_base_triangle, outerExceptionalBranch_snd]
    rfl
  · rw [Category.assoc, rightFibreChart_base_triangle, outerExceptionalBranch_snd]
    rfl

@[reassoc] lemma twoExceptional_zero :
    Reciprocal.zeroSection k ≫ twoExceptional hπ B = outerNode hπ ≫ leftFibreChart B hπ (zero π)
      := by
  rw [twoExceptional, Reciprocal.zeroSection_descend, ← Category.assoc]
  exact congrArg (· ≫ leftFibreChart B hπ (zero π)) (outerExceptionalBranch_endpoint hπ)
@[reassoc] lemma twoExceptional_infinity :
    Reciprocal.infinitySection k ≫ twoExceptional hπ B = outerNode hπ ≫ rightFibreChart B hπ (zero
      π) := by
  rw [twoExceptional, Reciprocal.infinitySection_descend, ← Category.assoc]
  exact congrArg (· ≫ rightFibreChart B hπ (zero π)) (outerExceptionalBranch_endpoint hπ)

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeExponentTwo


section NodeExponentTwoGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution

lemma unitNodeLaurentEquiv_u (k : Type u) [CommRing k] :
    unitNodeLaurentEquiv k (PlaneNode.U (1 : k)) = Reciprocal.t k := by
  change PlaneNode.Regularity.awayToLaurent (1 : k) (algebraMap _ _ (PlaneNode.U (1 : k))) = _
  simp [Reciprocal.t]
lemma unitNodeLaurentEquiv_v (k : Type u) [CommRing k] :
    unitNodeLaurentEquiv k (PlaneNode.V (1 : k)) = Reciprocal.invT k := by
  change PlaneNode.Regularity.awayToLaurent (1 : k) (algebraMap _ _ (PlaneNode.V (1 : k))) = _
  simp [Reciprocal.invT]

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {π : R} (hπ : Irreducible π)
local notation "k" => IsLocalRing.ResidueField R

@[reassoc] lemma zeroSourceTargetIso_inv_fst :
    (zeroSourceTargetIso π).inv ≫ pullback.fst ((zero π).map ≫ base) residueBase =
      pullback.fst (base (π := π) (n := 0)) residueBase := by
  dsimp only [zeroSourceTargetIso]
  rw [pullback.congrHom_inv]
  change pullback.lift _ _ _ ≫ pullback.fst _ _ = _
  rw [pullback.lift_fst, Category.comp_id]

local notation "unitParameterEq" =>
  Eq.trans (congrArg (algebraMap R k) (pow_zero π)) (map_one (algebraMap R k))

/-- A unit-node identification retaining the literal U and V coordinates. -/
def twoUnitFibreIso : Spec (.of (PlaneNode.Ring (1 : k))) ≅ sourceSpecialFibre (zero π) :=
  Scheme.Spec.mapIso (PlaneNode.congr
    (unitParameterEq : algebraMap R k (π ^ 0) = 1)).toRingEquiv.toCommRingCatIso.op ≪≫
    Scheme.PowerNode.specializationIso (S := k) (π ^ 0) ≪≫ (zeroSourceTargetIso π).symm

@[reassoc] lemma twoUnitFibreIso_fst :
    (twoUnitFibreIso (π := π)).hom ≫ pullback.fst ((zero π).map ≫ base) residueBase =
      Spec.map (CommRingCat.ofHom (nodeSpecializeAt (π ^ 0) (1 : k)
          (unitParameterEq)).toRingHom) := by
  rw [twoUnitFibreIso, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Category.assoc, Category.assoc,
    zeroSourceTargetIso_inv_fst]
  change Spec.map (CommRingCat.ofHom (PlaneNode.congr
    (unitParameterEq : algebraMap R k (π ^ 0) = 1)).toRingHom) ≫
    (Scheme.PowerNode.specializationIso (S := k) (π ^ 0)).hom ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring (π ^ 0)))))
        (Spec.map (CommRingCat.ofHom (algebraMap R k))) = _
  rw [Scheme.PowerNode.specializationIso_hom_fst]
  change Spec.map (CommRingCat.ofHom (PlaneNode.congr
    (unitParameterEq : algebraMap R k (π ^ 0) = 1)).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (PlaneNode.coefficientMap (S := k) (π ^ 0)).toRingHom) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  have h : ((PlaneNode.congr
    (unitParameterEq : algebraMap R k (π ^ 0) = 1)).toAlgHom.restrictScalars R).comp
      (PlaneNode.coefficientMap (S := k) (π ^ 0)) =
        nodeSpecializeAt (π ^ 0) (1 : k) (unitParameterEq) := by
    apply PlaneNode.hom_ext
    · rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, PlaneNode.coefficientMap_U,
        nodeSpecializeAt, PlaneNode.lift_U]
      change PlaneNode.congr
        (unitParameterEq : algebraMap R k (π ^ 0) = 1)
        (PlaneNode.U (algebraMap R k (π ^ 0))) = PlaneNode.U (1 : k)
      exact PlaneNode.congr_U _
    · rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, PlaneNode.coefficientMap_V,
        nodeSpecializeAt, PlaneNode.lift_V]
      change PlaneNode.congr
        (unitParameterEq : algebraMap R k (π ^ 0) = 1)
        (PlaneNode.V (algebraMap R k (π ^ 0))) = PlaneNode.V (1 : k)
      exact PlaneNode.congr_V _
  exact congrArg AlgHom.toRingHom h

@[reassoc] lemma twoUnitFibreIso_snd :
    (twoUnitFibreIso (π := π)).hom ≫ pullback.snd ((zero π).map ≫ base) residueBase =
      Spec.map (CommRingCat.ofHom (algebraMap k (PlaneNode.Ring (1 : k)))) := by
  rw [twoUnitFibreIso, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Category.assoc, Category.assoc,
    zeroSourceTargetIso_inv_snd]
  change Spec.map (CommRingCat.ofHom (PlaneNode.congr
    (unitParameterEq : algebraMap R k (π ^ 0) = 1)).toRingHom) ≫
    (Scheme.PowerNode.specializationIso (S := k) (π ^ 0)).hom ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring (π ^ 0)))))
        (Spec.map (CommRingCat.ofHom (algebraMap R k))) = _
  rw [Scheme.PowerNode.specializationIso_hom_snd]
  exact Spec.map_algHom_algebraMap (PlaneNode.congr
    (unitParameterEq : algebraMap R k (π ^ 0) = 1)).toAlgHom

/-- The middle Gm is isomorphic to the actual exponent-zero source fibre. -/
def twoMiddleGmIso : Reciprocal.gm k ≅ sourceSpecialFibre (zero π) :=
  Scheme.Spec.mapIso ((unitNodeLaurentEquiv k).trans (Reciprocal.inversionEquiv
    k)).toRingEquiv.toCommRingCatIso.op ≪≫
    twoUnitFibreIso (π := π)

lemma twoMiddleGm_eq_iso : twoMiddleGm (π := π) = (twoMiddleGmIso (π := π)).hom := by
  apply pullback.hom_ext
  · rw [twoMiddleGm_fst, twoMiddleGmIso, Iso.trans_hom, Category.assoc, twoUnitFibreIso_fst]
    change Spec.map (CommRingCat.ofHom (twoMiddleHom (π := π)).toRingHom) =
      Spec.map (CommRingCat.ofHom ((unitNodeLaurentEquiv k).trans (Reciprocal.inversionEquiv
        k)).toRingHom) ≫ _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    have h : (((unitNodeLaurentEquiv k).trans (Reciprocal.inversionEquiv
      k)).toAlgHom.restrictScalars R).comp
        (nodeSpecializeAt (π ^ 0) (1 : k) (unitParameterEq)) = twoMiddleHom (π := π) := by
      apply PlaneNode.hom_ext <;> simp [nodeSpecializeAt, twoMiddleHom, unitNodeLaurentEquiv_u,
        unitNodeLaurentEquiv_v, Reciprocal.inversionEquiv]
    exact (congrArg AlgHom.toRingHom h).symm
  · rw [twoMiddleGm_snd, twoMiddleGmIso, Iso.trans_hom, Category.assoc, twoUnitFibreIso_snd]
    exact (Spec.map_algHom_algebraMap ((unitNodeLaurentEquiv k).trans (Reciprocal.inversionEquiv
      k)).toAlgHom).symm

instance twoMiddleGm_isIso : IsIso (twoMiddleGm (π := π)) := by
  rw [twoMiddleGm_eq_iso]
  infer_instance

variable (B : OneStepBlowup.Data π 0)

lemma two_middle_range_subset : Set.range (middleFibreChart B hπ (zero π)) ⊆
    Set.range (twoExceptional hπ B) := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨t, rfl⟩ := (twoMiddleGm (π := π)).surjective z
  refine ⟨chart k 0 (Reciprocal.toZeroChart k t), ?_⟩
  change (Reciprocal.toZeroChart k ≫ chart k 0 ≫ twoExceptional hπ B) t =
    (twoMiddleGm (π := π) ≫ middleFibreChart B hπ (zero π)) t
  rw [twoExceptional_left, two_middle_left_fibre]

/-- Exhaustive actual exponent-two fibre: the exceptional P1 and the two strict-transform ends. -/
lemma two_components_cover (z : sourceSpecialFibre (step B hπ (zero π))) :
    z ∈ Set.range (stepLeftEnd hπ B (zero π)) ∨
      z ∈ Set.range (twoExceptional hπ B) ∨ z ∈ Set.range (stepRightEnd hπ B (zero π)) := by
  rcases fibre_three_charts_cover B hπ (zero π) z with hm | ⟨x, rfl⟩ | ⟨x, rfl⟩
  · exact Or.inr (Or.inl (two_middle_range_subset hπ B hm))
  · rcases outer_branches_cover hπ x with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr (Or.inl ⟨chart k 0 a, congr($(twoExceptional_left hπ B) a)⟩)
  · rcases outer_branches_cover hπ x with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact Or.inr (Or.inr ⟨a, rfl⟩)
    · exact Or.inr (Or.inl ⟨chart k 1 a, congr($(twoExceptional_right hπ B) a)⟩)

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeExponentTwoGeometry


section NodeExponentTwoClosed

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme.PowerNode.BlowupOverlaps AlgebraicGeometry.Scheme.Blowup.Coordinates
  AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {π : R} (hπ : Irreducible π) (B : OneStepBlowup.Data π 0)
local notation "k" => IsLocalRing.ResidueField R

/-- The basic open where the exponent-two outer ratio is invertible. -/
def twoOuterRatioOpen (π : R) : (Spec (.of (PlaneNode.Ring π))).Opens :=
  PrimeSpectrum.basicOpen (outerRatio π 0)

lemma two_stepLeft_preimage_right :
    stepLeftChart B hπ (zero π) ⁻¹' Set.range (stepRightChart B hπ (zero π)) =
      (twoOuterRatioOpen π : Set (Spec (.of (PlaneNode.Ring π)))) := by
  rw [range_snd_of_isPullback (stepRightChart_isPullback B hπ (zero π))]
  change (stepLeftChart B hπ (zero π) ≫ stepToBlowup B hπ (zero π)) ⁻¹' Set.range (rightChartMap
    B.atlas hπ) = _
  rw [stepLeftChart_toBlowup]
  rw [chart_preimage_of_overlap (awayMap (outerRatio π 0)) (leftChartMap B.atlas hπ)
    (rightChartMap B.atlas hπ) (outer_range hπ B.atlas)]
  exact PrimeSpectrum.localization_away_comap_range _ _

lemma two_stepRight_preimage_left :
    stepRightChart B hπ (zero π) ⁻¹' Set.range (stepLeftChart B hπ (zero π)) =
      (twoOuterRatioOpen π : Set (Spec (.of (PlaneNode.Ring π)))) := by
  rw [range_snd_of_isPullback (stepLeftChart_isPullback B hπ (zero π))]
  change (stepRightChart B hπ (zero π) ≫ stepToBlowup B hπ (zero π)) ⁻¹' Set.range (leftChartMap
    B.atlas hπ) = _
  rw [stepRightChart_toBlowup]
  rw [chart_preimage_of_overlap (awayMap (outerRatio π 0)) (rightChartMap B.atlas hπ)
    (leftChartMap B.atlas hπ)
    (overlap_range B.atlas (generator π 0 2) (generator π 0 0)
      (dvrRightReesEquiv π hπ 0).toRingEquiv (dvrLeftReesEquiv π hπ 0).toRingEquiv
      (outerRatio π 0) (right_left_ratio π hπ 0))]
  exact PrimeSpectrum.localization_away_comap_range _ _

lemma two_leftExceptional_preimage_right :
    (outerExceptionalBranch hπ ≫ leftFibreChart B hπ (zero π)) ⁻¹'
      Set.range (rightFibreChart B hπ (zero π)) = Set.range (Reciprocal.toZeroChart k) := by
  change outerExceptionalBranch hπ ⁻¹' (leftFibreChart B hπ (zero π) ⁻¹' Set.range
    (rightFibreChart B hπ (zero π))) = _
  dsimp only [leftFibreChart, rightFibreChart, sourceSpecialFibre, outerFibre]
  rw [fibreChart_preimage_range, two_stepLeft_preimage_right]
  change (outerExceptionalBranch hπ ≫
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π)))) residueBase) ⁻¹'
      (twoOuterRatioOpen π : Set (Spec (.of (PlaneNode.Ring π)))) = _
  rw [outerExceptionalBranch_fst]
  ext x
  change _ ↔ x ∈ (Reciprocal.toZeroChart k).opensRange
  rw [Reciprocal.zeroChart_range]
  change (residueRightHom π (residue_uniformizer hπ)) (outerRatio π 0) ∉ x.asIdeal ↔ Polynomial.X
    ∉ x.asIdeal
  simp [outerRatio, residueRightHom, x.isPrime.pow_mem_iff_mem 2 (by decide)]

lemma two_rightExceptional_preimage_left :
    (outerExceptionalBranch hπ ≫ rightFibreChart B hπ (zero π)) ⁻¹'
      Set.range (leftFibreChart B hπ (zero π)) = Set.range (Reciprocal.toInfinityChart k) := by
  change outerExceptionalBranch hπ ⁻¹' (rightFibreChart B hπ (zero π) ⁻¹' Set.range
    (leftFibreChart B hπ (zero π))) = _
  dsimp only [leftFibreChart, rightFibreChart, sourceSpecialFibre, outerFibre]
  rw [fibreChart_preimage_range, two_stepRight_preimage_left]
  change (outerExceptionalBranch hπ ≫
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π)))) residueBase) ⁻¹'
      (twoOuterRatioOpen π : Set (Spec (.of (PlaneNode.Ring π)))) = _
  rw [outerExceptionalBranch_fst]
  ext x
  change _ ↔ x ∈ (Reciprocal.toInfinityChart k).opensRange
  rw [Reciprocal.infinityChart_range]
  change (residueRightHom π (residue_uniformizer hπ)) (outerRatio π 0) ∉ x.asIdeal ↔ Polynomial.X
    ∉ x.asIdeal
  simp [outerRatio, residueRightHom, x.isPrime.pow_mem_iff_mem 2 (by decide)]

lemma twoExceptional_preimage_left :
    twoExceptional hπ B ⁻¹ᵁ (leftFibreChart B hπ (zero π)).opensRange = (chart k 0).opensRange := by
  ext z
  constructor
  · intro hz
    rcases Reciprocal.charts_cover k z with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact ⟨a, rfl⟩
    · have ha : a ∈ (outerExceptionalBranch hπ ≫ rightFibreChart B hπ (zero π)) ⁻¹'
          Set.range (leftFibreChart B hπ (zero π)) := by
        change (chart k 1 ≫ twoExceptional hπ B) a ∈ Set.range (leftFibreChart B hπ (zero π)) at hz
        rwa [twoExceptional_right] at hz
      rw [two_rightExceptional_preimage_left] at ha
      obtain ⟨t, rfl⟩ := ha
      refine ⟨Reciprocal.toZeroChart k t, ?_⟩
      exact congr($(Reciprocal.transition k) t)
  · rintro ⟨a, rfl⟩
    change (chart k 0 ≫ twoExceptional hπ B) a ∈ Set.range (leftFibreChart B hπ (zero π))
    rw [twoExceptional_left]
    exact ⟨outerExceptionalBranch hπ a, rfl⟩

lemma twoExceptional_preimage_right :
    twoExceptional hπ B ⁻¹ᵁ (rightFibreChart B hπ (zero π)).opensRange = (chart k 1).opensRange :=
      by
  ext z
  constructor
  · intro hz
    rcases Reciprocal.charts_cover k z with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · have ha : a ∈ (outerExceptionalBranch hπ ≫ leftFibreChart B hπ (zero π)) ⁻¹'
          Set.range (rightFibreChart B hπ (zero π)) := by
        change (chart k 0 ≫ twoExceptional hπ B) a ∈ Set.range (rightFibreChart B hπ (zero π)) at hz
        rwa [twoExceptional_left] at hz
      rw [two_leftExceptional_preimage_right] at ha
      obtain ⟨t, rfl⟩ := ha
      refine ⟨Reciprocal.toInfinityChart k t, ?_⟩
      exact (congr($(Reciprocal.transition k) t)).symm
    · exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    change (chart k 1 ≫ twoExceptional hπ B) a ∈ Set.range (rightFibreChart B hπ (zero π))
    rw [twoExceptional_right]
    exact ⟨outerExceptionalBranch hπ a, rfl⟩

lemma twoExceptional_left_isPullback :
    IsPullback (outerExceptionalBranch hπ) (chart k 0)
      (leftFibreChart B hπ (zero π)) (twoExceptional hπ B) :=
  IsOpenImmersion.isPullback _ _ _ _ (twoExceptional_left hπ B) (twoExceptional_preimage_left hπ B)
lemma twoExceptional_right_isPullback :
    IsPullback (outerExceptionalBranch hπ) (chart k 1)
      (rightFibreChart B hπ (zero π)) (twoExceptional hπ B) :=
  IsOpenImmersion.isPullback _ _ _ _ (twoExceptional_right hπ B) (twoExceptional_preimage_right hπ
    B)

instance twoExceptional_closedImmersion : IsClosedImmersion (twoExceptional hπ B) := by
  let U : Fin 2 → Scheme.{u} := fun _ => outerFibre (π := π)
  let j : ∀ i, U i ⟶ sourceSpecialFibre (step B hπ (zero π)) :=
    fun | 0 => leftFibreChart B hπ (zero π) | 1 => rightFibreChart B hπ (zero π)
  let c : ∀ i, Reciprocal.affineLine k ⟶ U i := fun _ => outerExceptionalBranch hπ
  have : ∀ i, IsOpenImmersion (j i) := by
    intro i
    fin_cases i <;> dsimp [j] <;> infer_instance
  have : ∀ i, IsClosedImmersion (c i) := by intro i; dsimp [c]; infer_instance
  apply Reciprocal.closedImmersion_of_pullbackCharts k (twoExceptional hπ B)
    (pullback.snd ((step B hπ (zero π)).map ≫ base) residueBase) (twoExceptional_base hπ B) U j c
  intro i
  fin_cases i
  · exact twoExceptional_left_isPullback hπ B
  · exact twoExceptional_right_isPullback hπ B

/-- The left end meets the exceptional projective line in its zero section, scheme-theoretically. -/
lemma twoLeftEnd_intersection_isPullback :
    IsPullback (Cross.endpoint k) (Reciprocal.zeroSection k)
      (stepLeftEnd hπ B (zero π)) (twoExceptional hπ B) := by
  exact (outer_branches_isPullback hπ).paste_vert (twoExceptional_left_isPullback hπ B)

/-- The right end meets the exceptional projective line in its infinity section,
  scheme-theoretically. -/
lemma twoRightEnd_intersection_isPullback :
    IsPullback (Cross.endpoint k) (Reciprocal.infinitySection k)
      (stepRightEnd hπ B (zero π)) (twoExceptional hπ B) := by
  exact (outer_branches_isPullback hπ).paste_vert (twoExceptional_right_isPullback hπ B)

lemma twoLeftEnd_preimage_right_empty :
    stepLeftEnd hπ B (zero π) ⁻¹' Set.range (rightFibreChart B hπ (zero π)) = ∅ := by
  change outerEndBranch hπ ⁻¹' (leftFibreChart B hπ (zero π) ⁻¹' Set.range (rightFibreChart B hπ
    (zero π))) = _
  dsimp only [leftFibreChart, rightFibreChart, sourceSpecialFibre, outerFibre]
  rw [fibreChart_preimage_range, two_stepLeft_preimage_right]
  change (outerEndBranch hπ ≫
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring π)))) residueBase) ⁻¹'
      (twoOuterRatioOpen π : Set (Spec (.of (PlaneNode.Ring π)))) = _
  rw [outerEndBranch_fst]
  ext x
  change (residueLeftHom π (residue_uniformizer hπ)) (outerRatio π 0) ∉ x.asIdeal ↔ False
  simp [outerRatio, residueLeftHom]

lemma two_ends_disjoint : Disjoint (Set.range (stepLeftEnd hπ B (zero π)))
    (Set.range (stepRightEnd hπ B (zero π))) := by
  rw [Set.disjoint_left]
  rintro z ⟨a, rfl⟩ ⟨b, hb⟩
  have h : a ∈ stepLeftEnd hπ B (zero π) ⁻¹' Set.range (rightFibreChart B hπ (zero π)) :=
    ⟨outerEndBranch hπ b, hb⟩
  rw [twoLeftEnd_preimage_right_empty] at h
  exact h

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeExponentTwoClosed


section NodeChainComponentFamily

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (π : R) (hπ : Irreducible π)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (ha : BlowupAffineAtlas.{u})
local notation "k" => IsLocalRing.ResidueField R

/-- The middle open chart embedding the resolution special fibre for exponent `q + 1` into that
for exponent `q + 3`. -/
def recursiveMiddleChart (q : ℕ) :
    sourceSpecialFibre (resolve π hπ hex hp ha (q + 1)) ⟶
      sourceSpecialFibre (resolve π hπ hex hp ha (q + 3)) :=
  middleFibreChart (OneStepBlowup.ofFamilies π (q + 1) hex hp ha) hπ
    (resolve π hπ hex hp ha (q + 1))

@[reassoc] lemma recursiveMiddleChart_base (q : ℕ) :
    recursiveMiddleChart π hπ hex hp ha q ≫
      pullback.snd ((resolve π hπ hex hp ha (q + 3)).map ≫ base) residueBase =
        pullback.snd ((resolve π hπ hex hp ha (q + 1)).map ≫ base) residueBase :=
  middleFibreChart_base_triangle ..

instance recursiveMiddleChart_open (q : ℕ) :
    IsOpenImmersion (recursiveMiddleChart π hπ hex hp ha q) := by
  unfold recursiveMiddleChart
  infer_instance

/-- The actual ordered family of interior projective-line morphisms into the
same recursive resolution. No family or chain certificate is supplied as input. -/
def interiorComponent : (q : ℕ) → Fin q →
    (projectiveP1 k ⟶ sourceSpecialFibre (resolve π hπ hex hp ha (q + 1)))
  | 0, i => Fin.elim0 i
  | 1, _ => twoExceptional hπ (OneStepBlowup.ofFamilies π 0 hex hp ha)
  | q + 2, i => Fin.cases (resolveLeftNewP1 π hπ hex hp ha q)
      (Fin.lastCases (resolveRightNewP1 π hπ hex hp ha q)
        (fun j => interiorComponent q j ≫
          recursiveMiddleChart π hπ hex hp ha q)) i

@[reassoc] lemma interiorComponent_base : ∀ q (i : Fin q),
    interiorComponent π hπ hex hp ha q i ≫
      pullback.snd ((resolve π hπ hex hp ha (q + 1)).map ≫ base) residueBase = structureMap k
  | 0, i => Fin.elim0 i
  | 1, i => twoExceptional_base hπ (OneStepBlowup.ofFamilies π 0 hex hp ha)
  | q + 2, i => by
    refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun j => ?_) j) i
    · exact resolveLeftNewP1_base π hπ hex hp ha q
    · simpa only [interiorComponent, Fin.cases_succ, Fin.lastCases_last] using
        resolveRightNewP1_base π hπ hex hp ha q
    · simpa only [interiorComponent, Fin.cases_succ, Fin.lastCases_castSucc,
        Category.assoc, recursiveMiddleChart_base] using
        interiorComponent_base q j

lemma interiorComponent_closedImmersion : ∀ q (i : Fin q),
    IsClosedImmersion (interiorComponent π hπ hex hp ha q i)
  | 0, i => Fin.elim0 i
  | 1, i => twoExceptional_closedImmersion hπ (OneStepBlowup.ofFamilies π 0 hex hp ha)
  | q + 2, i => by
    refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun j => ?_) j) i
    · exact resolveLeftNewP1_closedImmersion π hπ hex hp ha q
    · simpa only [interiorComponent, Fin.cases_succ, Fin.lastCases_last] using
        resolveRightNewP1_closedImmersion π hπ hex hp ha q
    · have := interiorComponent_closedImmersion q j
      simpa only [interiorComponent, Fin.cases_succ, Fin.lastCases_castSucc, recursiveMiddleChart]
        using
        middle_projective_component_closed π hπ
        (OneStepBlowup.ofFamilies π (q + 1) hex hp ha)
        (resolve π hπ hex hp ha (q + 1)) (interiorComponent π hπ hex hp ha q j)
        (interiorComponent_base π hπ hex hp ha q j)

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeChainComponentFamily


section NodeExceptionalContraction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
local notation "k" => IsLocalRing.ResidueField R

/-- The literal residue origin U = V = 0 in an affine node. -/
def residueOriginHom (c : R) (hc : algebraMap R k c = 0) : PlaneNode.Ring c →ₐ[R] k :=
  PlaneNode.lift c 0 0 (by simpa using hc.symm)

variable {π : R} (hπ : Irreducible π)

/-- The residue-field origin of the original node with parameter `π ^ (q + 1)`. -/
def originalNode (q : ℕ) : Spec (.of k) ⟶ Spec (.of (PlaneNode.Ring (π ^ (q + 1)))) :=
  Spec.map (CommRingCat.ofHom
    (residueOriginHom (π ^ (q + 1)) (residue_uniformizer_pow hπ q)).toRingHom)

@[reassoc] lemma originalNode_base (q : ℕ) :
    originalNode hπ q ≫ base = residueBase := by
  exact Spec.map_algHom_algebraMap (residueOriginHom (π ^ (q + 1)) (residue_uniformizer_pow hπ q))

lemma middleBase_specialization (m : ℕ) :
    (PlaneNode.coefficientMap (S := k) (π ^ m)).comp (middleBase π m) =
      (IsScalarTower.toAlgHom R k (PlaneNode.Ring (algebraMap R k (π ^ m)))).comp
        (residueOriginHom (π ^ (m + 2)) (residue_uniformizer_pow hπ (m + 1))) := by
  have hz : algebraMap R (PlaneNode.Ring (algebraMap R k (π ^ m))) π = 0 := by
    rw [IsScalarTower.algebraMap_apply R k (PlaneNode.Ring (algebraMap R k (π ^ m))) π,
      residue_uniformizer hπ, map_zero]
  apply PlaneNode.hom_ext <;>
    simp only [AlgHom.comp_apply, middleBase, PlaneNode.lift_U, PlaneNode.lift_V, map_mul,
      AlgHom.commutes, residueOriginHom, map_zero, hz, zero_mul]

@[reassoc] lemma middleBase_specialFibre (m : ℕ) :
    pullback.fst (base (π := π) (n := m)) (residueBase (R := R)) ≫
      Spec.map (CommRingCat.ofHom (middleBase π m).toRingHom) =
    pullback.snd (base (π := π) (n := m)) (residueBase (R := R)) ≫
      originalNode hπ (m + 1) := by
  apply (cancel_epi (Scheme.PowerNode.specializationIso (S := k) (π ^ m)).hom).mp
  change (Scheme.PowerNode.specializationIso (S := k) (π ^ m)).hom ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring (π ^ m)))))
          (Spec.map (CommRingCat.ofHom (algebraMap R k))) ≫
            Spec.map (CommRingCat.ofHom (middleBase π m).toRingHom) =
      (Scheme.PowerNode.specializationIso (S := k) (π ^ m)).hom ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R (PlaneNode.Ring (π ^ m)))))
          (Spec.map (CommRingCat.ofHom (algebraMap R k))) ≫ originalNode hπ (m + 1)
  rw [Scheme.PowerNode.specializationIso_hom_fst_assoc,
    Scheme.PowerNode.specializationIso_hom_snd_assoc, originalNode,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact congrArg (fun f => CommRingCat.ofHom f.toRingHom) (middleBase_specialization hπ m)

variable {m : ℕ} (B : OneStepBlowup.Data π m) (E : Data π m)

/-- The whole old middle fibre contracts to the original residue origin. -/
@[reassoc] lemma middleFibreChart_target :
    middleFibreChart B hπ E ≫ pullback.fst ((step B hπ E).map ≫ base) residueBase ≫
      (step B hπ E).map =
    pullback.snd (E.map ≫ base) residueBase ≫ originalNode hπ (m + 1) := by
  rw [middleFibreChart_source_triangle_assoc, stepModifiedChart_triangle]
  let j := pullback.lift
    (pullback.fst (E.map ≫ base) residueBase ≫ E.map)
    (pullback.snd (E.map ≫ base) residueBase)
    (by simpa only [Category.assoc] using (pullback.condition (f := E.map ≫ base) (g :=
      residueBase)))
  have h := congrArg (j ≫ ·) (middleBase_specialFibre hπ m)
  simpa only [← Category.assoc, j, pullback.lift_fst, pullback.lift_snd] using h

lemma leftBase_residueExceptional :
    (residueRightHom π (residue_uniformizer hπ)).comp (leftBase π m) =
      ((Algebra.ofId k k[X]).restrictScalars R).comp
        (residueOriginHom (π ^ (m + 2)) (residue_uniformizer_pow hπ (m + 1))) := by
  apply PlaneNode.hom_ext <;>
    simp [leftBase, residueRightHom, residueOriginHom, hπ.not_isUnit]

lemma rightBase_residueExceptional :
    (residueRightHom π (residue_uniformizer hπ)).comp (rightBase π m) =
      ((Algebra.ofId k k[X]).restrictScalars R).comp
        (residueOriginHom (π ^ (m + 2)) (residue_uniformizer_pow hπ (m + 1))) := by
  apply PlaneNode.hom_ext <;>
    simp [rightBase_u, rightBase_v, residueRightHom, residueOriginHom, hπ.not_isUnit]

@[reassoc] lemma outerExceptional_left_target :
    outerExceptionalBranch hπ ≫ leftFibreChart B hπ E ≫
      pullback.fst ((step B hπ E).map ≫ base) residueBase ≫ (step B hπ E).map =
    Spec.map (CommRingCat.ofHom (algebraMap k k[X])) ≫ originalNode hπ (m + 1) := by
  rw [leftFibreChart_source_triangle_assoc, outerExceptionalBranch_fst_assoc,
    stepLeftChart_triangle, originalNode, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact congrArg (fun f => CommRingCat.ofHom f.toRingHom) (leftBase_residueExceptional hπ (m := m))

@[reassoc] lemma outerExceptional_right_target :
    outerExceptionalBranch hπ ≫ rightFibreChart B hπ E ≫
      pullback.fst ((step B hπ E).map ≫ base) residueBase ≫ (step B hπ E).map =
    Spec.map (CommRingCat.ofHom (algebraMap k k[X])) ≫ originalNode hπ (m + 1) := by
  rw [rightFibreChart_source_triangle_assoc, outerExceptionalBranch_fst_assoc,
    stepRightChart_triangle, originalNode, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact congrArg (fun f => CommRingCat.ofHom f.toRingHom) (rightBase_residueExceptional hπ (m := m))

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeExceptionalContraction


section NodeInteriorContraction

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry Polynomial
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.PowerNode.BlowupAtlas
  AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.Resolution
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
local notation "k" => IsLocalRing.ResidueField R

lemma residueOriginHom_surjective (c : R) (hc : algebraMap R k c = 0) :
    Function.Surjective (residueOriginHom c hc) := by
  intro a
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (R := R) a
  refine ⟨algebraMap R (PlaneNode.Ring c) r, ?_⟩
  simpa only [AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq] using hr

variable {π : R} (hπ : Irreducible π)

instance originalNode_closedImmersion (q : ℕ) : IsClosedImmersion (originalNode hπ q) :=
  IsClosedImmersion.spec_of_surjective _ (residueOriginHom_surjective _ (residue_uniformizer_pow
    hπ q))

@[reassoc] lemma twoExceptional_target (B : OneStepBlowup.Data π 0) :
    twoExceptional hπ B ≫ pullback.fst ((step B hπ (zero π)).map ≫ base) residueBase ≫
      (step B hπ (zero π)).map = structureMap k ≫ originalNode hπ 1 := by
  apply Reciprocal.hom_ext k
  · rw [twoExceptional_left_assoc, outerExceptional_left_target, ← Category.assoc, chart_over]
  · rw [twoExceptional_right_assoc, outerExceptional_right_target, ← Category.assoc, chart_over]

variable (π : R) (hπ : Irreducible π)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (ha : BlowupAffineAtlas.{u})

@[reassoc] lemma resolveLeftNewP1_target (q : ℕ) :
    resolveLeftNewP1 π hπ hex hp ha q ≫
      pullback.fst ((resolve π hπ hex hp ha (q + 3)).map ≫ base) residueBase ≫
      (resolve π hπ hex hp ha (q + 3)).map = structureMap k ≫ originalNode hπ (q + 2) := by
  apply Reciprocal.hom_ext k
  · rw [resolveLeftNewP1_old_chart_assoc]
    simp only [resolve]
    rw [ middleFibreChart_target,
      ← Category.assoc, resolveLeftEnd_base, ← Category.assoc, chart_over]
  · rw [resolveLeftNewP1_new_chart_assoc]
    simp only [resolve]
    rw [ outerExceptional_left_target,
      ← Category.assoc, chart_over]

@[reassoc] lemma resolveRightNewP1_target (q : ℕ) :
    resolveRightNewP1 π hπ hex hp ha q ≫
      pullback.fst ((resolve π hπ hex hp ha (q + 3)).map ≫ base) residueBase ≫
      (resolve π hπ hex hp ha (q + 3)).map = structureMap k ≫ originalNode hπ (q + 2) := by
  apply Reciprocal.hom_ext k
  · rw [resolveRightNewP1_old_chart_assoc]
    simp only [resolve]
    rw [ middleFibreChart_target,
      ← Category.assoc, resolveRightEnd_base, ← Category.assoc, chart_over]
  · rw [resolveRightNewP1_new_chart_assoc]
    simp only [resolve]
    rw [ outerExceptional_right_target,
      ← Category.assoc, chart_over]

/-- Every actual interior projective line is contracted to the literal original
residue origin by the very same recursively constructed resolution morphism. -/
@[reassoc] lemma interiorComponent_target : ∀ q (i : Fin q),
    interiorComponent π hπ hex hp ha q i ≫
      pullback.fst ((resolve π hπ hex hp ha (q + 1)).map ≫ base) residueBase ≫
      (resolve π hπ hex hp ha (q + 1)).map = structureMap k ≫ originalNode hπ q
  | 0, i => Fin.elim0 i
  | 1, i => twoExceptional_target hπ (OneStepBlowup.ofFamilies π 0 hex hp ha)
  | q + 2, i => by
    refine Fin.cases ?_ (fun j => Fin.lastCases ?_ (fun j => ?_) j) i
    · exact resolveLeftNewP1_target π hπ hex hp ha q
    · simpa only [interiorComponent, Fin.cases_succ, Fin.lastCases_last] using
        resolveRightNewP1_target π hπ hex hp ha q
    · simp only [interiorComponent, Fin.cases_succ, Fin.lastCases_castSucc,
        Category.assoc, recursiveMiddleChart, resolve]
      rw [middleFibreChart_target, interiorComponent_base_assoc]

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeInteriorContraction
