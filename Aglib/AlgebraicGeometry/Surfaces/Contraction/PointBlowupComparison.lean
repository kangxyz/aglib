/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Contraction.Projective
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Line.RelativePositiveTwist
public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalFunctions
public import Aglib.AlgebraicGeometry.Morphisms.Proper.FibreDescent
public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts

/-!
# Descending a projective presentation through the original point blowup

The exceptional fibre of the specified regular point blowup is the original
projective line over the full residue field. Its conormal and the positive twist
of the supplied embedding invoke the projective contraction theorem. Equality
of the full pulled-back point ideals identifies the two exceptional fibres.
Actual proper fibre descent constructs both target maps; its uniqueness proves
that they are inverse and preserves the original affine-base triangle.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.Surfaces.Contraction

open Blowup Blowup.RegularPoint

private theorem normalStalks_of_regularStalks {X : Scheme.{u}}
    (hX : RegularStalks X) : NormalStalks X := by
  intro x
  let : IsRegularLocalRing (X.presheaf.stalk x) := hX x
  exact ⟨IsRegularLocalRing.isDomain_of_regularLocal _,
    IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _⟩

private theorem ne_genericPoint_of_dimension_two {X : Scheme.{u}} [IsIntegral X]
    (x : X) (hd : ringKrullDim (X.presheaf.stalk x) = 2) : x ≠ genericPoint X := by
  intro h
  subst x
  change ringKrullDim X.functionField = 2 at hd
  rw [ringKrullDim_eq_zero_of_field] at hd
  norm_num at hd

private theorem cancel_of_proper_structureSheaf_iso {X Y T : Scheme.{u}}
    (b : X ⟶ Y) [IsProper b] [Surjective b] [IsIso b.c]
    (f g : Y ⟶ T) (h : b ≫ f = b ≫ g) : f = g := by
  obtain ⟨a, _, ha⟩ := existsUnique_factor_of_isProper_of_isIso_c b (b ≫ f)
    (fun x y hxy => congrArg f hxy)
  exact (ha f rfl).trans (ha g h.symm).symm

private theorem exists_iso_of_same_fibres {X Y T : Scheme.{u}}
    (b : X ⟶ Y) [IsProper b] [Surjective b] [IsIso b.c]
    (c : X ⟶ T) [IsProper c] [Surjective c] [IsIso c.c]
    (hbc : ∀ x y : X, b x = b y → c x = c y)
    (hcb : ∀ x y : X, c x = c y → b x = b y) :
    ∃ e : Y ≅ T, b ≫ e.hom = c ∧ c ≫ e.inv = b := by
  obtain ⟨f, hf, _⟩ := existsUnique_factor_of_isProper_of_isIso_c b c hbc
  obtain ⟨g, hg, _⟩ := existsUnique_factor_of_isProper_of_isIso_c c b hcb
  have hfg : f ≫ g = 𝟙 Y := by
    apply cancel_of_proper_structureSheaf_iso b
    rw [← Category.assoc, hf, hg, Category.comp_id]
  have hgf : g ≫ f = 𝟙 T := by
    apply cancel_of_proper_structureSheaf_iso c
    rw [← Category.assoc, hg, hf, Category.comp_id]
  exact ⟨⟨f, g, hfg, hgf⟩, hf, hg⟩

private theorem support_of_field_point {k : Type u} [Field k] {T : Scheme.{u}}
    (ρ : Spec (.of k) ⟶ T) [IsClosedImmersion ρ] :
    (ρ.ker.support : Set T) = {ρ (IsLocalRing.closedPoint k)} := by
  rw [Hom.support_ker, ρ.isClosedEmbedding.isClosed_range.closure_eq]
  ext t
  constructor
  · rintro ⟨z, rfl⟩
    exact congrArg ρ (Subsingleton.elim z _)
  · intro ht
    exact ⟨IsLocalRing.closedPoint k, ht.symm⟩

/-- Two actual contractions with the same full inverse-image point ideal have
isomorphic original targets. The comparison is built by proper fibre descent
in both directions, using the canonical blowup lift on the second target. -/
theorem exists_pointBlowup_target_iso
    {Z : Scheme.{u}} [IsIntegral Z] [IsLocallyNoetherian Z]
    (hZ : RegularStalks Z) (x : Z) (hx : IsClosed ({x} : Set Z))
    (hd : ringKrullDim (Z.presheaf.stalk x) = 2)
    {k : Type u} [Field k] {T : Scheme.{u}} [IsIntegral T]
    (hT : RegularStalks T) (ρ : Spec (.of k) ⟶ T) [IsClosedImmersion ρ]
    (ht : ringKrullDim (T.presheaf.stalk (ρ (IsLocalRing.closedPoint k))) = 2)
    (c : pointBlowup Z x ⟶ T) [IsProper c] [Surjective c]
    (hf : cartierPullback ρ.ker c)
    [IsIso ((blowupDatum ρ.ker).lift c hf)]
    (hideal : ρ.ker.comap c =
      (Z.fromSpecResidueField x).ker.comap (pointBlowdown Z x)) :
    ∃ e : Z ≅ T, pointBlowdown Z x ≫ e.hom = c ∧ c ≫ e.inv = pointBlowdown Z x := by
  let B := pointBlowupDatum Z x
  let D := blowupDatum ρ.ker
  let l := D.lift c hf
  let : IsClosedImmersion (Z.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hnx := ne_genericPoint_of_dimension_two x hd
  have hIB := genericPoint_not_mem_pointCentre x hx hnx
  let : IsIntegral B.Y := B.isIntegral_of_genericPoint_not_mem_support hIB
  let : IsDominant B.map := B.isDominant_of_genericPoint_not_mem_support hIB
  let : IsProper B.map := B.isProper_of_isLocallyNoetherian
  let : Surjective B.map := inferInstance
  let : IsIso B.map.c := isIso_c_of_isProper_birational B.map
    (normalStalks_of_regularStalks hZ) (B.functionFieldMap_isIso hIB)
  have hsρ := support_of_field_point ρ
  have hsx : ((Z.fromSpecResidueField x).ker.support : Set Z) = {x} := by
    rw [Hom.support_ker, range_fromSpecResidueField, hx.closure_eq]
  have hID : genericPoint T ∉ (ρ.ker.support : Set T) := by
    rw [hsρ]
    exact Ne.symm (ne_genericPoint_of_dimension_two _ ht)
  let : IsIntegral D.Y := D.isIntegral_of_genericPoint_not_mem_support hID
  let : IsDominant D.map := D.isDominant_of_genericPoint_not_mem_support hID
  let : IsIso l := inferInstance
  let : IsDominant c := inferInstance
  let : IsDominant l := inferInstance
  let : IsIso (CommRingCat.ofHom (functionFieldMap D.map)) :=
    D.functionFieldMap_isIso hID
  let : IsIso (CommRingCat.ofHom (functionFieldMap l)) := FunctionField.fieldMap_isIso l
  have hcff : IsIso (CommRingCat.ofHom (functionFieldMap c)) := by
    have hfield : functionFieldMap (l ≫ D.map) = functionFieldMap c := by
      congr 1
      exact D.lift_map c hf
    rw [← hfield, functionFieldMap_comp, CommRingCat.ofHom_comp]
    infer_instance
  let : IsIso c.c := isIso_c_of_isProper_birational c
    (normalStalks_of_regularStalks hT) hcff
  have hcentre (z : B.Y) : c z = ρ (IsLocalRing.closedPoint k) ↔ B.map z = x := by
    have hs := congrArg (fun I : B.Y.IdealSheafData => z ∈ (I.support : Set B.Y)) hideal
    rw [IdealSheafData.support_comap, IdealSheafData.support_comap] at hs
    change (c z ∈ (ρ.ker.support : Set T)) =
      (B.map z ∈ ((Z.fromSpecResidueField x).ker.support : Set Z)) at hs
    rw [hsρ, hsx] at hs
    exact iff_of_eq hs
  have hl (z : B.Y) : D.map (l z) = c z :=
    congrArg (fun f : B.Y ⟶ T => f z) (D.lift_map c hf)
  apply exists_iso_of_same_fibres B.map c
  · intro z₁ z₂ hz
    by_cases h₁ : B.map z₁ = x
    · exact ((hcentre z₁).mpr h₁).trans ((hcentre z₂).mpr (hz.symm.trans h₁)).symm
    · have h₂ : B.map z₂ ≠ x := fun h => h₁ (hz.trans h)
      exact congrArg c (B.map_injective_away (by rwa [hsx]) (by rwa [hsx]) hz)
  · intro z₁ z₂ hz
    by_cases h₁ : c z₁ = ρ (IsLocalRing.closedPoint k)
    · exact ((hcentre z₁).mp h₁).trans ((hcentre z₂).mp (hz.symm.trans h₁)).symm
    · have h₂ : c z₂ ≠ ρ (IsLocalRing.closedPoint k) := fun h => h₁ (hz.trans h)
      have he : l z₁ = l z₂ := D.map_injective_away
        (by rwa [hl, hsρ]) (by rwa [hl, hsρ]) (by rwa [hl, hl])
      exact congrArg B.map (l.isOpenEmbedding.injective he)

/-- A finite projective presentation of the original regular point blowup
descends to a finite projective presentation of its original target over the
same ring and the same structural map. -/
theorem exists_projective_embedding_of_pointBlowup
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {Z : Scheme.{u}} [IsIntegral Z] [IsNoetherian Z]
    (hZ : RegularStalks Z) (x : Z) (hx : IsClosed ({x} : Set Z))
    (hd : ringKrullDim (Z.presheaf.stalk x) = 2)
    (q : Z ⟶ Spec (.of A)) {I : Type u} [Finite I]
    (p : pointBlowup Z x ⟶ ProjectiveSpace A I) [IsClosedImmersion p]
    (hp : p ≫ toSpec A I = pointBlowdown Z x ≫ q) :
    ∃ (J : Type u) (j : Z ⟶ ProjectiveSpace A J),
      Finite J ∧ IsClosedImmersion j ∧ j ≫ toSpec A J = q := by
  classical
  let k := ResidueField (Z.presheaf.stalk x)
  let : IsRegularLocalRing (Z.presheaf.stalk x) := hZ x
  have hnx := ne_genericPoint_of_dimension_two x hd
  let : IsIntegral (pointBlowup Z x) := pointBlowup_isIntegral Z x hx hnx
  let : IsClosedImmersion (pointExceptionalι Z x) :=
    pointExceptionalι_isClosedImmersion Z x hx
  let e₀ := pointExceptionalOverIsoProjectiveP1 Z x hx hd
  let e : pointExceptionalFibre Z x ≅ ProjectiveSpace k (ULift.{u} (Fin 2)) :=
    (Over.forget _).mapIso e₀ ≪≫ finUliftIso k 2
  let i := e.inv ≫ pointExceptionalι Z x
  let : IsClosedImmersion i := inferInstance
  let a : Hom.idealModule (pointExceptionalι Z x) ≅ Hom.idealModule i :=
    identityBaseIdealIso (pointExceptionalι Z x) i e.symm rfl
  have hI : IsLocallyRankOne (pointBlowup Z x) (Hom.idealModule i) :=
    isLocallyRankOne_of_iso _ a (pointIdealLine Z x hx).property
  let eC : (Scheme.Modules.pullback (pointExceptionalι Z x)).obj
      (Hom.idealModule (pointExceptionalι Z x)) ≅
      (Scheme.Modules.pullback e.hom).obj (twistingSheaf k (ULift.{u} (Fin 2)) 1) :=
    (pointConormalProjectiveP1Iso Z x hx hd).symm ≪≫
      (pullbackComp e₀.hom.left (finUliftIso k 2).hom).app
        (twistingSheaf k (ULift.{u} (Fin 2)) 1)
  let eI : (Scheme.Modules.pullback i).obj (Hom.idealModule i) ≅
      twistingSheaf k (ULift.{u} (Fin 2)) 1 :=
    (Scheme.Modules.pullback i).mapIso a.symm ≪≫
      ((pullbackComp e.inv (pointExceptionalι Z x)).app
        (Hom.idealModule (pointExceptionalι Z x))).symm ≪≫
      (Scheme.Modules.pullback e.inv).mapIso eC ≪≫
      (pullbackComp e.inv e.hom).app (twistingSheaf k (ULift.{u} (Fin 2)) 1) ≪≫
      (pullbackCongr e.inv_hom_id).app (twistingSheaf k (ULift.{u} (Fin 2)) 1) ≪≫
      (pullbackId _).app (twistingSheaf k (ULift.{u} (Fin 2)) 1)
  let H := pullbackLineBundle p (twistingLineBundle A I 1)
  obtain ⟨d, hdpos, ⟨eH₀⟩⟩ := Line.exists_positiveTwist_of_isClosedImmersion_over_ring (i ≫ p)
  let eH : (Scheme.Modules.pullback i).obj H.val ≅
      twistingSheaf k (ULift.{u} (Fin 2)) (d : ℤ) :=
    (pullbackComp i p).app (twistingSheaf A I 1) ≪≫ eH₀
  let : Nonempty I := ⟨(coordinateAffineOpenCover A I).idx
    (p (genericPoint (pointBlowup Z x)))⟩
  let : Fintype I := Fintype.ofFinite I
  let r := Fintype.card I - 1
  have hcard : Fintype.card I = r + 1 := (Nat.sub_add_cancel Fintype.card_pos).symm
  let eIcoord : I ≃ Fin (r + 1) := Fintype.equivFinOfCardEq hcard
  obtain ⟨T, c, ρ, s, hf, hc, hcp, hρ, _, hTN, hTR, hTI, ht,
      hbl, hfull, _, hbase, ⟨J, j, hJ, hj, hjs⟩, _⟩ :=
    exists_cartier_projective_contraction (p := p) i hI H (eP := Iso.refl _) d
      (regularStalks_pointBlowup Z hZ x hx hd) r eIcoord eI eH hdpos
  let : IsNoetherian T := hTN
  let : IsIntegral T := hTI
  let : IsProper c := hcp
  let : Surjective c := hc
  let : IsClosedImmersion ρ := hρ
  let : IsIso ((blowupDatum ρ.ker).lift c hf) := hbl
  let : IsClosedImmersion (Z.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have hfull' : ρ.ker.comap c =
      (Z.fromSpecResidueField x).ker.comap (pointBlowdown Z x) := by
    rw [hfull]
    change (e.inv ≫ pullback.fst (pointBlowdown Z x) (Z.fromSpecResidueField x)).ker = _
    rw [Hom.ker_comp_of_isIso, IdealSheafData.ker_fst_of_isClosedImmersion]
  obtain ⟨ε, hε, _⟩ := exists_pointBlowup_target_iso hZ x hx hd hTR ρ ht c hf hfull'
  let : Finite J := hJ
  let : IsClosedImmersion j := hj
  have hIB := genericPoint_not_mem_pointCentre x hx hnx
  let B := pointBlowupDatum Z x
  let : IsProper B.map := B.isProper_of_isLocallyNoetherian
  let : IsDominant B.map := B.isDominant_of_genericPoint_not_mem_support hIB
  let : Surjective B.map := inferInstance
  let : IsIso B.map.c := isIso_c_of_isProper_birational B.map
    (normalStalks_of_regularStalks hZ) (B.functionFieldMap_isIso hIB)
  refine ⟨J, ε.hom ≫ j, hJ, inferInstance, ?_⟩
  apply cancel_of_proper_structureSheaf_iso B.map
  calc
    B.map ≫ (ε.hom ≫ j) ≫ toSpec A J = c ≫ s := by
      rw [Category.assoc, hjs, ← Category.assoc, hε]
    _ = B.map ≫ q := hbase.trans hp

end AlgebraicGeometry.Scheme.Surfaces.Contraction
