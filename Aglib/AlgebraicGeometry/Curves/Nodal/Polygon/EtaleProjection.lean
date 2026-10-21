/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Nodal.Polygon.Projection
public import Aglib.RingTheory.Etale.MilnorPatching.Unramified
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.RankOne
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Basic

/-!
# Finite étale properties of the polygon projection

The rings and maps are the canonical objects in `Scheme.Polygon`. The actual
conductor map is a split-power Milnor map, so its étaleness follows from the
proved finite-free supplier without an assumed universal patching family.

Source: frozen R5 `Curves/Cyclic/Covers/FiniteCover.lean`, lines 44–126,
153–162, 182–191, 225–366, 382–470 and 607–614, revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`b96dbafa96b00d65651d1f9b2e777bc889c72e9e02c218b154c2a17813a33f37`.
All ranks concern the literal projection, for every natural level including zero.
Positivity is required only for connectedness and surjectivity.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry Polynomial
open RingHom.Etale
open scoped Polynomial TensorProduct
open AlgebraicGeometry.Scheme.OverField (FScheme HasGeometricDegree)
open AlgebraicGeometry.Scheme.Hom (coordinateAlgebra HasGeometricFibreRank
  hasGeometricFibreRank_iff_hasGeometricDegree)

universe u

namespace AlgebraicGeometry.Scheme.Polygon

variable (k : Type u) [Field k] (n : ℕ)

/-- The actual conductor fibre product of the pinched line. -/
abbrev baseFiberRing := MilnorPatching.fiberRing (baseBoundary k).toRingHom
  (algebraMap k (k × k))
/-- The conductor fibre product with the native cyclic boundary convention. -/
abbrev cycleFiberRing := MilnorPatching.fiberRing (normalizationBoundary k n).toRingHom
  (nodeBoundary k n).toRingHom

theorem normalizationDiagonal_square :
    (normalizationBoundary k n).toRingHom.comp
      (algebraMap k[X] (NormalizationRing k n)) =
      (algebraMap (k × k) (BoundaryRing k n)).comp (baseBoundary k).toRingHom := by
  ext p i <;> rfl

theorem nodeDiagonal_square :
    (nodeBoundary k n).toRingHom.comp (algebraMap k (NodeValues k n)) =
      (algebraMap (k × k) (BoundaryRing k n)).comp (algebraMap k (k × k)) := by
  ext a i <;> rfl

/-- The literal map of the two actual conductor fibre-product rings. -/
def fiberBaseMap : baseFiberRing k →+* cycleFiberRing k n :=
  MilnorPatching.fiberMap (baseBoundary k).toRingHom (algebraMap k (k × k))
    (algebraMap k[X] (NormalizationRing k n)) (algebraMap k (NodeValues k n))
    (algebraMap (k × k) (BoundaryRing k n)) (normalizationBoundary k n).toRingHom
    (nodeBoundary k n).toRingHom (normalizationDiagonal_square k n) (nodeDiagonal_square k n)

/-- The native normalization boundary is the pointwise endpoint ring map. -/
theorem normalizationBoundary_eq_compLeft :
    (normalizationBoundary k n).toRingHom = (baseBoundary k).toRingHom.compLeft (Fin n) := by
  ext p i <;> rfl

/-- The native node boundary is the pointwise diagonal followed by the actual
first-branch cyclic twist. The second branch keeps the current index. -/
theorem nodeBoundary_eq_twisted_compLeft :
    (nodeBoundary k n).toRingHom = (boundaryTwist k n).toRingHom.comp
      ((algebraMap k (k × k)).compLeft (Fin n)) := by
  ext a i <;> rfl

/-- The concrete finite split-power Milnor theorem applies to the exact native
conductor map. No universal `EtalePatching` proposition is assumed. -/
theorem fiberBaseMap_etale : (fiberBaseMap k n).Etale := by
  change (MilnorPatching.FiniteFree.map (baseBoundary k).toRingHom
    (algebraMap k (k × k)) (boundaryTwist k n)).Etale
  exact MilnorPatching.FiniteFree.etale_map (baseBoundary k).toRingHom
    (algebraMap k (k × k)) (boundaryTwist k n) (baseBoundary_surjective k)

/-- The base conductor fibre product is the actual pinched polynomial ring. -/
def baseFiberEquiv : Polynomial.PinchedPair.nodeRing k ≃+* baseFiberRing k where
  toFun p := ⟨(p.val, p.val.eval 0), by
    change (p.val.eval 0, p.val.eval 1) = (p.val.eval 0, p.val.eval 0)
    exact Prod.ext rfl p.property.symm⟩
  invFun p := ⟨p.val.1, by
    have h₀ := congrArg Prod.fst p.property
    have h₁ := congrArg Prod.snd p.property
    exact h₀.trans h₁.symm⟩
  left_inv p := rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Prod.fst p.property
  map_mul' p q := by apply Subtype.ext; exact Prod.ext rfl Polynomial.eval_mul
  map_add' p q := by apply Subtype.ext; exact Prod.ext rfl Polynomial.eval_add

/-- Subalgebra and subring presentations of the same actual equations. -/
def cycleFiberEquiv : nodeRing k n ≃+* cycleFiberRing k n :=
  (fiberEquiv k n).toRingEquiv.trans
  { toFun := fun p => ⟨p.val, p.property⟩
    invFun := fun p => ⟨p.val, p.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

/-- Comparison with the actual diagonal map, without choosing another cover. -/
theorem baseMap_eq_fiberMap :
    (baseMap k n).toRingHom = (cycleFiberEquiv k n).symm.toRingHom.comp
      ((fiberBaseMap k n).comp (baseFiberEquiv k).toRingHom) := by
  ext p i
  rfl

/-- The literal diagonal map from the one-gon node to the polygon node is
étale for every natural level, with no characteristic restriction. -/
theorem baseMap_etale : (baseMap k n).toRingHom.Etale := by
  rw [baseMap_eq_fiberMap]
  apply RingHom.Etale.stableUnderComposition
  · exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective (baseFiberEquiv k).bijective) (fiberBaseMap_etale k n)
  · exact RingHom.Etale.of_bijective (cycleFiberEquiv k n).symm.bijective

/-- The canonical affine polygon projection is étale at every level. -/
instance affineMap_etale : Etale (affineMap k n) := by
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (baseMap_etale k n)

/-- Actual connected finite étale surjective affine cyclic cover of the node
chart. This is not yet a proper projective polygon or a model cover. -/
theorem actual_affine_cycle [NeZero n] :
    IsFinite (affineMap k n) ∧ Etale (affineMap k n) ∧
      Function.Surjective (affineMap k n) ∧ ConnectedSpace (nodeScheme k n) :=
  ⟨inferInstance, affineMap_etale k n, affineMap_surjective k n, nodeScheme_connected k n⟩

/-- The canonical split infinity projection is finite at every level. -/
instance infinityMap_finite : IsFinite (infinityMap k n) := by
  have : Module.Finite (V k) (V k) := Module.Finite.self _
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr
    (inferInstance : Module.Finite (V k) (Fin n → V k))

/-- The canonical split infinity projection is étale at every level. -/
instance infinityMap_etale : Etale (infinityMap k n) := by
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
  exact RingHom.etale_algebraMap.mpr inferInstance

theorem gluingToNode_range : (gluingToNode k n).opensRange =
    PrimeSpectrum.basicOpen (conductor k n) := by
  change ((conductorOpenIso k n).hom ≫ nodeOverlapInclusion k n).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact Scheme.Hom.opensRange_localizationAway (R := .of (nodeRing k n)) (conductor k n)

theorem base_gluingToNode_range : (Scheme.PinchedLine.gluingToNode k).opensRange =
    PrimeSpectrum.basicOpen (Polynomial.PinchedPair.conductor k) := by
  change ((Scheme.PinchedLine.conductorOpenIso k).hom ≫
    Scheme.PinchedLine.nodeOverlapInclusion k).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact Scheme.Hom.opensRange_localizationAway (R := .of (Polynomial.PinchedPair.nodeRing k))
    (Polynomial.PinchedPair.conductor k)

theorem gluingToInfinity_range : (gluingToInfinity k n).opensRange =
    PrimeSpectrum.basicOpen (fun _ : Fin n => algebraMap k[X] (V k) X) := by
  change ((Scheme.Spec.mapIso (reciprocalEquiv k n).toRingEquiv.toCommRingCatIso.op).hom ≫
    (Scheme.Spec.mapIso (standardOverlapEquiv k n).toCommRingCatIso.symm.op).hom ≫
    infinityOverlapInclusion k n).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_comp_of_isIso]
  rw [SetLike.ext'_iff]
  exact PrimeSpectrum.localization_away_comap_range (productInfinityOverlapRing k n)
    (fun _ : Fin n => algebraMap k[X] (V k) X)

theorem base_gluingToInfinity_range : (Scheme.PinchedLine.gluingToInfinity k).opensRange =
    PrimeSpectrum.basicOpen (algebraMap k[X] (V k) X) := by
  change ((Scheme.PinchedLine.reciprocalSchemeIso k).hom ≫
    (Scheme.PinchedLine.standardOverlapSpecIso k).hom ≫
      Scheme.PinchedLine.infinityOverlapInclusion k).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_comp_of_isIso]
  exact Scheme.Hom.opensRange_localizationAway (R := .of (V k)) (algebraMap k[X] (V k) X)

theorem affine_overlap_preimage :
    affineMap k n ⁻¹ᵁ (Scheme.PinchedLine.gluingToNode k).opensRange = (gluingToNode k
      n).opensRange := by
  rw [base_gluingToNode_range, gluingToNode_range]
  ext p
  rfl

theorem infinity_overlap_preimage :
    infinityMap k n ⁻¹ᵁ (Scheme.PinchedLine.gluingToInfinity k).opensRange =
      (gluingToInfinity k n).opensRange := by
  rw [base_gluingToInfinity_range, gluingToInfinity_range]
  ext p
  rfl

/-- No infinity point is inadvertently added to the inverse image of the
node-containing chart: the overlap preimage is the proved principal open. -/
theorem cycleMap_preimage_affine :
    cycleMap k n ⁻¹ᵁ (pushout.inl (Scheme.PinchedLine.gluingToNode k)
      (Scheme.PinchedLine.gluingToInfinity k)).opensRange =
      (pushout.inl (gluingToNode k n) (gluingToInfinity k n)).opensRange := by
  ext z
  change (∃ x, pushout.inl (Scheme.PinchedLine.gluingToNode k)
    (Scheme.PinchedLine.gluingToInfinity k) x = cycleMap k n z) ↔ ∃ x, pushout.inl (gluingToNode
    k n) (gluingToInfinity k n) x = z
  constructor
  · rintro ⟨x, hx⟩
    rcases Scheme.openPushout_covered (gluingToNode k n) (gluingToInfinity k n) z with
      ⟨a, rfl⟩ | ⟨v, rfl⟩
    · exact ⟨a, rfl⟩
    · have he :
          pushout.inl (Scheme.PinchedLine.gluingToNode k)
              (Scheme.PinchedLine.gluingToInfinity k) x =
            pushout.inr (Scheme.PinchedLine.gluingToNode k)
              (Scheme.PinchedLine.gluingToInfinity k) (infinityMap k n v) := by
        simpa only [← Scheme.Hom.comp_apply, cycleMap_infinity] using hx
      obtain ⟨w, _, hw⟩ := (Scheme.OpenNormalizationGluing.left_eq_right_iff
        (Scheme.PinchedLine.gluingToNode k) (Scheme.PinchedLine.gluingToInfinity k) _ _).mp he
      have hv : v ∈ (gluingToInfinity k n).opensRange := by
        rw [← infinity_overlap_preimage]
        exact ⟨w, hw⟩
      obtain ⟨w', rfl⟩ := hv
      refine ⟨gluingToNode k n w', ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pushout.condition]
  · rintro ⟨x, rfl⟩
    refine ⟨affineMap k n x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, cycleMap_affine]

theorem cycleMap_preimage_infinity :
    cycleMap k n ⁻¹ᵁ (pushout.inr (Scheme.PinchedLine.gluingToNode k)
      (Scheme.PinchedLine.gluingToInfinity k)).opensRange =
      (pushout.inr (gluingToNode k n) (gluingToInfinity k n)).opensRange := by
  ext z
  change (∃ v, pushout.inr (Scheme.PinchedLine.gluingToNode k)
    (Scheme.PinchedLine.gluingToInfinity k) v = cycleMap k n z) ↔ ∃ v, pushout.inr (gluingToNode
    k n) (gluingToInfinity k n) v = z
  constructor
  · rintro ⟨v, hv⟩
    rcases Scheme.openPushout_covered (gluingToNode k n) (gluingToInfinity k n) z with
      ⟨a, rfl⟩ | ⟨v', rfl⟩
    · have he :
          pushout.inl (Scheme.PinchedLine.gluingToNode k)
              (Scheme.PinchedLine.gluingToInfinity k) (affineMap k n a) =
            pushout.inr (Scheme.PinchedLine.gluingToNode k)
              (Scheme.PinchedLine.gluingToInfinity k) v := by
        symm
        simpa only [← Scheme.Hom.comp_apply, cycleMap_affine] using hv
      obtain ⟨w, hw, _⟩ := (Scheme.OpenNormalizationGluing.left_eq_right_iff
        (Scheme.PinchedLine.gluingToNode k) (Scheme.PinchedLine.gluingToInfinity k) _ _).mp he
      have ha : a ∈ (gluingToNode k n).opensRange := by
        rw [← affine_overlap_preimage]
        exact ⟨w, hw⟩
      obtain ⟨w', rfl⟩ := ha
      refine ⟨gluingToInfinity k n w', ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pushout.condition]
    · exact ⟨v', rfl⟩
  · rintro ⟨v, rfl⟩
    refine ⟨infinityMap k n v, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, cycleMap_infinity]

theorem cycleMap_affine_isPullback :
    IsPullback (affineMap k n) (pushout.inl (gluingToNode k n) (gluingToInfinity k n))
      (pushout.inl (Scheme.PinchedLine.gluingToNode k) (Scheme.PinchedLine.gluingToInfinity k))
        (cycleMap k n) :=
  IsOpenImmersion.isPullback (affineMap k n) _ _ _ (cycleMap_affine k n)
    (cycleMap_preimage_affine k n)

theorem cycleMap_infinity_isPullback :
    IsPullback (infinityMap k n) (pushout.inr (gluingToNode k n) (gluingToInfinity k n))
      (pushout.inr (Scheme.PinchedLine.gluingToNode k) (Scheme.PinchedLine.gluingToInfinity k))
        (cycleMap k n) :=
  IsOpenImmersion.isPullback (infinityMap k n) _ _ _ (cycleMap_infinity k n)
    (cycleMap_preimage_infinity k n)

/-- The literal global polygon projection is finite. -/
instance cycleMap_finite : IsFinite (cycleMap k n) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @AlgebraicGeometry.IsFinite)
    (Scheme.OpenNormalizationGluing.twoChartCover
      (Scheme.PinchedLine.gluingToNode k) (Scheme.PinchedLine.gluingToInfinity k))
  intro b
  cases b
  · change IsFinite (pullback.snd (cycleMap k n) (pushout.inl _ _))
    rw [← (cycleMap_affine_isPullback k n).flip.isoPullback_inv_snd]
    infer_instance
  · change IsFinite (pullback.snd (cycleMap k n) (pushout.inr _ _))
    rw [← (cycleMap_infinity_isPullback k n).flip.isoPullback_inv_snd]
    infer_instance

/-- The literal global polygon projection is étale, using the two actual charts. -/
instance cycleMap_etale : Etale (cycleMap k n) := by
  have := affineMap_etale k n
  apply IsZariskiLocalAtSource.of_openCover (P := @Etale)
    (Scheme.OpenNormalizationGluing.twoChartCover (gluingToNode k n) (gluingToInfinity k n))
  intro b
  cases b
  · change Etale (pushout.inl _ _ ≫ cycleMap k n)
    rw [cycleMap_affine]
    infer_instance
  · change Etale (pushout.inr _ _ ≫ cycleMap k n)
    rw [cycleMap_infinity]
    infer_instance

/-- The polygon structure map is proper through its finite projection. -/
instance structureMap_proper : IsProper (structureMap k n) := by
  unfold structureMap
  infer_instance

/-- The literal finite étale polygon projection is flat. -/
theorem cycleMap_flat : Flat (cycleMap k n) := inferInstance

/-- The actual split infinity algebra has rank equal to the level. -/
theorem infinityMap_finrank (p : Spec (.of (V k))) : (infinityMap k n).finrank p = n := by
  have : Module.Finite (V k) (V k) := Module.Finite.self _
  rw [infinityMap, Scheme.Hom.finrank_SpecMap_algebraMap,
    Module.rankAtStalk_eq_finrank_of_free]
  change Module.finrank (V k) (Fin n → V k) = n
  exact Module.finrank_fin_fun (V k)

/-- Genuine rank n of the actual proper finite etale cycle morphism. -/
theorem cycleMap_finrank
    (p : Scheme.PinchedLine.pinchedGluing k) : (cycleMap k n).finrank p = n := by
  have := cycleMap_etale k n
  let q : Spec (.of (V k)) := Classical.choice (inferInstance : Nonempty (Spec (.of (V k))))
  have hconst := (cycleMap k n).isLocallyConstant_finrank.apply_eq_of_preconnectedSpace p
    (pushout.inr (Scheme.PinchedLine.gluingToNode k) (Scheme.PinchedLine.gluingToInfinity k) q)
  rw [hconst, ← Scheme.Hom.finrank_of_isPullback _ _ _ _ (cycleMap_infinity_isPullback k n).flip]
  exact infinityMap_finrank k n q

/-- Rank n persists after every actual scheme base change. -/
theorem cycleMap_baseChange_finrank {T : Scheme.{u}}
    (g : T ⟶ Scheme.PinchedLine.pinchedGluing k) (t : T) :
    (pullback.snd (cycleMap k n) g).finrank t = n := by
  have := cycleMap_etale k n
  rw [Scheme.Hom.finrank_pullback_snd]
  exact cycleMap_finrank k n _

theorem cycleMap_surjective [NeZero n] :
    Surjective (cycleMap k n) := by
  have := cycleMap_etale k n
  apply (Scheme.Hom.one_le_finrank_iff_surjective (cycleMap k n)).mp
  intro p
  rw [cycleMap_finrank k n]
  exact Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)

/-- Concrete connected proper n-sheet finite etale cycle cover. Projective
component and normalization identifications remain separate outputs. -/
theorem actual_global_cycle [NeZero n] :
    IsFinite (cycleMap k n) ∧ Etale (cycleMap k n) ∧ Surjective (cycleMap k n) ∧
      ConnectedSpace (cycleScheme k n) ∧ IsProper (structureMap k n) ∧
      ∀ p, (cycleMap k n).finrank p = n :=
  ⟨inferInstance, cycleMap_etale k n, cycleMap_surjective k n,
    cycleScheme_connected k n, inferInstance, cycleMap_finrank k n⟩

/-- The polygon as a scheme over its actual coefficient field. -/
def cycleSourceScheme : FScheme k := Over.mk (structureMap k n)
/-- The pinched target as a scheme over the same coefficient field. -/
def cycleTargetScheme : FScheme k := Over.mk (Scheme.PinchedLine.pinchedStructure k)
/-- The same polygon projection as an over-field morphism. -/
def cycleMorphism : cycleSourceScheme k n ⟶ cycleTargetScheme k :=
  Over.homMk (cycleMap k n) rfl

/-- The underlying map of the over-field projection is finite. -/
instance cycleMorphism_finite : IsFinite (cycleMorphism k n).left := cycleMap_finite k n

/-- The underlying map of the over-field projection is étale. -/
instance cycleMorphism_etale :
    Etale (cycleMorphism k n).left := cycleMap_etale k n

/-- The actual fibre-coordinate algebra has dimension n over every field
mapping to the nodal target; this is the unchanged geometric-rank interface. -/
theorem cycleMap_geometricFibre_finrank
    (K : Type u) [Field K] (p : Spec (.of K) ⟶ Scheme.PinchedLine.pinchedGluing k) :
    letI : Algebra K Γ(pullback (cycleMap k n) p, ⊤) :=
      coordinateAlgebra K (Over.mk (pullback.snd (cycleMap k n) p))
    Module.finrank K Γ(pullback (cycleMap k n) p, ⊤) = n := by
  have := cycleMap_etale k n
  rw [← Scheme.Hom.FiniteFlat.nativeRank_geometricFibre]
  exact cycleMap_finrank k n _

theorem cycleMorphism_hasGeometricFibreRank :
    HasGeometricFibreRank (cycleMorphism k n) n := by
  intro K _ _ s y
  exact cycleMap_geometricFibre_finrank k n K y.left

/-- Same-map adapter to the unchanged all-geometric-field degree consumer. -/
theorem cycleMorphism_hasGeometricDegree :
    HasGeometricDegree (cycleMorphism k n) n := by
  have := cycleMorphism_etale k n
  exact (hasGeometricFibreRank_iff_hasGeometricDegree (cycleMorphism k n) n).mp
    (cycleMorphism_hasGeometricFibreRank k n)

/-- The literal polygon projection as an object of the finite étale cover category. -/
def finiteEtaleCycleCover :
    Scheme.FiniteEtale (Scheme.PinchedLine.pinchedGluing k) := by
  have := cycleMap_etale k n
  exact Scheme.FiniteEtale.mk (cycleMap k n)

@[simp] theorem finiteEtaleCycleCover_hom :
    (finiteEtaleCycleCover k n).obj.hom = cycleMap k n := rfl

end AlgebraicGeometry.Scheme.Polygon
