/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Construction
public import Aglib.AlgebraicGeometry.Blowup.Properness
public import Aglib.AlgebraicGeometry.Blowup.AffineAtlas
public import Aglib.AlgebraicGeometry.Blowup.FlatBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.Etale.ReducedDescent
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.ExceptionalFibres
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.WeierstrassStrictTransformClosure

/-!
# Reducedness of the same pointed Run residue fibre

Source: frozen R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
`CyclicModelComparison/ReducedResolvedFibre.lean`, lines 33–144, 165–199.
SHA-256: `210b89122602b5f6684df77360b856824c733fb9828ea93a9369bbea4be1d67e`.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.PowerNode

section PointedRunReducedChart

/-! The FULL common chart of the same Run, specialized over the original
residue field, is reduced by its actual étale map to the local resolution. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {X : Scheme.{u}} {q₀ : Spec (.of (ResidueField R)) ⟶ X}
  {π : R} {hπ : Irreducible π}
  {hex : NoetherianBlowupExistence.{u}} {hp : NoetherianBlowupProper.{u}}
  {hatlas : BlowupAffineAtlas.{u}} {hbc : BlowupFlatBaseChange.{u}}
  {n : ℕ} {hn : 0 < n} {S : State X q₀ π hπ n hn}
  (T : Run hex hp hatlas hbc S)

lemma fullCommonToGlobal_etale : Etale (fullCommonToGlobal T) := by
  exact MorphismProperty.of_isPullback (P := @Etale) (fullCommon_square T).flip inferInstance

lemma fullNodeComparison_etale : Etale (fullNodeComparison T) := by
  exact MorphismProperty.of_isPullback (P := @Etale)
    (fullNodeComparison_square T).flip inferInstance

variable (b : S.Y ⟶ Spec (.of R))
  (hb : S.chart.toGlobal ≫ b = S.chart.toNode ≫ Resolution.base)

include hb in
lemma fullCommon_structure :
    fullCommonToGlobal T ≫ T.map ≫ b =
      fullNodeComparison T ≫ (Resolution.resolve π hπ hex hp hatlas n).map ≫
        Resolution.base := by
  rw [← Category.assoc, fullCommon_triangle, Category.assoc, hb]
  rw [← fullNodeComparison_triangle_assoc]

/-- The residue-field fibre of the full common pullback over the base map `b`. -/
abbrev fullCommonSpecial : Scheme.{u} :=
  pullback (fullCommonToGlobal T ≫ T.map ≫ b) (Resolution.residueBase (R := R))

/-- The map from the full common special fibre to the final source special fibre induced by its
projection. -/
abbrev fullCommonSpecialMap : fullCommonSpecial T b ⟶
    pullback (T.map ≫ b) (Resolution.residueBase (R := R)) :=
  Scheme.baseChangeMap (fullCommonToGlobal T) (T.map ≫ b) Resolution.residueBase

lemma fullCommonSpecialMap_etale : Etale (fullCommonSpecialMap T b) := by
  let := fullCommonToGlobal_etale T
  dsimp [fullCommonSpecialMap]
  infer_instance

include hb in
lemma fullCommonSpecial_reduced :
    IsReduced (fullCommonSpecial T b) := by
  let : IsLocallyNoetherian (Resolution.sourceSpecialFibre
      (Resolution.resolve π hπ hex hp hatlas n)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd
      ((Resolution.resolve π hπ hex hp hatlas n).map ≫ Resolution.base)
      (Resolution.residueBase (R := R)))
  let := fullNodeComparison_etale T
  let : IsReduced (pullback
      ((Resolution.resolve π hπ hex hp hatlas n).map ≫ Resolution.base)
      (Resolution.residueBase (R := R))) := by
    simpa only [Resolution.sourceSpecialFibre] using
      Resolution.resolve_specialFibre_reduced π hπ hex hp hatlas n
  exact Scheme.isReduced_baseChange_of_comp_eq
    (fullNodeComparison T)
    ((Resolution.resolve π hπ hex hp hatlas n).map ≫ Resolution.base)
    Resolution.residueBase _ (fullCommon_structure T b hb)

/-- The actual full common chart covers every point over the original centre.
No rational point is lifted through an arbitrary étale map. -/
lemma fullCommonSpecialMap_covers_centre
    (z : (pullback (T.map ≫ b) (Resolution.residueBase (R := R)) : Scheme.{u}))
    (hz : (pullback.fst (T.map ≫ b) Resolution.residueBase ≫ T.map) z ∈
      Set.range S.chart.globalPoint) :
    z ∈ Set.range (fullCommonSpecialMap T b) := by
  rw [Scheme.Pullback.Transport.range_eq_preimage_of_isPullback
    (Scheme.baseChangeMap_isPullback (fullCommonToGlobal T)
      (T.map ≫ b) Resolution.residueBase).flip]
  change pullback.fst (T.map ≫ b) Resolution.residueBase z ∈
    Set.range (fullCommonToGlobal T)
  rw [Scheme.Pullback.Transport.range_eq_preimage_of_isPullback (fullCommon_square T)]
  obtain ⟨k, hk⟩ := hz
  refine ⟨S.chart.point k, ?_⟩
  simpa only [← Scheme.Hom.comp_apply, S.chart.point_global] using hk

include hb in
/-- A reduced unchanged open plus the actual full common chart proves the
same Run residue fibre reduced. The open-range identity is literal. -/
lemma specialFibre_reduced_of_unchanged
    (V : (pullback (T.map ≫ b) (Resolution.residueBase (R := R)) : Scheme.{u}).Opens)
    [IsReduced V]
    (hV : Set.range (Scheme.Opens.ι V) =
      (pullback.fst (T.map ≫ b) Resolution.residueBase ≫ T.map) ⁻¹'
        (Set.range S.chart.globalPoint)ᶜ) :
    IsReduced (pullback (T.map ≫ b) (Resolution.residueBase (R := R))) := by
  apply Scheme.reduced_of_pointwise_flat_cover
  intro z
  by_cases hz : (pullback.fst (T.map ≫ b) Resolution.residueBase ≫ T.map) z ∈
      Set.range S.chart.globalPoint
  · obtain ⟨y, hy⟩ := fullCommonSpecialMap_covers_centre T b z hz
    let := fullCommonSpecialMap_etale T b
    exact ⟨fullCommonSpecial T b, fullCommonSpecialMap T b, y, hy,
      inferInstance, fullCommonSpecial_reduced T b hb⟩
  · have hz' : z ∈ Set.range (Scheme.Opens.ι V) := by
      rw [hV]
      exact hz
    obtain ⟨y, hy⟩ := hz'
    exact ⟨V, Scheme.Opens.ι V, y, hy, inferInstance, inferInstance⟩

include hb in
/-- Explicit structural equalities transport the entire dependent unchanged
open and range certificate, rather than changing only its displayed points. -/
lemma specialFibre_reduced_of_structure
    (a : T.source ⟶ Spec (.of R)) (ha : a = T.map ≫ b)
    (r : Spec (.of (ResidueField R)) ⟶ Spec (.of R))
    (hr : r = Resolution.residueBase)
    (V : (pullback a r : Scheme.{u}).Opens) [IsReduced V]
    (hV : Set.range (Scheme.Opens.ι V) =
      (pullback.fst a r ≫ T.map) ⁻¹' (Set.range S.chart.globalPoint)ᶜ) :
    IsReduced (pullback a r) := by
  subst a
  subst r
  exact specialFibre_reduced_of_unchanged T b hb V hV

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run

end -- noncomputable section
end PointedRunReducedChart


section WeierstrassResolvedFibreReduced

/-! Reducedness of the literal same final residue fibre, proved from the full
common étale chart and the unchanged integral punctured cubic. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open AlgebraicGeometry.Scheme
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π)
  (n : ℕ) (hn : 0 < n)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ n))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
local notation "T" => originalRun M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "V" => strictPuncturedOpen M π hπ n hn a ha he ρ hρ hex hp hatlas hbc

/-- The original initial chart is over the same DVR on both projections. -/
lemma initialChart_structure :
    (initialState M π hπ n hn a ha he ρ hρ).chart.toGlobal ≫ structureMap W =
      (initialState M π hπ n hn a ha he ρ hρ).chart.toNode ≫
        Resolution.base := by
  have H : ProjectiveNodeBlowup.commonToProjective M ≫ structureMap W =
      M.toPowerNodeScheme (π ^ n) a ha ≫
        Resolution.base := by
    rw [ProjectiveNodeBlowup.commonToProjective, Category.assoc, affineChart_structure,
      M.original_structure_triangle, Resolution.base,
      M.power_structure_triangle]
  change (_ ≫ ProjectiveNodeBlowup.commonToProjective M) ≫ structureMap W =
    (_ ≫ M.toPowerNodeScheme (π ^ n) a ha) ≫ _
  rw [Category.assoc, H, Category.assoc]

lemma finalSpecialFibre_reduced :
    IsReduced (finalSpecialFibre M π hπ n hn a ha he ρ hρ hex hp hatlas hbc) := by
  have hb : (initialState M π hπ n hn a ha he ρ hρ).chart.toGlobal ≫ structureMap W =
      (initialState M π hπ n hn a ha he ρ hρ).chart.toNode ≫
        Resolution.base :=
    initialChart_structure M π hπ n hn a ha he ρ hρ
  have hf : modification M π hπ n hn a ha he ρ hρ hex hp hatlas hbc = (T).map := by
    simp only [modification, Run.toOriginal, initialState, Category.comp_id]
  apply Run.specialFibre_reduced_of_structure T (structureMap W) hb
    (modification M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫ structureMap W)
    (congrArg (· ≫ structureMap W) hf)
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
    (by rfl) V
  have H := strictPunctured_original_range_eq M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
  change Set.range (Scheme.Opens.ι V) =
    (pullback.fst
      (modification M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫ structureMap W)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ (T).map) ⁻¹'
        (Set.range (residueNodeMap W x y he))ᶜ
  exact H.trans (congrArg (fun g => g ⁻¹' (Set.range (residueNodeMap W x y he))ᶜ)
    (congrArg (fun (g : finalSpecialFibre M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ⟶ scheme W) =>
      (g : _ → _))
      (congrArg (pullback.fst
        (modification M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫ structureMap W)
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ ·) hf)))

/-- The same fibre reducedness using the four proved ordinary blowup suppliers. -/
theorem finalSpecialFibre_reduced_concrete :
    IsReduced (finalSpecialFibre M π hπ n hn a ha he ρ hρ
      Scheme.Blowup.noetherianBlowupExistence Scheme.Blowup.noetherianBlowupProper
      Scheme.Blowup.blowupAffineAtlas Scheme.Blowup.blowupFlatBaseChange) :=
  finalSpecialFibre_reduced M π hπ n hn a ha he ρ hρ
    Scheme.Blowup.noetherianBlowupExistence Scheme.Blowup.noetherianBlowupProper
    Scheme.Blowup.blowupAffineAtlas Scheme.Blowup.blowupFlatBaseChange

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassResolvedFibreReduced
