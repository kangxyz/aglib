/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.PointedEtale.Unchanged
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Blowup.Comparison
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.ResidueNodeInfinity

/-!
Native extraction from the R5 local-model source
`PointedResolution.PointedEtale.Runs`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`ff1e06845b3b68ef4240398b750d3a1cd8106afc24c3284414e86d83520a9580`.
Only source230–291 initialChart/State/initial_blowup. Additional actual
  originalRun/modification/properness are selected from ResolutionGeometry239–284; no
  discriminant-thickness constructor, generic model geometry, or marked endpoint is imported.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode WeierstrassCurve
universe u

section WeierstrassPointedInvariant


/-! Actual initial and accepted-first-blowup states for the original given
Weierstrass equation. The initial common chart is genuinely shrunk so its
whole two centre fibres are the same Spec of the original residue field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
open WeierstrassCurve.CriticalNeighborhood
open WeierstrassCurve.Projective
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (n : ℕ)
  (hn : 0 < n)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ n))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)

/-- The common pointed etale chart of the given Weierstrass equation and power node, shrunk to
preserve both full centre fibres. -/
def initialChart : Chart (scheme W) π hπ n hn := by
  let p := M.commonResiduePoint he ρ hρ
  let f := ProjectiveNodeBlowup.commonToProjective M
  let q := residueNodeMap W x y he
  let g := M.toPowerNodeScheme (π ^ n) a ha
  let r := NextCenter.origin π hπ n hn
  have h : p ≫ f = q := ProjectiveNodeBlowup.commonResidue_projective_triangle M he ρ hρ
  have k : p ≫ g = r := by
    rw [M.residue_power_triangle he ρ hρ (π ^ n) a ha]
    rfl
  exact {
    C := (AlgebraicGeometry.Etale.PointShrinking.Common.commonOpen p f q h g r k).toScheme
    toGlobal := AlgebraicGeometry.Etale.PointShrinking.Common.toLeft p f q h g r k
    toNode := AlgebraicGeometry.Etale.PointShrinking.Common.toRight p f q h g r k
    global_etale := inferInstance
    node_etale := inferInstance
    point := AlgebraicGeometry.Etale.PointShrinking.Common.point p f q h g r k
    globalPoint := q
    globalPoint_closed := inferInstance
    global_square := AlgebraicGeometry.Etale.PointShrinking.Common.left_isPullback p f q h g r k
    node_square := AlgebraicGeometry.Etale.PointShrinking.Common.right_isPullback p f q h g r k }

/-- Identity starts the actual finite sequence on the original projective
surface; it does not blow up the regular n=1 case. -/
def initialState : State (scheme W) (residueNodeMap W x y he) π hπ n hn where
  Y := scheme W
  map := 𝟙 _
  proper := inferInstance
  noetherian := ProjectiveNodeBlowup.projective_isLocallyNoetherian
  chart := initialChart M π hπ n hn a ha he ρ hρ
  point_triangle := by simp [initialChart]

/-- The chosen global first blowup is literally the accepted projective one. -/
lemma initial_blowup (m : ℕ)
    (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (m + 2)))
    (hex : NoetherianBlowupExistence.{u}) :
    State.blowup (initialState M π hπ (m + 2) (by omega) a ha he ρ hρ) hex =
      ProjectiveNodeBlowup.projectiveBlowup he hex := rfl

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end
end WeierstrassPointedInvariant

section WeierstrassFiniteModification


/-! The constructive finite trace on the original equation preserves its
actual residue-node complement, infinity section and fraction-field fibre.
Global regularity and integrality remain separate subsequent obligations. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
open WeierstrassCurve.CriticalNeighborhood
open WeierstrassCurve.Projective
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}

lemma originalComplement_disjoint (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y) :
    Disjoint (residueNodeComplement W x y he : Set (scheme W)) (Set.range (residueNodeMap W x y
      he)) := by
  apply Set.disjoint_left.mpr
  rintro z hz ⟨w, rfl⟩
  change residueNodeMap W x y he w ≠ residueNode W x y he at hz
  exact hz (congrArg (residueNodeMap W x y he) (Subsingleton.elim w (closedPoint (ResidueField R))))

variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (n : ℕ)
  (hn : 0 < n)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ n))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})

/-- The finite pointed blowup run starting from the given Weierstrass equation and its initial
chart. -/
def originalRun := run hex hp hatlas hbc n hn (initialState M π hπ n hn a ha he ρ hρ)

/-- The composite proper modification of the given projective Weierstrass scheme supplied by its
pointed run. -/
def modification : (originalRun M π hπ n hn a ha he ρ hρ hex hp hatlas hbc).source ⟶ scheme W :=
  (originalRun M π hπ n hn a ha he ρ hρ hex hp hatlas hbc).toOriginal

instance modification_proper : IsProper (modification M π hπ n hn a ha he ρ hρ hex hp hatlas hbc) :=
  inferInstanceAs (IsProper (originalRun M π hπ n hn a ha he ρ hρ hex hp hatlas hbc).toOriginal)

instance complement_unchanged :
    IsIso (modification M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ∣_ residueNodeComplement W x y
      he) := by
  apply Run.unchanged _ _ (originalComplement_disjoint he)
  change IsIso ((𝟙 (scheme W)) ∣_ _)
  infer_instance


end AlgebraicGeometry.Scheme.PowerNode.PointedEtale
end
end WeierstrassFiniteModification
