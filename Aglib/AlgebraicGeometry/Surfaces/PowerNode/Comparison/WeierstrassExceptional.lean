/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.ExceptionalComparison
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.PointedEtale.Weierstrass

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.ExceptionalComparison`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`bbcdcb52753990834123ae15628e4b96eb235ab2c3ee831891bec4c7f8a9d6d4`.
Only source470–535, specializing the generic actual exceptional comparison to the same original
  Weierstrass run. Every original input and projection is retained.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

section WeierstrassIteratedExceptionalComparison

/-! Specialization to the unchanged original Weierstrass Run and its literal
original residue-node fibre. This is the full exceptional scheme, not the entire
special fibre over Spec R; the strict transform is a separate component. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
open WeierstrassCurve.CriticalNeighborhood
open WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
  (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (n : ℕ) (hn : 0 <
    n)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ n))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
local notation "T" => originalRun M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "E" => Resolution.resolve π hπ hex hp hatlas n
local notation "origin" => NextCenter.origin π hπ n hn

/-- The same local full exceptional scheme mapped into the same original Run. -/
def originalExceptionalMap : pullback (E).map origin ⟶ (T).source := (Run.exceptionalToGlobal (R
  := R) (X := scheme W) (q₀ := residueNodeMap W x y he)
    (π := π) (hπ := hπ) (hex := hex) (hp := hp) (hatlas := hatlas) (hbc := hbc)
    (n := n) (hn := hn) (S := initialState M π hπ n hn a ha he ρ hρ) (T))

lemma originalExceptionalMap_square :
    IsPullback (originalExceptionalMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc)
      (pullback.snd (E).map origin)
      (modification M π hπ n hn a ha he ρ hρ hex hp hatlas hbc)
      (residueNodeMap W x y he) := by
  have H := Run.exceptionalToGlobal_square (R := R) (X := scheme W) (q₀ := residueNodeMap W x y he)
    (π := π) (hπ := hπ) (hex := hex) (hp := hp) (hatlas := hatlas) (hbc := hbc)
    (n := n) (hn := hn) (S := initialState M π hπ n hn a ha he ρ hρ) (T)
  simpa only [originalExceptionalMap, modification, Run.toOriginal,
    initialState, initialChart, Category.comp_id] using H

/-- A full exceptional-fibre isomorphism on the actual arbitrary original Run,
with the original residue-base projection retained exactly. -/
def originalExceptionalComparisonIso : pullback (E).map origin ≅
    pullback (modification M π hπ n hn a ha he ρ hρ hex hp hatlas hbc)
      (residueNodeMap W x y he) :=
  (originalExceptionalMap_square M π hπ n hn a ha he ρ hρ hex hp hatlas hbc).isoPullback

@[reassoc (attr := simp)] lemma originalExceptionalComparisonIso_hom_fst :
    (originalExceptionalComparisonIso M π hπ n hn a ha he ρ hρ hex hp hatlas hbc).hom ≫
      pullback.fst (modification M π hπ n hn a ha he ρ hρ hex hp hatlas hbc)
        (residueNodeMap W x y he) =
      originalExceptionalMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc :=
  (originalExceptionalMap_square M π hπ n hn a ha he ρ hρ hex hp hatlas hbc).isoPullback_hom_fst

@[reassoc (attr := simp)] lemma originalExceptionalComparisonIso_hom_snd :
    (originalExceptionalComparisonIso M π hπ n hn a ha he ρ hρ hex hp hatlas hbc).hom ≫
      pullback.snd (modification M π hπ n hn a ha he ρ hρ hex hp hatlas hbc)
        (residueNodeMap W x y he) = pullback.snd (E).map origin :=
  (originalExceptionalMap_square M π hπ n hn a ha he ρ hρ hex hp hatlas hbc).isoPullback_hom_snd

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassIteratedExceptionalComparison
