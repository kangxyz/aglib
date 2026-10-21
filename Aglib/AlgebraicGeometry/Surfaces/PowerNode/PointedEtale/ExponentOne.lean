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
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.PointedEtale.WeierstrassSections
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.ResidueFiber
public import Aglib.AlgebraicGeometry.Properties.Regular.OpenCover

/-!
# The actual exponent-one modification

Source: frozen R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
`CyclicModelComparison/UnitThicknessComparison.lean`, lines 24–51.
SHA-256: `d367a974e638bacc92c481c4f160de071716082f6c3c2191fbab869ccdcce11a`.
`IntrinsicSplitNode/ValueOne.lean`, lines 59–97, 174–281.
SHA-256: `456fa148ece80652b570110e61ff7aa374ea52a4d46f3e703d0d2239f1120acf`.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open Scheme.Blowup Scheme.PowerNode WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
  (N : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π)
  (n : ℕ) (hn : 0 < n)
  (a : N.Carrierˣ) (ha : N.translated.a₆ = (a : N.Carrier) * algebraMap R N.Carrier (π ^ n))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})

/-- Equality of the actual dependent trace with its one-step terminal constructor.
The sole transport is the original thickness equation along n=1. -/
theorem originalRun_heq_one (h : n = 1) :
    HEq (originalRun N π hπ n hn a ha he ρ hρ hex hp hatlas hbc)
      (Run.one (hex := hex) (hp := hp) (hatlas := hatlas) (hbc := hbc)
        (initialState N π hπ 1 Nat.zero_lt_one a
          (by simpa only [h] using ha) he ρ hρ)) := by
  subst n
  simp only [originalRun, run, heq_eq_eq]

/-- The dependent source of that same trace is the original projective equation. -/
theorem originalRun_source_eq (h : n = 1) :
    (originalRun N π hπ n hn a ha he ρ hρ hex hp hatlas hbc).source =
      scheme W := by
  subst n
  unfold originalRun
  rw [run]
  rfl

/-- Literal identity after the proved source equality; no unrelated identity map is chosen. -/
theorem modification_eq_source_identity (h : n = 1) :
    modification N π hπ n hn a ha he ρ hρ hex hp hatlas hbc =
      eqToHom (originalRun_source_eq N π hπ n hn a ha he ρ hρ hex hp hatlas hbc h) := by
  subst n
  let S := initialState N π hπ 1 hn a ha he ρ hρ
  have aux (T : Run hex hp hatlas hbc S) (hT : T = Run.one S)
      (e : T.source = scheme W) : T.toOriginal = eqToHom e := by
    subst T
    change 𝟙 (scheme W) ≫ 𝟙 (scheme W) = eqToHom e
    simp
    rfl
  exact aux (originalRun N π hπ 1 hn a ha he ρ hρ hex hp hatlas hbc)
    (eq_of_heq (originalRun_heq_one N π hπ 1 hn a ha he ρ hρ hex hp hatlas hbc rfl))
    (originalRun_source_eq N π hπ 1 hn a ha he ρ hρ hex hp hatlas hbc rfl)

/-- This is the map of the constructed original run, rather than an independently
chosen resolution. At exponent one, `run` is literally `Run.one`. -/
theorem modification_isIso_of_exponent_one (h : n = 1) :
    IsIso (modification N π hπ n hn a ha he ρ hρ hex hp hatlas hbc) := by
  subst n
  unfold modification originalRun
  rw [run]
  change IsIso (𝟙 (scheme W) ≫ 𝟙 (scheme W))
  infer_instance

/-- Regularity transfers to the same literal equation through the actual
thickness-one modification; no minimality of the output is needed. -/
theorem original_regular_of_exponent_one (h : n = 1)
    (hregular : AlgebraicGeometry.Scheme.RegularStalks
      (originalRun N π hπ n hn a ha he ρ hρ hex hp hatlas hbc).source) :
    AlgebraicGeometry.Scheme.RegularStalks (scheme W) := by
  let := modification_isIso_of_exponent_one N π hπ n hn a ha he ρ hρ hex hp hatlas hbc h
  intro z
  obtain ⟨w, rfl⟩ :=
    (modification N π hπ n hn a ha he ρ hρ hex hp hatlas hbc).homeomorph.surjective z
  exact Scheme.RegularStalks.at_image
    (modification N π hπ n hn a ha he ρ hρ hex hp hatlas hbc) hregular w

/-- The same actual modification, regarded as an isomorphism over the DVR. -/
def exponentOneSurfaceOverIso (h : n = 1) :
    Over.mk (modification N π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫ structureMap W) ≅
      Over.mk (structureMap W) := by
  letI := modification_isIso_of_exponent_one N π hπ n hn a ha he ρ hρ hex hp hatlas hbc h
  exact Over.isoMk (asIso (modification N π hπ n hn a ha he ρ hρ hex hp hatlas hbc)) rfl

@[reassoc] theorem exponentOneSurfaceOverIso_infinity (h : n = 1) :
    infinityLift N π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫
      (exponentOneSurfaceOverIso N π hπ n hn a ha he ρ hρ hex hp hatlas hbc h).hom.left =
        infinitySection W := by
  change infinityLift N π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫
    modification N π hπ n hn a ha he ρ hρ hex hp hatlas hbc = infinitySection W
  exact infinityLift_triangle N π hπ n hn a ha he ρ hρ hex hp hatlas hbc

/-- Base change of that exact modification to the original residue pullback. -/
def exponentOneResiduePullbackIso (h : n = 1) :
    Over.mk (pullback.snd
      (modification N π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫ structureMap W)
      (Scheme.LocalRing.residueSpecMap R)) ≅
    Over.mk (pullback.snd (structureMap W) (Scheme.LocalRing.residueSpecMap R)) :=
  (Over.pullback (Scheme.LocalRing.residueSpecMap R)).mapIso
    (exponentOneSurfaceOverIso N π hπ n hn a ha he ρ hρ hex hp hatlas hbc h)

@[reassoc] theorem exponentOneResiduePullbackIso_fst (h : n = 1) :
    (exponentOneResiduePullbackIso N π hπ n hn a ha he ρ hρ hex hp hatlas hbc h).hom.left ≫
      pullback.fst (structureMap W) (Scheme.LocalRing.residueSpecMap R) =
    pullback.fst
      (modification N π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫ structureMap W)
      (Scheme.LocalRing.residueSpecMap R) ≫
        modification N π hπ n hn a ha he ρ hρ hex hp hatlas hbc := by
  let f := modification N π hπ n hn a ha he ρ hρ hex hp hatlas hbc
  let s := structureMap W
  let r := Scheme.LocalRing.residueSpecMap R
  change pullback.lift (pullback.fst (f ≫ s) r ≫ f) (pullback.snd (f ≫ s) r)
    (by rw [Category.assoc, pullback.condition]) ≫ pullback.fst s r = _
  exact pullback.lift_fst _ _ _

@[reassoc] theorem exponentOneResiduePullbackIso_snd (h : n = 1) :
    (exponentOneResiduePullbackIso N π hπ n hn a ha he ρ hρ hex hp hatlas hbc h).hom.left ≫
      pullback.snd (structureMap W) (Scheme.LocalRing.residueSpecMap R) =
    pullback.snd
      (modification N π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫ structureMap W)
      (Scheme.LocalRing.residueSpecMap R) :=
  (exponentOneResiduePullbackIso N π hπ n hn a ha he ρ hρ hex hp hatlas hbc h).hom.w

/-- The actual final residue fibre at exponent one is the same coefficient equation. -/
def exponentOneResidueEquationIso (h : n = 1) :
    Over.mk (pullback.snd
      (modification N π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫ structureMap W)
      (Scheme.LocalRing.residueSpecMap R)) ≅
    Over.mk (structureMap (W.baseChange (ResidueField R))) :=
  exponentOneResiduePullbackIso N π hπ n hn a ha he ρ hρ hex hp hatlas hbc h ≪≫
    (Over.isoMk (specialCoefficientIso W) (specialCoefficientIso_hom_snd W)).symm

/-- Exponent-one identity with the proved ordinary blowup suppliers. -/
theorem modification_isIso_of_exponent_one_concrete (h : n = 1) :
    IsIso (modification N π hπ n hn a ha he ρ hρ
      Scheme.Blowup.noetherianBlowupExistence Scheme.Blowup.noetherianBlowupProper
      Scheme.Blowup.blowupAffineAtlas Scheme.Blowup.blowupFlatBaseChange) :=
  modification_isIso_of_exponent_one N π hπ n hn a ha he ρ hρ
    Scheme.Blowup.noetherianBlowupExistence Scheme.Blowup.noetherianBlowupProper
    Scheme.Blowup.blowupAffineAtlas Scheme.Blowup.blowupFlatBaseChange h

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale
end
