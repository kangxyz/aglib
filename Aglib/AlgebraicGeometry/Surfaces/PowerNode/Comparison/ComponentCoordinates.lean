/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.ExceptionalIntersections
public import Aglib.AlgebraicGeometry.Gluing.TwoPoint
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.ReducedComparison

/-!
# Actual component coordinates on the same resolved fibre

Source: frozen R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
`IntrinsicSplitNode/ResolvedCoordinates.lean`, lines 42–105, 114–125, 149–217, 247–377.
SHA-256: `424932cf8a97432d3030dacda7f9d34b15e99b6b09a00ef681e3d3969bb2681a`.
-/

@[expose] public section

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode
open AlgebraicGeometry.Scheme.TwoPoint AlgebraicGeometry.Scheme.RegularityDescent
open AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension

open _root_.AlgebraicGeometry.Scheme (SmoothClosedPointDimension SmoothFieldRegularity)

/-!
Actual resolved components and compatible original-residue-field coordinates for two or more
  components.

Supporting encoded subset of `K2-018#lem:k2018-cycle-cover`,
`research/exposes/K2/018/expose.tex`:619-663 at source revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Incoming E30 `PolygonCovers.lean` SHA-256:
`8aae72ab131433f5fbc833fc35f10827993175115e53ff0c986b24740f373f53`.
The exact displayed ordinary theorem families remain assumptions. This does not
close general model/comparison existence, E2 cover lifting, or the arbitrary-isogeny
converse. Embedded reconstruction-status comments describe the incoming source
stage; present validation coverage is recorded separately.
-/

section

/-! Actual same-fibre component adapter. The finite ordering is attached to the
literal resolved fibre and its existing strict/exceptional maps. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
open AlgebraicGeometry.Scheme.RegularityDescent
open AlgebraicGeometry.Scheme.ProjectiveLine (projectiveP1)
universe u

namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.ResolvedCyclicDiagram

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
  (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (m : ℕ)
  (a : M.Carrierˣ)
  (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (m + 2)))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R)
  (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x) (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
  (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (H : NormalProperCurveGenericExtension.{u})

local notation "k" => ResidueField R
local notation "F" => finalSpecialFibre M π hπ (m + 2) (Nat.succ_pos (m + 1))
  a ha he ρ hρ hex hp hatlas hbc
local notation "e" => resolvedComponentEquiv M π hπ (m + 1) a ha he ρ hρ
  hex hp hatlas hbc (Nat.succ_pos m)
local notation "p" => resolvedP1Map M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H

/-- Index0 is strict; index j + 1 is the original exceptional component j. -/
def componentEquiv : Fin (m + 2) ≃ irreducibleComponents F :=
  (finSuccEquiv (m + 1)).trans e

/-- The strict component at index zero and the exceptional components at successor indices, mapped
into the final special fibre. -/
def componentMap (j : Fin (m + 2)) : projectiveP1 k ⟶ F := p (finSuccEquiv (m + 1) j)

@[simp] lemma componentEquiv_zero :
    componentEquiv M π hπ m a ha he ρ hρ hex hp hatlas hbc 0 = e none := by
  simp [componentEquiv]

@[simp] lemma componentEquiv_succ (j : Fin (m + 1)) :
    componentEquiv M π hπ m a ha he ρ hρ hex hp hatlas hbc j.succ = e (some j) := by
  simp [componentEquiv]

@[simp] lemma componentMap_zero :
    componentMap M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H 0 =
      strictP1ToFinal M π hπ (m + 2) (Nat.succ_pos (m + 1))
        a ha he ρ hρ hex hp hatlas hbc hx hy H := by
  simp [componentMap, resolvedP1Map]

@[simp] lemma componentMap_succ (j : Fin (m + 1)) :
    componentMap M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H j.succ =
      originalExceptionalP1 M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc j := by
  simp [componentMap, resolvedP1Map]

@[reassoc] lemma componentMap_base (j : Fin (m + 2)) :
    componentMap M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H j ≫
      pullback.snd (modification M π hπ (m + 2) (Nat.succ_pos (m + 1))
        a ha he ρ hρ hex hp hatlas hbc ≫ structureMap W)
        (Resolution.residueBase (R := R)) = Scheme.ProjectiveLine.structureMap k :=
  resolvedP1Map_base M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H _

variable (hdvr : ProperBirationalDVRIsomorphismLocus.{u})

include hdvr in
lemma componentMap_closed (j : Fin (m + 2)) :
    IsClosedImmersion (componentMap M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H j) :=
  resolvedP1Map_closed M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H
    hdvr _

include hdvr in
lemma componentMap_range (j : Fin (m + 2)) :
    Set.range (componentMap M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H j) =
      (componentEquiv M π hπ m a ha he ρ hρ hex hp hatlas hbc j).val := by
  exact (resolvedP1Map_range M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H
    hdvr _).trans
    (resolvedComponentEquiv_range M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc
      (Nat.succ_pos m) _).symm

include hdvr in
lemma componentMap_ranges_cover :
    (⋃ j : Fin (m + 2), Set.range
      (componentMap M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H j)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  let v : irreducibleComponents F :=
    ⟨irreducibleComponent z, irreducibleComponent_mem_irreducibleComponents z⟩
  obtain ⟨j, hj⟩ :=
    (componentEquiv M π hπ m a ha he ρ hρ hex hp hatlas hbc).surjective v
  refine Set.mem_iUnion.mpr ⟨j, ?_⟩
  rw [componentMap_range M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H
    hdvr, hj]
  exact mem_irreducibleComponent

/-- The original P1 map, now indexed by the actual irreducible component. -/
def indexedComponent (v : irreducibleComponents F) :
    projectiveP1 k ⟶ F :=
  componentMap M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H
    ((componentEquiv M π hπ m a ha he ρ hρ hex hp hatlas hbc).symm v)

include hdvr in
lemma indexedComponent_range (v : irreducibleComponents F) :
    Set.range (indexedComponent M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H v) = v.val := by
  rw [indexedComponent, componentMap_range M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H
    hdvr, Equiv.apply_symm_apply]

include hdvr in
lemma indexedComponent_closed (v : irreducibleComponents F) :
    IsClosedImmersion
      (indexedComponent M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H v) :=
  componentMap_closed M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H hdvr _

@[reassoc] lemma indexedComponent_base (v : irreducibleComponents F) :
    indexedComponent M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H v ≫
      pullback.snd
        (modification M π hπ (m + 2) (Nat.succ_pos (m + 1))
          a ha he ρ hρ hex hp hatlas hbc ≫ structureMap W)
        (Resolution.residueBase (R := R)) = Scheme.ProjectiveLine.structureMap k :=
  componentMap_base M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H _

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.ResolvedCyclicDiagram

end -- original EOF scope

end

section

/-! Actual scheme-valued endpoint proof. Distinctness follows from the actual endpoint
pullback squares and endpoint incidence, including when n=3. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
open AlgebraicGeometry.Scheme.RegularityDescent
universe u

namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.ResolvedCyclicDiagram

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
  (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (m : ℕ)
  (a : M.Carrierˣ)
  (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (m + 3)))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R)
  (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x) (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
  (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (hext : NormalProperCurveGenericExtension.{u})
  (hdvr : ProperBirationalDVRIsomorphismLocus.{u})

local notation "k" => ResidueField R
local notation "F" => finalSpecialFibre M π hπ (m + 3) (Nat.succ_pos (m + 2))
  a ha he ρ hρ hex hp hatlas hbc
local notation "f" => strictP1ToFinal M π hπ (m + 3) (Nat.succ_pos (m + 2))
  a ha he ρ hρ hex hp hatlas hbc hx hy hext
local notation "P" => originalExceptionalP1 M π hπ (m + 2) a ha he ρ hρ hex hp hatlas hbc
local notation "left" => originalLeftStrictPoint M π hπ m a ha he ρ hρ
  hex hp hatlas hbc hx hy hext hdvr
local notation "right" => originalRightStrictPoint M π hπ m a ha he ρ hρ
  hex hp hatlas hbc hx hy hext hdvr
local notation "last" => (Fin.last (m + 1) : Fin (m + 2))

/-- The two strict sections have disjoint images on the same strict P1.
First and last exceptional components are not assumed disjoint. -/
lemma strict_endpoints_disjoint : Disjoint (Set.range left) (Set.range right) := by
  have hfirstlast : (0 : Fin (m + 2)) ≠ last := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at hval
    omega
  have hl (z : Spec (.of k)) : f (left z) =
      P 0 (Resolution.interiorStart (R := R) (m + 2) 0 z) := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun q : Spec (.of k) ⟶ F => q z)
        (originalLeftStrictPoint_isPullback M π hπ m a ha he ρ hρ
          hex hp hatlas hbc hx hy hext hdvr).w
  have hr (z : Spec (.of k)) : f (right z) =
      P last (Resolution.interiorFinish (R := R) (m + 2) last z) := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun q : Spec (.of k) ⟶ F => q z)
        (originalRightStrictPoint_isPullback M π hπ m a ha he ρ hρ
          hex hp hatlas hbc hx hy hext hdvr).w
  apply Set.disjoint_left.mpr
  rintro z ⟨s, hs⟩ ⟨t, ht⟩
  have hmem : (Resolution.interiorStart (R := R) (m + 2) 0 ≫ P 0) s ∈
      Set.range (P last) := by
    refine ⟨Resolution.interiorFinish (R := R) (m + 2) last t, ?_⟩
    simpa only [Scheme.Hom.comp_apply] using
      (hr t).symm.trans ((congrArg f (ht.trans hs.symm)).trans (hl s))
  have hbad := (originalExceptionalP1_start_mem_iff M π hπ (m + 2) a ha he ρ hρ
    hex hp hatlas hbc 0 last hfirstlast s).mp hmem
  simp only [Fin.val_zero, Fin.val_last] at hbad
  omega

/-- Distinct actual over-k section morphisms for the P1 coordinate adapter. -/
lemma strict_endpoints_ne : left ≠ right := by
  intro h
  let z : Spec (.of k) := Classical.choice inferInstance
  exact Set.disjoint_left.mp
    (strict_endpoints_disjoint M π hπ m a ha he ρ hρ
      hex hp hatlas hbc hx hy hext hdvr)
    ⟨z, rfl⟩ ⟨z, congrArg (fun q : Spec (.of k) ⟶
      Scheme.ProjectiveLine.projectiveP1 k => q z) h.symm⟩

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.ResolvedCyclicDiagram

end -- original EOF scope

end

section

/-! Actual same-fibre component adapter. At exponent two, both edges use the SAME
full scheme-theoretic pair intersection. No singleton-pair replacement occurs. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.FunctionField.GenericExtension
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
open AlgebraicGeometry.Scheme.RegularityDescent
universe u

namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.ResolvedCyclicDiagram


variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
  (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π)
  (a : M.Carrierˣ)
  (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ 2))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R)
  (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x) (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
  (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (H : NormalProperCurveGenericExtension.{u})
  (σ : ResidueField R)
  (hσ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x) (y := y) σ)
  (hne : ρ ≠ σ)

local notation "k" => ResidueField R
local notation "f" => strictP1ToFinal M π hπ 2 (Nat.succ_pos 1)
  a ha he ρ hρ hex hp hatlas hbc hx hy H
local notation "g" => originalExceptionalP1 M π hπ 1 a ha he ρ hρ hex hp hatlas hbc 0
local notation "J" => originalExceptionalToSpecial M π hπ 2 (Nat.succ_pos 1)
  a ha he ρ hρ hex hp hatlas hbc
local notation "b" => Scheme.ProjectiveLine.structureMap k
local notation "base" => pullback.snd (modification M π hπ 2 (Nat.succ_pos 1)
  a ha he ρ hρ hex hp hatlas hbc ≫ structureMap W) (Resolution.residueBase (R := R))

/-- The complete shared pair intersection, before choosing either of its points. -/
def twoComponentPairIso : pullback f g ≅ Spec (.of (k × k)) := by
  let : IsReduced (pullback f J) := strictExceptional_isReduced M π hπ 2 (by decide)
    a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
  exact Scheme.ReducedClosedIntersection.intersectionIso f g J
    (originalExceptionalP1_single_range M π hπ 1 a ha he ρ hρ
      hex hp hatlas hbc (by decide) rfl 0) ≪≫
    strictExceptionalTwoPointIso M π hπ 2 (by decide)
      a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne

local notation "e" => twoComponentPairIso M π hπ a ha he ρ hρ
  hex hp hatlas hbc hx hy H σ hσ hne

@[reassoc] lemma twoComponentPairIso_structure :
    (e).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k (k × k))) =
      pullback.fst f g ≫ b := by
  let : IsReduced (pullback f J) := strictExceptional_isReduced M π hπ 2 (by decide)
    a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
  simp only [twoComponentPairIso, Iso.trans_hom, Category.assoc,
    strictExceptionalTwoPointIso_structure,
    Scheme.ReducedClosedIntersection.intersectionIso_hom_fst_assoc]

/-- Both actual projections use the same inverse of the same shared-pair iso. -/
def twoComponentStrictBoundary : Spec (.of (k × k)) ⟶ Scheme.ProjectiveLine.projectiveP1 k :=
  (e).inv ≫ pullback.fst f g

/-- The exceptional-side projection of the shared two-point intersection, transported through the
pair isomorphism. -/
def twoComponentExceptionalBoundary : Spec (.of (k × k)) ⟶ Scheme.ProjectiveLine.projectiveP1 k :=
  (e).inv ≫ pullback.snd f g

local notation "s" => twoComponentStrictBoundary M π hπ a ha he ρ hρ
  hex hp hatlas hbc hx hy H σ hσ hne
local notation "t" => twoComponentExceptionalBoundary M π hπ a ha he ρ hρ
  hex hp hatlas hbc hx hy H σ hσ hne

@[reassoc] lemma twoComponentPairIso_strict : (e).hom ≫ s = pullback.fst f g := by
  simp only [twoComponentStrictBoundary, Iso.hom_inv_id_assoc]

@[reassoc] lemma twoComponentPairIso_exceptional : (e).hom ≫ t = pullback.snd f g := by
  simp only [twoComponentExceptionalBoundary, Iso.hom_inv_id_assoc]

@[reassoc] lemma twoComponentBoundary_square : s ≫ f = t ≫ g := by
  simp only [twoComponentStrictBoundary, twoComponentExceptionalBoundary, Category.assoc]
  rw [pullback.condition]

@[reassoc] lemma twoComponentStrictBoundary_over :
    s ≫ b = Spec.map (CommRingCat.ofHom (algebraMap k (k × k))) := by
  rw [← cancel_epi (e).hom]
  simpa only [twoComponentPairIso_strict_assoc] using
    (twoComponentPairIso_structure M π hπ a ha he ρ hρ
      hex hp hatlas hbc hx hy H σ hσ hne).symm

@[reassoc] lemma twoComponentExceptionalBoundary_over :
    t ≫ b = Spec.map (CommRingCat.ofHom (algebraMap k (k × k))) := by
  have hf : f ≫ base = b := strictP1ToFinal_over M π hπ 2 (by decide)
    a ha he ρ hρ hex hp hatlas hbc hx hy H
  have hg : g ≫ base = b := originalExceptionalP1_base M π hπ 1
    a ha he ρ hρ hex hp hatlas hbc 0
  calc
    t ≫ b = (t ≫ g) ≫ base := by rw [Category.assoc, hg]
    _ = (s ≫ f) ≫ base := by rw [twoComponentBoundary_square]
    _ = s ≫ b := by rw [Category.assoc, hf]
    _ = _ := twoComponentStrictBoundary_over M π hπ a ha he ρ hρ
      hex hp hatlas hbc hx hy H σ hσ hne

instance twoComponentStrictBoundary_closed : IsClosedImmersion s := by
  unfold twoComponentStrictBoundary
  infer_instance

/-- The ordered strict points are distinct by the actual closed projection. -/
lemma twoComponentStrictPoints_ne : productPoint0 k ≫ s ≠ productPoint1 k ≫ s := by
  intro h
  exact productPoints_ne k ((cancel_mono s).mp h)

@[reassoc] lemma twoComponentStrictPoint0_over : productPoint0 k ≫ s ≫ b = 𝟙 _ := by
  rw [twoComponentStrictBoundary_over, productPoint0_over]

@[reassoc] lemma twoComponentStrictPoint1_over : productPoint1 k ≫ s ≫ b = 𝟙 _ := by
  rw [twoComponentStrictBoundary_over, productPoint1_over]

@[reassoc] lemma twoComponentExceptionalPoint0_over : productPoint0 k ≫ t ≫ b = 𝟙 _ := by
  rw [twoComponentExceptionalBoundary_over, productPoint0_over]

@[reassoc] lemma twoComponentExceptionalPoint1_over : productPoint1 k ≫ t ≫ b = 𝟙 _ := by
  rw [twoComponentExceptionalBoundary_over, productPoint1_over]

variable (hdvr : ProperBirationalDVRIsomorphismLocus.{u})

include hdvr in
lemma twoComponentExceptionalBoundary_closed : IsClosedImmersion t := by
  let : IsClosedImmersion f := strictP1ToFinal_closedImmersion_positive M π hπ 0
    a ha he ρ hρ hex hp hatlas hbc hx hy H hdvr
  unfold twoComponentExceptionalBoundary
  infer_instance

include hdvr in
/-- The exceptional points use the same ordering of the full pair. To match
the two-cycle target, reverse one component's incoming/outgoing ordering. -/
lemma twoComponentExceptionalPoints_ne : productPoint0 k ≫ t ≠ productPoint1 k ≫ t := by
  let := twoComponentExceptionalBoundary_closed M π hπ a ha he ρ hρ
    hex hp hatlas hbc hx hy H σ hσ hne hdvr
  intro h
  exact productPoints_ne k ((cancel_mono t).mp h)

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.ResolvedCyclicDiagram

end -- original EOF scope

end
