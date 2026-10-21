/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.ComponentCoordinates
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.PointedEtale.ReducedFibre
public import Aglib.AlgebraicGeometry.Curves.Models.Components.NeighborIntersections
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.ReducedComparison

/-!
# Actual complementary component intersections

Source: frozen R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
`CyclicModelComparison/NativeStrictIntersections.lean`, lines 76–193.
SHA-256: `fac02b501b47bacc71f37f16530448525acab94fcb52ebfe8953089e2849de5f`.
`CyclicModelComparison/NativeExceptionalIntersections.lean`, lines 284–478, 495–555.
SHA-256: `1ded720bf0270889aeb32307b3555a839946a1d77571920d7720a5f17f737233`.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open Scheme.Blowup Scheme.PowerNode Scheme.ProjectiveLine Scheme.TwoPoint
open Scheme.RegularityDescent Scheme.FunctionField.GenericExtension
open Scheme.LocalRing.ResidueFiber WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.ResolvedCyclicDiagram
section StrictComplement
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
  (H : NormalProperCurveGenericExtension.{u})
  (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (hdvr : Scheme.ProperBirationalDVRIsomorphismLocus.{u})
local notation "k" => ResidueField R
local notation "πY" => modification M π hπ (m + 2) (Nat.succ_pos (m + 1))
  a ha he ρ hρ hex hp hatlas hbc ≫ structureMap W
local notation "F" => finalSpecialFibre M π hπ (m + 2) (Nat.succ_pos (m + 1))
  a ha he ρ hρ hex hp hatlas hbc
local notation "e" => resolvedComponentEquiv M π hπ (m + 1) a ha he ρ hρ
  hex hp hatlas hbc (Nat.succ_pos (m + 0))
local notation "i" => indexedComponent M π hπ m a ha he ρ hρ
  hex hp hatlas hbc hx hy H
local notation "ranges" => indexedComponent_range M π hπ m
  a ha he ρ hρ hex hp hatlas hbc hx hy H hdvr

local instance componentsFinite2 : Finite (irreducibleComponents F) :=
  Finite.of_equiv (Option (Fin (m + 1))) e

/-- The same Option-indexed map after the exact finite reindexing. -/
lemma indexedComponent_option (j : Option (Fin (m + 1))) :
    i (e j) = resolvedP1Map M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H j := by
  simp only [indexedComponent, componentMap, componentEquiv, Equiv.symm_trans_apply,
    Equiv.apply_symm_apply, Equiv.symm_apply_apply]

local notation "v" => e none
local notation "strict" => strictP1ToFinal M π hπ (m + 2) (Nat.succ_pos (m + 1))
  a ha he ρ hρ hex hp hatlas hbc hx hy H
local notation "exceptional" => originalExceptionalToSpecial M π hπ (m + 2)
  (Nat.succ_pos (m + 1)) a ha he ρ hρ hex hp hatlas hbc

include hdvr in
/-- Exact support of the actual reduced complement of the strict component. -/
lemma resolvedStrict_otherMap_range :
    Set.range (ComponentFamily.otherMap πY i v) = Set.range exceptional := by
  let : ∀ component, IsClosedImmersion (i component) := fun component =>
    indexedComponent_closed M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H
      hdvr component
  let : ∀ _ : irreducibleComponents F, IsIntegral (projectiveP1 k) := fun _ => inferInstance
  rw [ComponentFamily.otherMap_range πY i ranges]
  exact resolved_non_strict_components_support M π hπ (m + 1) a ha he ρ hρ
    hex hp hatlas hbc (Nat.succ_pos m)

variable (σ : ResidueField R)
  (hσ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x) (y := y) σ)
  (hne : ρ ≠ σ)

/-- The strict component meets its actual kernel-defined complement in two points. -/
def resolvedStrictComponentOtherTwoPointIso :
    ComponentFamily.componentOtherTwoPointIso πY i v := by
  let : ∀ component, IsClosedImmersion (i component) := fun component =>
    indexedComponent_closed M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H
      hdvr component
  let : ∀ _ : irreducibleComponents F, IsIntegral (projectiveP1 k) := fun _ => inferInstance
  let j := ComponentFamily.otherMap πY i v
  let iv := i v
  have hi : iv = strict := by
    dsimp only [iv]
    simp only [indexedComponent_option, resolvedP1Map]
  have hb : ComponentFamily.structureMap πY i v = Scheme.ProjectiveLine.structureMap k :=
    indexedComponent_base M π hπ m a ha he ρ hρ hex hp hatlas hbc hx hy H v
  let : IsReduced (pullback iv exceptional) := by
    rw [hi]
    exact strictExceptional_isReduced M π hπ (m + 2) (Nat.succ_pos (m + 1))
      a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
  have hs : Set.range j = Set.range exceptional :=
    resolvedStrict_otherMap_range M π hπ m a ha he ρ hρ hex hp hatlas hbc
      H hx hy hdvr
  have etwo : Over.mk (pullback.fst iv exceptional ≫ ComponentFamily.structureMap πY i v) ≅
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (k × k)))) := by
    rw [hi, hb]
    exact strictExceptionalTwoPointOverIso M π hπ (m + 2) (Nat.succ_pos (m + 1))
      a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
  change Over.mk (pullback.snd j iv ≫ ComponentFamily.structureMap πY i v) ≅ _
  let swap : Over.mk (pullback.snd j iv ≫ ComponentFamily.structureMap πY i v) ≅
      Over.mk (pullback.fst iv j ≫ ComponentFamily.structureMap πY i v) :=
    Over.isoMk (pullbackSymmetry j iv) (by simp)
  exact swap ≪≫ Scheme.ReducedClosedIntersection.intersectionOverIso
    iv j exceptional hs (ComponentFamily.structureMap πY i v) ≪≫ etwo

/-- At exponent two the sole exceptional component has the same full shared pair. -/
def resolvedSingleExceptionalComponentOtherTwoPointIso (hm : m = 0) (j₀ : Fin (m + 1)) :
    ComponentFamily.componentOtherTwoPointIso πY i (e (some j₀)) := by
  subst m
  let pi0 := modification M π hπ 2 (Nat.succ_pos 1) a ha he ρ hρ hex hp hatlas hbc ≫
    structureMap W
  let fibre0 := finalSpecialFibre M π hπ 2 (Nat.succ_pos 1) a ha he ρ hρ hex hp hatlas hbc
  let inc0 := indexedComponent M π hπ 0 a ha he ρ hρ hex hp hatlas hbc hx hy H
  let range0 := indexedComponent_range M π hπ 0 a ha he ρ hρ hex hp hatlas hbc
    hx hy H hdvr
  let : ∀ component, IsClosedImmersion (inc0 component) := fun component =>
    indexedComponent_closed M π hπ 0 a ha he ρ hρ hex hp hatlas hbc hx hy H
      hdvr component
  let : ∀ _ : irreducibleComponents fibre0, IsIntegral (projectiveP1 k) := fun _ => inferInstance
  let w := resolvedComponentEquiv M π hπ 1 a ha he ρ hρ
    hex hp hatlas hbc Nat.zero_lt_one (some j₀)
  let iv := indexedComponent M π hπ 0 a ha he ρ hρ hex hp hatlas hbc hx hy H w
  let other := ComponentFamily.otherMap pi0 inc0 w
  let fs := strictP1ToFinal M π hπ 2 (Nat.succ_pos 1) a ha he ρ hρ hex hp hatlas hbc hx hy H
  let es := originalExceptionalToSpecial M π hπ 2 (Nat.succ_pos 1) a ha he ρ hρ hex hp hatlas hbc
  let b := Scheme.ProjectiveLine.structureMap k
  have hi : iv = originalExceptionalP1 M π hπ 1 a ha he ρ hρ hex hp hatlas hbc j₀ := by
    dsimp only [iv, w]
    simp only [indexedComponent_option, resolvedP1Map]
  have hs : Set.range iv = Set.range es := by
    rw [hi]
    exact originalExceptionalP1_single_range M π hπ 1 a ha he ρ hρ
      hex hp hatlas hbc Nat.zero_lt_one rfl j₀
  have hf : Set.range fs = Set.range (strictTransformInclusion M π hπ 2 (Nat.succ_pos 1)
      a ha he ρ hρ hex hp hatlas hbc) :=
    resolvedP1Map_range M π hπ 0 a ha he ρ hρ hex hp hatlas hbc hx hy H
      hdvr none
  have ho : Set.range other = Set.range fs := by
    rw [ComponentFamily.otherMap_range pi0 inc0 range0]
    exact (resolved_except_single_exceptional_support M π hπ 1 a ha he ρ hρ
      hex hp hatlas hbc Nat.zero_lt_one rfl j₀).trans hf.symm
  let : IsReduced (pullback fs es) := strictExceptional_isReduced M π hπ 2 (Nat.succ_pos 1)
    a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
  let : IsClosedImmersion fs := strictP1ToFinal_closedImmersion_positive M π hπ 0
    a ha he ρ hρ hex hp hatlas hbc hx hy H hdvr
  let efi := Scheme.ReducedClosedIntersection.intersectionOverIso fs iv es hs b ≪≫
    strictExceptionalTwoPointOverIso M π hπ 2 (Nat.succ_pos 1)
      a ha he ρ hρ hex hp hatlas hbc hx hy H σ hσ hne
  let : IsReduced (pullback fs iv) := isReduced_of_isOpenImmersion
    (Scheme.ReducedClosedIntersection.intersectionIso fs iv es hs).hom
  let : IsReduced (pullback iv fs) :=
    isReduced_of_isOpenImmersion (pullbackSymmetry iv fs).hom
  have hib : iv ≫ pullback.snd
      (modification M π hπ 2 (Nat.succ_pos 1) a ha he ρ hρ hex hp hatlas hbc ≫ structureMap W)
      (Resolution.residueBase (R := R)) = b :=
    indexedComponent_base M π hπ 0 a ha he ρ hρ hex hp hatlas hbc hx hy H w
  have hfb : fs ≫ pullback.snd
      (modification M π hπ 2 (Nat.succ_pos 1) a ha he ρ hρ hex hp hatlas hbc ≫ structureMap W)
      (Resolution.residueBase (R := R)) = b :=
    strictP1ToFinal_over M π hπ 2 (Nat.succ_pos 1) a ha he ρ hρ hex hp hatlas hbc hx hy H
  have hswap : (pullbackSymmetry iv fs).hom ≫ (pullback.fst fs iv ≫ b) =
      pullback.fst iv fs ≫ b := by
    rw [pullbackSymmetry_hom_comp_fst_assoc, ← hfb, ← Category.assoc,
      ← pullback.condition, Category.assoc, hib, hfb]
  let swfi : Over.mk (pullback.fst iv fs ≫ b) ≅ Over.mk (pullback.fst fs iv ≫ b) :=
    Over.isoMk (pullbackSymmetry iv fs) hswap
  have enative : Over.mk (pullback.fst iv other ≫ b) ≅
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (k × k)))) :=
    Scheme.ReducedClosedIntersection.intersectionOverIso iv other fs ho b ≪≫ swfi ≪≫ efi
  change Over.mk (pullback.snd other iv ≫ ComponentFamily.structureMap pi0 inc0 w) ≅ _
  have hb : ComponentFamily.structureMap pi0 inc0 w = b := hib
  rw [hb]
  let swap : Over.mk (pullback.snd other iv ≫ b) ≅ Over.mk (pullback.fst iv other ≫ b) :=
    Over.isoMk (pullbackSymmetry other iv) (by simp)
  exact swap ≪≫ enative
end StrictComplement

section ExceptionalComplement
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
  (H : NormalProperCurveGenericExtension.{u})
  (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (hdvr : Scheme.ProperBirationalDVRIsomorphismLocus.{u})
local notation "k" => ResidueField R
local notation "πY" => modification M π hπ (m + 3) (Nat.succ_pos (m + 2))
  a ha he ρ hρ hex hp hatlas hbc ≫ structureMap W
local notation "F" => finalSpecialFibre M π hπ (m + 3) (Nat.succ_pos (m + 2))
  a ha he ρ hρ hex hp hatlas hbc
local notation "e" => resolvedComponentEquiv M π hπ (m + 2) a ha he ρ hρ
  hex hp hatlas hbc (Nat.succ_pos (m + 1))
local notation "i" => indexedComponent M π hπ (m + 1) a ha he ρ hρ
  hex hp hatlas hbc hx hy H
local notation "ranges" => indexedComponent_range M π hπ (m + 1)
  a ha he ρ hρ hex hp hatlas hbc hx hy H hdvr

local instance componentsFinite3 : Finite (irreducibleComponents F) :=
  Finite.of_equiv (Option (Fin (m + 2))) e

local notation "PM" => resolvedP1Map M π hπ (m + 1) a ha he ρ hρ
  hex hp hatlas hbc hx hy H
local notation "EP" => originalExceptionalP1 M π hπ (m + 2) a ha he ρ hρ hex hp hatlas hbc
variable (j : Fin (m + 2))
local notation "v" => e (some j)
local notation "v₀" => e (previousExceptional j)
local notation "v₁" => e (followingExceptional j)
local notation "p₀" => Resolution.interiorStart (R := R) (m + 2) j
local notation "p₁" => Resolution.interiorFinish (R := R) (m + 2) j
local notation "s₀" => resolvedPreviousPoint M π hπ m a ha he ρ hρ hex hp hatlas hbc
  hx hy H hdvr j
local notation "s₁" => resolvedFollowingPoint M π hπ m a ha he ρ hρ hex hp hatlas hbc
  hx hy H hdvr j
include hdvr in
/-- The actual start endpoint lies in the native open which removes every
third component. Both exceptional and strict exclusions are proved geometrically. -/
lemma resolvedExceptional_neighborOpen_start :
    Set.range (p₀ ≫ i v) ⊆
      (ComponentFamily.neighborOpen πY v v₀ : Set F) := by
  let : ∀ component, IsClosedImmersion (i component) := fun component =>
    indexedComponent_closed M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc hx hy H
      hdvr component
  let : ∀ _ : irreducibleComponents F, IsIntegral (projectiveP1 k) := fun _ => inferInstance
  rw [indexedComponent_option]
  change Set.range (p₀ ≫ EP j) ⊆ _
  rintro t ⟨z,rfl⟩
  change (p₀ ≫ EP j) z ∉
    ⋃ u : {u : irreducibleComponents F // u ≠ v ∧ u ≠ v₀}, u.val.val
  intro hbad
  obtain ⟨u,hu⟩ := Set.mem_iUnion.mp hbad
  obtain ⟨l,hl⟩ := (e).surjective u.val
  have hr : ((e) l).val = Set.range (PM l) :=
      (resolvedComponentEquiv_range M π hπ (m + 2) a ha he ρ hρ hex hp hatlas hbc
        (Nat.succ_pos (m + 1)) l).trans
      (resolvedP1Map_range M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc
        hx hy H hdvr l).symm
  have hu' : (p₀ ≫ EP j) z ∈ Set.range (PM l) := by
    rw [← hr,hl]
    exact hu
  have hlself : l ≠ some j := by
    intro h
    apply u.property.1
    rw [← hl,h]
  have hlneighbor : l = previousExceptional j := by
    cases l with
    | none =>
        have hj0 := (exceptionalStart_strict_mem_iff M π hπ m a ha he ρ hρ hex hp hatlas hbc
          hx hy H hdvr j z).mp hu'
        exact ((previousExceptional_eq_none j).mpr (by rw [hj0]; rfl)).symm
    | some l =>
      have hjl : j ≠ l := by
        intro h
        exact hlself (congrArg some h.symm)
      exact ((previousExceptional_eq_some j l).mpr
        ((originalExceptionalP1_start_mem_iff M π hπ (m + 2) a ha he ρ hρ
          hex hp hatlas hbc j l hjl z).mp hu')).symm
  exact u.property.2 (hl.symm.trans (congrArg (e) hlneighbor))

include hdvr in
/-- The actual finish endpoint lies in the native open which removes every
third component. Both exceptional and strict exclusions are proved geometrically. -/
lemma resolvedExceptional_neighborOpen_finish :
    Set.range (p₁ ≫ i v) ⊆
      (ComponentFamily.neighborOpen πY v v₁ : Set F) := by
  let : ∀ component, IsClosedImmersion (i component) := fun component =>
    indexedComponent_closed M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc hx hy H
      hdvr component
  let : ∀ _ : irreducibleComponents F, IsIntegral (projectiveP1 k) := fun _ => inferInstance
  rw [indexedComponent_option]
  change Set.range (p₁ ≫ EP j) ⊆ _
  rintro t ⟨z,rfl⟩
  change (p₁ ≫ EP j) z ∉
    ⋃ u : {u : irreducibleComponents F // u ≠ v ∧ u ≠ v₁}, u.val.val
  intro hbad
  obtain ⟨u,hu⟩ := Set.mem_iUnion.mp hbad
  obtain ⟨l,hl⟩ := (e).surjective u.val
  have hr : ((e) l).val = Set.range (PM l) :=
      (resolvedComponentEquiv_range M π hπ (m + 2) a ha he ρ hρ hex hp hatlas hbc
        (Nat.succ_pos (m + 1)) l).trans
      (resolvedP1Map_range M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc
        hx hy H hdvr l).symm
  have hu' : (p₁ ≫ EP j) z ∈ Set.range (PM l) := by
    rw [← hr,hl]
    exact hu
  have hlself : l ≠ some j := by
    intro h
    apply u.property.1
    rw [← hl,h]
  have hlneighbor : l = followingExceptional j := by
    cases l with
    | none =>
        have hjlast := (exceptionalFinish_strict_mem_iff M π hπ m a ha he ρ hρ hex hp hatlas hbc
          hx hy H hdvr j z).mp hu'
        exact ((followingExceptional_eq_none j).mpr (by rw [hjlast]; simp)).symm
    | some l =>
      have hjl : j ≠ l := by
        intro h
        exact hlself (congrArg some h.symm)
      exact ((followingExceptional_eq_some j l).mpr
        ((originalExceptionalP1_finish_mem_iff M π hπ (m + 2) a ha he ρ hρ
          hex hp hatlas hbc j l hjl z).mp hu')).symm
  exact u.property.2 (hl.symm.trans (congrArg (e) hlneighbor))

include hdvr in
/-- Every point of the actual native intersection projects to one of the two
retained endpoint sections. This is proved from the exhaustive actual inventory. -/
lemma resolvedExceptional_native_projection_support :
    Set.range (pullback.snd (ComponentFamily.otherMap πY i v) (i v)) ⊆
      Set.range p₀ ∪ Set.range p₁ := by
  let : ∀ component, IsClosedImmersion (i component) := fun component =>
    indexedComponent_closed M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc hx hy H
      hdvr component
  let : ∀ _ : irreducibleComponents F, IsIntegral (projectiveP1 k) := fun _ => inferInstance
  rintro z ⟨w,rfl⟩
  have hz : i v (pullback.snd (ComponentFamily.otherMap πY i v) (i v) w) ∈
      Set.range (ComponentFamily.otherMap πY i v) := by
    refine ⟨pullback.fst (ComponentFamily.otherMap πY i v) (i v) w,?_⟩
    exact congrArg (fun f => f w) (pullback.condition (f := ComponentFamily.otherMap πY i v) (g :=
      i v))
  rw [ComponentFamily.otherMap_range πY i ranges] at hz
  obtain ⟨u,hu⟩ := Set.mem_iUnion.mp hz
  obtain ⟨l,hl⟩ := (e).surjective u.val
  have hr : ((e) l).val = Set.range (PM l) :=
    (resolvedComponentEquiv_range M π hπ (m + 2) a ha he ρ hρ hex hp hatlas hbc
      (Nat.succ_pos (m + 1)) l).trans
    (resolvedP1Map_range M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc
      hx hy H hdvr l).symm
  have hi : i v = EP j :=
    indexedComponent_option M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc
      H hx hy (some j)
  have hu' : EP j (pullback.snd (ComponentFamily.otherMap πY i v) (i v) w) ∈ Set.range (PM l) := by
    rw [← hi,← hr,hl]
    exact hu
  have hlself : l ≠ some j := by
    intro h
    exact u.property (hl.symm.trans (congrArg (e) h))
  cases l with
  | none =>
    exact strictP1_exceptional_preimage_subset M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy H hdvr j hu'
  | some l =>
    have hjl : j ≠ l := by
      intro h
      exact hlself (congrArg some h.symm)
    exact originalExceptionalP1_other_preimage M π hπ (m + 2) a ha he ρ hρ
      hex hp hatlas hbc j l hjl hu'

/-- Every actual exceptional component for exponent m + 3 has its genuine native
complementary two-point scheme over the original residue field. No incidence,
component inventory, or count is supplied as a premise. -/
def resolvedExceptionalComponentOtherTwoPointIso : ComponentFamily.componentOtherTwoPointIso πY i
  v := by
  let : ∀ component, IsClosedImmersion (i component) := fun component =>
    indexedComponent_closed M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc hx hy H
      hdvr component
  let : ∀ _ : irreducibleComponents F, IsIntegral (projectiveP1 k) := fun _ => inferInstance
  have hw₀ : v₀ ≠ v := fun h => previousExceptional_ne_self j ((e).injective h)
  have hw₁ : v₁ ≠ v := fun h => followingExceptional_ne_self j ((e).injective h)
  have H₀ : IsPullback s₀ p₀ (i v₀) (i v) := by
    rw [indexedComponent_option, indexedComponent_option]
    exact resolvedPreviousPoint_isPullback M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy H hdvr j
  have H₁ : IsPullback s₁ p₁ (i v₁) (i v) := by
    rw [indexedComponent_option, indexedComponent_option]
    exact resolvedFollowingPoint_isPullback M π hπ m a ha he ρ hρ hex hp hatlas hbc
      hx hy H hdvr j
  have hb : ComponentFamily.structureMap πY i v = Scheme.ProjectiveLine.structureMap k :=
    indexedComponent_base M π hπ (m + 1) a ha he ρ hρ hex hp hatlas hbc hx hy H v
  have hb₀ : p₀ ≫ ComponentFamily.structureMap πY i v = 𝟙 _ := by
    rw [hb,Resolution.interiorStart_over]
  have hb₁ : p₁ ≫ ComponentFamily.structureMap πY i v = 𝟙 _ := by
    rw [hb,Resolution.interiorFinish_over]
  exact ComponentFamily.nativeOtherTwoPointIsoOfNeighborSquares πY i ranges v v₀ v₁ hw₀ hw₁ s₀
    p₀ s₁ p₁ H₀ H₁
    (resolvedExceptional_neighborOpen_start M π hπ m a ha he ρ hρ hex hp hatlas hbc
      H hx hy hdvr j)
    (resolvedExceptional_neighborOpen_finish M π hπ m a ha he ρ hρ hex hp hatlas hbc
      H hx hy hdvr j)
    (Resolution.interior_endpoints_disjoint (m + 2) j)
    (resolvedExceptional_native_projection_support M π hπ m a ha he ρ hρ hex hp hatlas hbc
      H hx hy hdvr j) hb₀ hb₁
end ExceptionalComplement

section AllComponents
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
  (H : NormalProperCurveGenericExtension.{u})
  (hx : (W.map (IsLocalRing.residue R)).toAffine.polynomialX.evalEval x y = 0)
  (hy : (W.map (IsLocalRing.residue R)).toAffine.polynomialY.evalEval x y = 0)
  (hdvr : Scheme.ProperBirationalDVRIsomorphismLocus.{u})
local notation "k" => ResidueField R
local notation "πY" => modification M π hπ (m + 2) (Nat.succ_pos (m + 1))
  a ha he ρ hρ hex hp hatlas hbc ≫ structureMap W
local notation "F" => finalSpecialFibre M π hπ (m + 2) (Nat.succ_pos (m + 1))
  a ha he ρ hρ hex hp hatlas hbc
local notation "e" => resolvedComponentEquiv M π hπ (m + 1) a ha he ρ hρ
  hex hp hatlas hbc (Nat.succ_pos (m + 0))
local notation "i" => indexedComponent M π hπ m a ha he ρ hρ
  hex hp hatlas hbc hx hy H
local notation "ranges" => indexedComponent_range M π hπ m
  a ha he ρ hρ hex hp hatlas hbc hx hy H hdvr

local instance allComponentsFinite : Finite (irreducibleComponents F) :=
  Finite.of_equiv (Option (Fin (m + 1))) e

variable (σ : ResidueField R)
  (hσ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x) (y := y) σ)
  (hne : ρ ≠ σ)

/-- Exhaustive actual complementary intersections, without a model or geometry record. -/
def componentOtherTwoPointIso (v : irreducibleComponents F) :
    ComponentFamily.componentOtherTwoPointIso πY i v := by
  let j := (e).symm v
  have hindex : (e) j = v := (e).apply_symm_apply v
  rw [← hindex]
  cases j with
  | none =>
    exact resolvedStrictComponentOtherTwoPointIso M π hπ m a ha he ρ hρ
      hex hp hatlas hbc H hx hy hdvr σ hσ hne
  | some j =>
    cases m with
    | zero =>
      exact resolvedSingleExceptionalComponentOtherTwoPointIso M π hπ 0 a ha he ρ hρ
        hex hp hatlas hbc H hx hy hdvr σ hσ hne rfl j
    | succ m =>
      exact resolvedExceptionalComponentOtherTwoPointIso M π hπ m a ha he ρ hρ
        hex hp hatlas hbc H hx hy hdvr j
end AllComponents
end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.ResolvedCyclicDiagram
end
