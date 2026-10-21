/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.ComponentInventory

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.ExceptionalComparison`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`bbcdcb52753990834123ae15628e4b96eb235ab2c3ee831891bec4c7f8a9d6d4`.
Actual arbitrary-scheme pointed-run/component maps with all original blowup-family inputs. The
  final source470–535 Weierstrass specialization is separately retained pending its original-run
  adapter.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode
open AlgebraicGeometry.Scheme.Hom.Range AlgebraicGeometry.Scheme.Pullback.Fibre

/-!
# Pointed-run attachments and iterated exceptional comparison

This module preserves the conditional interfaces and source-coverage boundaries
recorded in the individual sections below.
-/

section PointedRunExceptionalAttachments

/-! Transport literal component morphisms and their actual scheme-theoretic
branch attachments through the full arbitrary-Run comparison. Source component
and intersection schemes are unchanged, and both component-side attachment
maps stay exactly the original maps. No local endpoint singleton is declared
an extra component. -/
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
local notation "E" => Resolution.resolve π hπ hex hp hatlas n
local notation "origin" => NextCenter.origin π hπ n hn
variable {A : Scheme.{u}} (f : A ⟶ pullback (Resolution.resolve π hπ hex hp hatlas n).map
    (NextCenter.origin π hπ n hn))

/-- Transports a morphism into the literal node exceptional fibre to the exceptional fibre of the
given run. -/
def exceptionalComponent : A ⟶ pullback T.map S.chart.globalPoint :=
  CategoryStruct.comp (X := A) (Y := pullback (E).map origin)
    (Z := pullback T.map S.chart.globalPoint) f (exceptionalComparisonIso (R := R) (X := X) (q₀ :=
      q₀) (π := π) (hπ := hπ) (hex := hex) (hp := hp) (hatlas := hatlas) (hbc := hbc) (n := n) (hn
      := hn) (S := S) T).hom

/-- Maps the chosen literal exceptional-fibre morphism into the full common chart of the run. -/
def commonExceptionalMap : A ⟶ T.fullCommon :=
  CategoryStruct.comp (X := A) (Y := pullback (E).map origin) (Z := T.fullCommon) f
    (CategoryStruct.comp (X := pullback (E).map origin)
      (Y := pullback T.fullCommonMap S.chart.point) (Z := T.fullCommon)
      (commonNodeExceptionalIso (R := R) (X := X) (q₀ := q₀) (π := π) (hπ := hπ) (hex := hex) (hp
        := hp) (hatlas := hatlas) (hbc := hbc) (n := n) (hn := hn) (S := S) T).inv (pullback.fst
        T.fullCommonMap S.chart.point))

/-- Maps the chosen literal exceptional-fibre morphism into the global source of the run. -/
def globalExceptionalMap : A ⟶ T.source := commonExceptionalMap T f ≫ T.fullCommonToGlobal

@[reassoc (attr := simp)] lemma exceptionalComponent_base :
    exceptionalComponent T f ≫ pullback.snd T.map S.chart.globalPoint = f ≫ pullback.snd (E).map
      origin := by
  simp only [exceptionalComponent, Category.assoc, exceptionalComparisonIso_hom_snd]

@[reassoc (attr := simp)] lemma commonExceptionalMap_node :
    commonExceptionalMap T f ≫ (fullNodeComparison (π := π) (hπ := hπ) (hex := hex) (hp := hp)
      (hatlas := hatlas) (hbc := hbc) (n := n) (hn := hn) (S := S) T) = f ≫ pullback.fst (E).map
      origin := by
  simp only [commonExceptionalMap, Category.assoc]
  rw [← commonNodeExceptionalIso_hom_fst T, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)] lemma commonExceptionalMap_chart :
    commonExceptionalMap T f ≫ T.fullCommonMap = f ≫ pullback.snd (E).map origin ≫ S.chart.point
      := by
  simp only [commonExceptionalMap, Category.assoc]
  rw [pullback.condition, ← commonNodeExceptionalIso_hom_snd T, Category.assoc,
    Iso.inv_hom_id_assoc]

lemma globalExceptionalMap_eq :
    globalExceptionalMap T f = exceptionalComponent T f ≫ pullback.fst T.map S.chart.globalPoint
      := by
  simp only [globalExceptionalMap, exceptionalComponent, commonExceptionalMap,
    exceptionalComparisonIso,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, fullCommonExceptionalIso_hom_fst]

@[reassoc (attr := simp)] lemma globalExceptionalMap_target :
    globalExceptionalMap T f ≫ T.map = f ≫ pullback.snd (E).map origin ≫ S.chart.globalPoint := by
  simp only [globalExceptionalMap_eq, Category.assoc, pullback.condition,
    exceptionalComponent_base_assoc]

@[reassoc (attr := simp)] lemma globalExceptionalMap_original :
    globalExceptionalMap T f ≫ T.toOriginal = f ≫ pullback.snd (E).map origin ≫ q₀ := by
  simp only [toOriginal, ← Category.assoc, globalExceptionalMap_target]
  simp only [Category.assoc, S.point_triangle]

instance exceptionalComponent_closed [IsClosedImmersion f] : IsClosedImmersion
  (exceptionalComponent T f) := by
  dsimp [exceptionalComponent]
  infer_instance

instance globalExceptionalMap_closed [IsClosedImmersion f] : IsClosedImmersion
  (globalExceptionalMap T f) := by
  rw [globalExceptionalMap_eq]
  infer_instance

lemma commonExceptionalMap_global_square :
    IsPullback (commonExceptionalMap T f) (𝟙 A) T.fullCommonToGlobal (globalExceptionalMap T f) :=
      by
  let a := f ≫ pullback.snd (E).map origin
  have H : IsPullback (a ≫ S.chart.point) (𝟙 A) S.chart.toGlobal (a ≫ S.chart.globalPoint) := by
    simpa only [Category.comp_id] using
      (show IsPullback a (𝟙 A) (𝟙 _) a from IsPullback.of_id_snd).paste_horiz
        S.chart.global_square
  have K : IsPullback (commonExceptionalMap T f ≫ T.fullCommonMap) (𝟙 A)
      S.chart.toGlobal (globalExceptionalMap T f ≫ T.map) := by
    simpa only [commonExceptionalMap_chart, globalExceptionalMap_target, Category.assoc, a] using H
  exact K.of_right (by simp only [Category.id_comp, globalExceptionalMap]) T.fullCommon_square.flip

variable {L P : Scheme.{u}}
  (g : L ⟶ (Resolution.resolve π hπ hex hp hatlas n).Y)
  (s : P ⟶ L) (t : P ⟶ A)
  (H : IsPullback s t g (f ≫ pullback.fst
    (Resolution.resolve π hπ hex hp hatlas n).map
    (NextCenter.origin π hπ n hn)))

/-- The literal full common pullback of the chosen original local branch. -/
def liftedBranch : Scheme.{u} := pullback (fullNodeComparison (π := π) (hπ := hπ) (hex := hex) (hp
  := hp) (hatlas := hatlas) (hbc := hbc) (n := n) (hn := hn) (S := S) T) g

/-- The projection from the pulled-back local branch to the global source of the run. -/
def liftedBranchToGlobal : liftedBranch T g ⟶ T.source :=
  pullback.fst (fullNodeComparison (π := π) (hπ := hπ) (hex := hex) (hp := hp) (hatlas := hatlas)
    (hbc := hbc) (n := n) (hn := hn) (S := S) T) g ≫ T.fullCommonToGlobal

/-- The attachment morphism into the pulled-back branch induced by the given intersection square. -/
def liftedAttachment : P ⟶ liftedBranch T g :=
  pullback.lift (t ≫ commonExceptionalMap T f) s
    (by simpa only [Category.assoc, commonExceptionalMap_node] using H.w.symm)

@[reassoc (attr := simp)] lemma liftedAttachment_branch :
    liftedAttachment T f g s t H ≫ pullback.snd (fullNodeComparison (π := π) (hπ := hπ) (hex :=
      hex) (hp := hp) (hatlas := hatlas) (hbc := hbc) (n := n) (hn := hn) (S := S) T) g = s :=
      pullback.lift_snd ..

@[reassoc (attr := simp)] lemma liftedAttachment_common :
    liftedAttachment T f g s t H ≫ pullback.fst (fullNodeComparison (π := π) (hπ := hπ) (hex :=
      hex) (hp := hp) (hatlas := hatlas) (hbc := hbc) (n := n) (hn := hn) (S := S) T) g = t ≫
      commonExceptionalMap T f :=
  pullback.lift_fst ..

lemma liftedAttachment_common_square :
    IsPullback (liftedAttachment T f g s t H) t
      (pullback.fst (fullNodeComparison (π := π) (hπ := hπ) (hex := hex) (hp := hp) (hatlas :=
        hatlas) (hbc := hbc) (n := n) (hn := hn) (S := S) T) g) (commonExceptionalMap T f) := by
  have K : IsPullback (liftedAttachment T f g s t H ≫ pullback.snd (fullNodeComparison (π := π)
    (hπ := hπ) (hex := hex) (hp := hp) (hatlas := hatlas) (hbc := hbc) (n := n) (hn := hn) (S :=
    S) T) g) t g
      (commonExceptionalMap T f ≫ (fullNodeComparison (π := π) (hπ := hπ) (hex := hex) (hp := hp)
        (hatlas := hatlas) (hbc := hbc) (n := n) (hn := hn) (S := S) T)) := by
    simpa only [liftedAttachment_branch, commonExceptionalMap_node] using H
  exact K.of_right (liftedAttachment_common T f g s t H)
    (IsPullback.of_hasPullback (fullNodeComparison (π := π) (hπ := hπ) (hex := hex) (hp := hp)
      (hatlas := hatlas) (hbc := hbc) (n := n) (hn := hn) (S := S) T) g).flip

/-- Applies separately to the left and right original branch maps: their
intersection schemes and component-side endpoint maps are preserved exactly. -/
lemma liftedAttachment_global_square :
    IsPullback (liftedAttachment T f g s t H) t (liftedBranchToGlobal T g) (globalExceptionalMap T
      f) := by
  simpa only [Category.comp_id, liftedBranchToGlobal] using
    (liftedAttachment_common_square T f g s t H).paste_vert (commonExceptionalMap_global_square T f)

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run

end -- noncomputable section
end PointedRunExceptionalAttachments


section PointedRunExceptionalInventory

/-! The derived actual P1 inventory is transported through the accepted full
comparison for the very same arbitrary Run, with no component-count premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open PlaneNode _root_.PowerNode.Rees
open AlgebraicGeometry.Scheme.ProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {X : Scheme.{u}} {q₀ : Spec (.of (ResidueField R)) ⟶ X}
  {π : R} {hπ : Irreducible π}
  {hex : NoetherianBlowupExistence.{u}} {hp : NoetherianBlowupProper.{u}}
  {ha : BlowupAffineAtlas.{u}} {hbc : BlowupFlatBaseChange.{u}}
  {q : ℕ} {S : State X q₀ π hπ (q + 1) (Nat.succ_pos _)}
  (T : Run hex hp ha hbc S)
local notation "k" => ResidueField R
local notation "E" => Resolution.resolve π hπ hex hp ha (q + 1)
local notation "origin" => NextCenter.origin π hπ (q + 1) (Nat.succ_pos _)

/-- The indexed literal exceptional projective line transported to the exceptional fibre of the
run. -/
def actualExceptionalP1 (i : Fin q) : projectiveP1 k ⟶ pullback T.map S.chart.globalPoint :=
  exceptionalComponent T (Resolution.exceptionalP1 π hπ hex hp ha q i)

@[reassoc (attr := simp)] lemma actualExceptionalP1_base (i : Fin q) :
    actualExceptionalP1 T i ≫ pullback.snd T.map S.chart.globalPoint = structureMap k := by
  simp only [actualExceptionalP1, exceptionalComponent_base]
  exact Resolution.exceptionalP1_base π hπ hex hp ha q i

instance actualExceptionalP1_closed (i : Fin q) : IsClosedImmersion (actualExceptionalP1 T i) := by
  dsimp [actualExceptionalP1]
  infer_instance

lemma actualExceptionalP1_cover (hq : 0 < q) (z : ↥(pullback T.map S.chart.globalPoint)) :
    ∃ i : Fin q, z ∈ Set.range (actualExceptionalP1 T i) := by
  obtain ⟨x,rfl⟩ := (exceptionalComparisonIso T).hom.surjective z
  obtain ⟨i,p,hp⟩ := Resolution.exceptionalP1_cover π hπ hex hp ha q hq x
  exact ⟨i,p,congrArg (exceptionalComparisonIso T).hom hp⟩

/-- Actual maximal irreducible components of this Run's original-centre fibre. -/
def actualExceptionalComponentEquiv (hq : 0 < q) :
    Fin q ≃ irreducibleComponents ↥(pullback T.map S.chart.globalPoint) :=
  (Resolution.exceptionalComponentEquiv π hπ hex hp ha q hq).trans
    (exceptionalIrreducibleComponentsEquiv T)

lemma actualExceptionalComponentEquiv_range (hq : 0 < q) (i : Fin q) :
    (actualExceptionalComponentEquiv T hq i).val = Set.range (actualExceptionalP1 T i) := by
  change (exceptionalComparisonIso T).hom '' Set.range
    (Resolution.exceptionalP1 π hπ hex hp ha q i) = Set.range (actualExceptionalP1 T i)
  ext z
  constructor
  · rintro ⟨y,⟨p,rfl⟩,hz⟩
    exact ⟨p,hz⟩
  · rintro ⟨p,rfl⟩
    exact ⟨_,⟨p,rfl⟩,rfl⟩

lemma actualExceptional_irreducibleComponents_card (hq : 0 < q) :
    Nat.card (irreducibleComponents ↥(pullback T.map S.chart.globalPoint)) = q := by
  rw [← Nat.card_congr (actualExceptionalComponentEquiv T hq)]
  simp

/-- The global source map preserves the original contraction point exactly. -/
def actualExceptionalP1ToSource (i : Fin q) : projectiveP1 k ⟶ T.source :=
  globalExceptionalMap T (Resolution.exceptionalP1 π hπ hex hp ha q i)

@[reassoc (attr := simp)] lemma actualExceptionalP1ToSource_original (i : Fin q) :
    actualExceptionalP1ToSource T i ≫ T.toOriginal = structureMap k ≫ q₀ := by
  simp only [actualExceptionalP1ToSource, globalExceptionalMap_original]
  exact Resolution.exceptionalP1_base_assoc π hπ hex hp ha q i q₀

instance actualExceptionalP1ToSource_closed (i : Fin q) :
    IsClosedImmersion (actualExceptionalP1ToSource T i) := by
  dsimp [actualExceptionalP1ToSource]
  infer_instance

/-- The two actual labelled endpoint maps are transported without changing
Spec(k), either P1, or the original residue-field structure map. -/
def actualLeftExceptionalPoint : Spec (.of k) ⟶ pullback T.map S.chart.globalPoint :=
  exceptionalComponent T (Resolution.leftExceptionalPoint π hπ hex hp ha q)
/-- The right endpoint of the literal exceptional fibre transported to the exceptional fibre of
the run. -/
def actualRightExceptionalPoint : Spec (.of k) ⟶ pullback T.map S.chart.globalPoint :=
  exceptionalComponent T (Resolution.rightExceptionalPoint π hπ hex hp ha q)

@[reassoc (attr := simp)] lemma actualLeftExceptionalPoint_base :
    actualLeftExceptionalPoint T ≫ pullback.snd T.map S.chart.globalPoint = 𝟙 _ := by
  simp only [actualLeftExceptionalPoint, exceptionalComponent_base]
  exact Resolution.leftExceptionalPoint_base π hπ hex hp ha q
@[reassoc (attr := simp)] lemma actualRightExceptionalPoint_base :
    actualRightExceptionalPoint T ≫ pullback.snd T.map S.chart.globalPoint = 𝟙 _ := by
  simp only [actualRightExceptionalPoint, exceptionalComponent_base]
  exact Resolution.rightExceptionalPoint_base π hπ hex hp ha q

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run

end -- noncomputable section
end PointedRunExceptionalInventory


section RunAfterFirstMap

/-! The actual finite Run of thickness at least two factors through its first
chosen global blowup, including the terminal thickness-two case. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {X : Scheme.{u}} {q₀ : Spec (.of (ResidueField R)) ⟶ X}
  {π : R} {hπ : Irreducible π}
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})

namespace Run
variable {hex hp hatlas hbc}

/-- Constructor-level factorization avoids transports through the recursive
construction of a canonical Run. The lower bound only excludes Run.one. -/
def afterFirstMap : {n : ℕ} → {hn : 0 < n} → {S : State X q₀ π hπ n hn} →
    (T : Run hex hp hatlas hbc S) → (h : 2 ≤ n) →
      (T.source ⟶ (S.chart.globalBlowup hex).Y)
  | _, _, _, .one _, h => False.elim (by omega)
  | _, _, _, .two _, _ => 𝟙 _
  | _, _, _, .next _ _ tail, _ => tail.map

@[reassoc] lemma afterFirstMap_triangle :
    {n : ℕ} → {hn : 0 < n} → {S : State X q₀ π hπ n hn} →
    (T : Run hex hp hatlas hbc S) → (h : 2 ≤ n) →
      afterFirstMap T h ≫ (S.chart.globalBlowup hex).map = T.map
  | _, _, _, .one _, h => False.elim (by omega)
  | _, _, _, .two _, _ => Category.id_comp _
  | _, _, _, .next _ _ _, _ => rfl

end Run

/-- Identity for `Run.two`, and the actual tail map for `Run.next`. -/
def runAfterFirstMap (m : ℕ) (S : State X q₀ π hπ (m + 2) (by omega)) :
    (run hex hp hatlas hbc (m + 2) (by omega) S).source ⟶ (S.blowup hex).Y :=
  (run hex hp hatlas hbc (m + 2) (by omega) S).afterFirstMap (by omega)

@[reassoc] lemma runAfterFirstMap_triangle
    (m : ℕ) (S : State X q₀ π hπ (m + 2) (by omega)) :
    runAfterFirstMap hex hp hatlas hbc m S ≫ (S.blowup hex).map =
      (run hex hp hatlas hbc (m + 2) (by omega) S).map :=
  Run.afterFirstMap_triangle _ _

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end RunAfterFirstMap


section RunFirstBlowupComparison

/-! The accepted full node comparison also retains the actual first-blowup
maps. This is an identity of the existing constructions, proved by Run cases. -/
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
  {ha : BlowupAffineAtlas.{u}} {hbc : BlowupFlatBaseChange.{u}}

/-- The original common first blowup retained by the entire actual Run. -/
def firstCommonToBlowup : {n : ℕ} → {hn : 0 < n} → {S : State X q₀ π hπ n hn} →
    (T : Run hex hp ha hbc S) → (h : 2 ≤ n) →
      (T.fullCommon ⟶ (S.chart.commonBlowup hex).Y)
  | _,_,_,.one _,h => False.elim (by omega)
  | _,_,_,.two S,_ => (twoFullCommonIso hex hp ha hbc S).inv
  | _,_,_,.next _ S tail,_ =>
      (Step.retainedFullCommonIso S hex hp ha hbc tail).inv ≫ Step.retainedToBlowup S hex hp ha
        hbc tail

@[reassoc] lemma firstCommonToBlowup_global : ∀ (m : ℕ)
    (S : State X q₀ π hπ (m + 2) (by omega)) (T : Run hex hp ha hbc S),
    firstCommonToBlowup T (by omega) ≫ Chart.Step.toGlobal S.chart (S.blowup hex) (S.commonBlowup
      hex) =
      T.fullCommonToGlobal ≫ T.afterFirstMap (by omega)
  | 0,S,T => by
    cases T with
    | two S =>
      simp only [firstCommonToBlowup, afterFirstMap, Category.comp_id]
      rw [← twoFullCommonIso_hom_global hex hp ha hbc S, Iso.inv_hom_id_assoc]
  | m + 1,S,T => by
    cases T with
    | next m S tail =>
      simp only [firstCommonToBlowup, afterFirstMap, Category.assoc]
      rw [← (Step.retained_square S hex hp ha hbc tail).w,
        ← Step.retainedFullCommonIso_hom_global S hex hp ha hbc tail]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The local first blowdown and the genuine global first blowup are compatible
through the SAME full exceptional comparison, including exponent two. -/
@[reassoc] lemma firstCommonToBlowup_node : ∀ (m : ℕ)
    (S : State X q₀ π hπ (m + 2) (by omega)) (T : Run hex hp ha hbc S),
    firstCommonToBlowup T (by omega) ≫
      Chart.Step.toNode S.chart (OneStepBlowup.ofFamilies π m hex hp ha) (S.commonBlowup hex) =
    fullNodeComparison T ≫ Resolution.stepToBlowup
      (OneStepBlowup.ofFamilies π m hex hp ha) hπ (Resolution.resolve π hπ hex hp ha m)
  | 0,S,T => by
    cases T with
    | two S =>
      change (twoFullCommonIso hex hp ha hbc S).inv ≫ _ =
        ((twoFullCommonIso hex hp ha hbc S).inv ≫ _ ≫
          (Resolution.resolveTwoBlowupIso π hπ hex hp ha).inv) ≫
          (Resolution.resolveTwoBlowupIso π hπ hex hp ha).hom
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  | m + 1,S,T => by
    cases T with
    | next m S tail =>
      change (Step.retainedFullCommonIso S hex hp ha hbc tail).inv ≫
          Step.retainedToBlowup S hex hp ha hbc tail ≫ _ =
        ((Step.retainedFullCommonIso S hex hp ha hbc tail).inv ≫
          Step.Comparison.gluedComparison S hex hp ha hbc tail
            (Resolution.resolve π hπ hex hp ha (m + 1)) (fullNodeComparison tail)
            (fullNodeComparison_square tail)) ≫ _
      rw [Category.assoc, Step.Comparison.gluedComparison_triangle]

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale.Run

end -- noncomputable section
end RunFirstBlowupComparison


section NodeExceptionalMiddleWitnesses

/-! Each actual exceptional P1 has an explicit residue-field point in the
first middle chart. Exponent two uses the genuine Gm coordinate value one. -/
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

/-- The actual Gm point t=1, with its coordinate homomorphism exhibited. -/
def gmOnePoint (k : Type u) [Field k] : Spec (.of k) ⟶ Reciprocal.gm k :=
  Spec.map (CommRingCat.ofHom
    (IsLocalization.Away.liftAlgHom (Polynomial.X : k[X]) (f := aeval (1 : k)) (by simp)).toRingHom)

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (π : R) (hπ : Irreducible π)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (ha : BlowupAffineAtlas.{u})
local notation "k" => IsLocalRing.ResidueField R

/-- A literal k-point on each previously constructed source component. -/
def componentOriginPoint (q : ℕ) : ∀ a : ComponentIndex q,
    Spec (.of k) ⟶ componentScheme (R := R) q a
  | .inl _ => Cross.endpoint k
  | .inr _ => Reciprocal.zeroSection k

/-- Every exceptional P1 meets the full first middle through actual equal
morphisms out of Spec(k); this includes the terminal Gm point at exponent two. -/
lemma exceptionalP1_middle_witness : ∀ (m : ℕ) (i : Fin (m + 1)),
    ∃ (s : Spec (.of k) ⟶ projectiveP1 k)
      (t : Spec (.of k) ⟶ sourceSpecialFibre (resolve π hπ hex hp ha m)),
    s ≫ interiorComponent π hπ hex hp ha (m + 1) i =
      t ≫ middleFibreChart (OneStepBlowup.ofFamilies π m hex hp ha) hπ
        (resolve π hπ hex hp ha m)
  | 0,i => by
    refine ⟨gmOnePoint k ≫ Reciprocal.toZeroChart k ≫ chart k 0,
      gmOnePoint k ≫ twoMiddleGm (π := π),?_⟩
    simp only [interiorComponent, resolve, Category.assoc]
    rw [twoExceptional_left, two_middle_left_fibre]
  | m + 1,i => by
    let a := extensionIndex m i
    refine ⟨componentOriginPoint (R := R) m a ≫ extensionChart (R := R) m a,
      componentOriginPoint (R := R) m a ≫ componentMap π hπ hex hp ha m a,?_⟩
    rw [interiorComponent_eq_extended]
    simpa only [Category.assoc, a, recursiveMiddleChart] using
      congrArg (componentOriginPoint (R := R) m a ≫ ·)
        (extendedComponent_isPullback π hπ hex hp ha m a).w.symm

/-- The point on the P1's total-scheme image lies in the actual first middle
open of the same first local blowup. -/
lemma exceptionalP1_firstBlowup_meets_middle (m : ℕ) (i : Fin (m + 1)) :
    ∃ p : projectiveP1 k,
    (interiorComponent π hπ hex hp ha (m + 1) i ≫
      pullback.fst ((resolve π hπ hex hp ha (m + 2)).map ≫ base) residueBase ≫
      stepToBlowup (OneStepBlowup.ofFamilies π m hex hp ha) hπ
        (resolve π hπ hex hp ha m)) p ∈
      Set.range (BlowupAtlas.middleChartMap (OneStepBlowup.ofFamilies π m hex hp ha).atlas hπ) := by
  obtain ⟨s,t,H⟩ := exceptionalP1_middle_witness π hπ hex hp ha m i
  let z := IsLocalRing.closedPoint k
  refine ⟨s z,?_⟩
  have ht := congrArg (· ≫ pullback.fst ((resolve π hπ hex hp ha (m + 2)).map ≫ base) residueBase ≫
      stepToBlowup (OneStepBlowup.ofFamilies π m hex hp ha) hπ
        (resolve π hπ hex hp ha m)) H
  have Hchart : middleFibreChart (OneStepBlowup.ofFamilies π m hex hp ha) hπ
      (resolve π hπ hex hp ha m) ≫
      pullback.fst ((resolve π hπ hex hp ha (m + 2)).map ≫ base) residueBase ≫
      stepToBlowup (OneStepBlowup.ofFamilies π m hex hp ha) hπ
        (resolve π hπ hex hp ha m) =
      pullback.fst ((resolve π hπ hex hp ha m).map ≫ base) residueBase ≫
      (resolve π hπ hex hp ha m).map ≫
        BlowupAtlas.middleChartMap (OneStepBlowup.ofFamilies π m hex hp ha).atlas hπ := by
    calc
      _ = pullback.fst ((resolve π hπ hex hp ha m).map ≫ base) residueBase ≫
          stepModifiedChart (OneStepBlowup.ofFamilies π m hex hp ha) hπ
            (resolve π hπ hex hp ha m) ≫
          stepToBlowup (OneStepBlowup.ofFamilies π m hex hp ha) hπ
            (resolve π hπ hex hp ha m) := by
        exact middleFibreChart_source_triangle_assoc _ _ _ _
      _ = _ := by rw [← (stepModifiedChart_isPullback
        (OneStepBlowup.ofFamilies π m hex hp ha) hπ (resolve π hπ hex hp ha m)).w]
  simp only [Category.assoc] at ht
  rw [Hchart] at ht
  refine ⟨(t ≫ pullback.fst ((resolve π hπ hex hp ha m).map ≫ base) residueBase ≫
    (resolve π hπ hex hp ha m).map) z,?_⟩
  exact (congrArg (fun f => f z) ht).symm

end AlgebraicGeometry.Scheme.PowerNode.Resolution

end -- noncomputable section
end NodeExceptionalMiddleWitnesses
