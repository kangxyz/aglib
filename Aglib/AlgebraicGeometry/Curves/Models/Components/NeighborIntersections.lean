/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Models.Components.Complement
public import Aglib.AlgebraicGeometry.IdealSheaf.Closed.ReducedComparison
public import Aglib.AlgebraicGeometry.Gluing.TwoPoint

/-!
# Actual neighbor intersections of complementary component unions

The actual irreducible-component index determines the neighbor-isolating open. The complement is
compared to its neighbor only after that open pullback. Two exact pairwise pullback squares, open
containment, disjointness and exhaustive support construct the actual split two-point intersection
over the original residue field.

R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
`Curves/LocalModels/CyclicModelComparison/NativeExceptionalIntersections.lean`: source ranges
[[36, 261]];
SHA-256 `1ded720bf0270889aeb32307b3555a839946a1d77571920d7720a5f17f737233`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily
variable {R : Type u} [CommRing R] [IsLocalRing R]
  {Y : Scheme.{u}} (π : Y ⟶ Spec (.of R))
  {C : irreducibleComponents (obj π) → Scheme.{u}}
  (inclusion : ∀ v, C v ⟶ obj π)
  [∀ v, IsClosedImmersion (inclusion v)] [∀ v, IsIntegral (C v)]
  [Finite (irreducibleComponents (obj π))]
  (hrange : ∀ v, Set.range (inclusion v) = v.val)

/-- Remove every other actual component except the selected neighbor. -/
def neighborOpen (v w : irreducibleComponents (obj π)) : (obj π).Opens :=
  ⟨(⋃ u : {u : irreducibleComponents (obj π) // u ≠ v ∧ u ≠ w}, u.val.val)ᶜ,
    (isClosed_iUnion_of_finite (fun u =>
      isClosed_of_mem_irreducibleComponents _ u.val.property)).isOpen_compl⟩

include hrange in
lemma neighborOpen_other_range (v w : irreducibleComponents (obj π)) (hw : w ≠ v) :
    (neighborOpen π v w).ι ⁻¹' Set.range (otherMap π inclusion v) =
      (neighborOpen π v w).ι ⁻¹' Set.range (inclusion w) := by
  ext z
  change (neighborOpen π v w).ι z ∈ Set.range (otherMap π inclusion v) ↔
    (neighborOpen π v w).ι z ∈ Set.range (inclusion w)
  rw [otherMap_range π inclusion hrange, hrange]
  constructor
  · intro hz
    obtain ⟨u,hu⟩ := Set.mem_iUnion.mp hz
    by_cases huw : u.val = w
    · simpa only [huw] using hu
    · have hzU : (neighborOpen π v w).ι z ∈ neighborOpen π v w := z.property
      exact False.elim (hzU (Set.mem_iUnion.mpr ⟨⟨u.val,u.property,huw⟩,hu⟩))
  · intro hz
    exact Set.mem_iUnion.mpr ⟨⟨w,hw⟩,hz⟩

/-- Genuine scheme comparison of the native union with the actual neighbor,
with no assertion that arbitrary ideal intersections commute with pullback. -/
def neighborOpenOtherIso (v w : irreducibleComponents (obj π)) (hw : w ≠ v) :
    pullback (otherMap π inclusion v) (neighborOpen π v w).ι ≅
      pullback (inclusion w) (neighborOpen π v w).ι :=
  Scheme.ReducedClosedSubscheme.onOpen (otherMap π inclusion v) (inclusion w)
    (neighborOpen π v w) (neighborOpen_other_range π inclusion hrange v w hw)

@[reassoc (attr := simp)] lemma neighborOpenOtherIso_hom_snd
    (v w : irreducibleComponents (obj π)) (hw : w ≠ v) :
    (neighborOpenOtherIso π inclusion hrange v w hw).hom ≫
      pullback.snd (inclusion w) (neighborOpen π v w).ι =
      pullback.snd (otherMap π inclusion v) (neighborOpen π v w).ι :=
  Scheme.ReducedClosedSubscheme.on_open_hom_snd _ _ _ _


section NeighborPoint
variable (v w : irreducibleComponents (obj π)) (hw : w ≠ v)
local notation "U" => neighborOpen π v w
local notation "o" => otherMap π inclusion v
local notation "i" => inclusion v
local notation "j" => inclusion w
local notation "I" => componentOtherIntersection π inclusion v

/-- The selected actual neighbor factors through the reduced complementary union. -/
def neighborToOther : C w ⟶ otherScheme π inclusion v :=
  liftReducedToClosed o j (by
    rw [otherMap_range π inclusion hrange, hrange]
    exact Set.subset_iUnion (fun u : {u : irreducibleComponents (obj π) // u ≠ v} => u.val.val)
      ⟨w,hw⟩)

@[reassoc (attr := simp)] lemma neighborToOther_fac :
    neighborToOther π inclusion hrange v w hw ≫ o = j := liftReducedToClosed_fac ..

variable {Z : Scheme.{u}} (s : Z ⟶ C w) (t : Z ⟶ C v)
  (H : IsPullback s t (inclusion w) (inclusion v))
  (hU : Set.range (t ≫ inclusion v) ⊆ neighborOpen π v w)

/-- The actual pairwise pullback chart mapped into the component-complement intersection. -/
def neighborIntersectionPoint : Z ⟶ I :=
  pullback.lift (s ≫ neighborToOther π inclusion hrange v w hw) t
    (by simp only [Category.assoc, neighborToOther_fac]; exact H.w)

@[reassoc (attr := simp)] lemma neighborIntersectionPoint_fst :
    neighborIntersectionPoint π inclusion hrange v w hw s t H ≫ pullback.fst o i =
      s ≫ neighborToOther π inclusion hrange v w hw := pullback.lift_fst ..
@[reassoc (attr := simp)] lemma neighborIntersectionPoint_snd :
    neighborIntersectionPoint π inclusion hrange v w hw s t H ≫ pullback.snd o i = t :=
      pullback.lift_snd ..

/-- The same pairwise intersection mapped into the actual neighbor-isolating open. -/
def neighborIntersectionToOpen : Z ⟶ (U).toScheme :=
  IsOpenImmersion.lift (U).ι (t ≫ i) (by simpa only [Scheme.Opens.range_ι] using hU)

omit [∀ v, IsClosedImmersion (inclusion v)] [∀ v, IsIntegral (C v)] in
@[reassoc (attr := simp)] lemma neighborIntersectionToOpen_fac :
    neighborIntersectionToOpen π inclusion v w t hU ≫ (U).ι = t ≫ i := IsOpenImmersion.lift_fac ..

/-- The native intersection chart is literally the pullback of the actual
ambient open. Its scheme structure comes from the exact pairwise square. -/
lemma neighborIntersectionPoint_square :
    IsPullback (neighborIntersectionToOpen π inclusion v w t hU)
      (neighborIntersectionPoint π inclusion hrange v w hw s t H) (U).ι (pullback.snd o i ≫ i) := by
  let p := neighborIntersectionPoint π inclusion hrange v w hw s t H
  let a := neighborIntersectionToOpen π inclusion v w t hU
  have hab : a ≫ (U).ι = p ≫ (pullback.snd o i ≫ i) := by
    simp only
      [a,p,neighborIntersectionToOpen_fac,neighborIntersectionPoint_snd_assoc]
  let liftOther := fun (c : PullbackCone (U).ι (pullback.snd o i ≫ i)) =>
    pullback.lift (c.snd ≫ pullback.fst o i) c.fst (by
      rw [Category.assoc,pullback.condition]
      exact c.condition.symm)
  let toNeighbor := fun (c : PullbackCone (U).ι (pullback.snd o i ≫ i)) =>
    liftOther c ≫ (neighborOpenOtherIso π inclusion hrange v w hw).hom ≫ pullback.fst j (U).ι
  have triangle : ∀ c, toNeighbor c ≫ j = c.snd ≫ pullback.snd o i ≫ i := by
    intro c
    simp only [toNeighbor,Category.assoc,pullback.condition,neighborOpenOtherIso_hom_snd_assoc,
      liftOther,pullback.lift_snd_assoc]
    exact c.condition
  apply IsPullback.of_isLimit (c := PullbackCone.mk a p hab)
  refine PullbackCone.IsLimit.mk _
    (fun c => H.lift (toNeighbor c) (c.snd ≫ pullback.snd o i) (triangle c)) ?_ ?_ ?_
  · intro c
    apply (cancel_mono (U).ι).mp
    simp only [Category.assoc,a,neighborIntersectionToOpen_fac,H.lift_snd_assoc]
    exact c.condition.symm
  · intro c
    apply pullback.hom_ext
    · apply (cancel_mono o).mp
      simp only [Category.assoc,p,pullback.condition,
        neighborIntersectionPoint_snd_assoc,H.lift_snd_assoc]
    · simp only [Category.assoc,p,neighborIntersectionPoint_snd,H.lift_snd]
  · intro c m hm₁ hm₂
    let : Mono t := H.mono_snd_of_mono
    apply (cancel_mono t).mp
    rw [H.lift_snd]
    have hh := congrArg (fun f => f ≫ pullback.snd o i) hm₂
    simpa only [Category.assoc,p,neighborIntersectionPoint_snd] using hh

include hU in
lemma neighborIntersectionPoint_open :
    IsOpenImmersion (neighborIntersectionPoint π inclusion hrange v w hw s t H) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (neighborIntersectionPoint_square π inclusion hrange v w hw s t H hU) inferInstance


end NeighborPoint

section TwoPoints
variable (v w₀ w₁ : irreducibleComponents (obj π))
  (hw₀ : w₀ ≠ v) (hw₁ : w₁ ≠ v)
local notation "k" => IsLocalRing.ResidueField R
local notation "o" => otherMap π inclusion v
local notation "i" => inclusion v
variable (s₀ : Spec (.of (IsLocalRing.ResidueField R)) ⟶ C w₀) (t₀ : Spec (.of
  (IsLocalRing.ResidueField R)) ⟶ C v)
  (s₁ : Spec (.of (IsLocalRing.ResidueField R)) ⟶ C w₁) (t₁ : Spec (.of (IsLocalRing.ResidueField
    R)) ⟶ C v)
  (H₀ : IsPullback s₀ t₀ (inclusion w₀) (inclusion v))
  (H₁ : IsPullback s₁ t₁ (inclusion w₁) (inclusion v))
  (hU₀ : Set.range (t₀ ≫ inclusion v) ⊆ neighborOpen π v w₀)
  (hU₁ : Set.range (t₁ ≫ inclusion v) ⊆ neighborOpen π v w₁)
  (hd : Disjoint (Set.range t₀) (Set.range t₁))
  (hc : Set.range (pullback.snd (otherMap π inclusion v) (inclusion v)) ⊆ Set.range t₀ ∪
    Set.range t₁)
  (hb₀ : t₀ ≫ structureMap π inclusion v = 𝟙 _)
  (hb₁ : t₁ ≫ structureMap π inclusion v = 𝟙 _)

/-- No intersection degree is supplied: two actual cartesian point charts,
their open containment, disjointness and exhaustive support yield the native iso. -/
def nativeOtherTwoPointIso_of_neighbor_squares : componentOtherTwoPointIso π inclusion v := by
  let a := neighborIntersectionPoint π inclusion hrange v w₀ hw₀ s₀ t₀ H₀
  let b := neighborIntersectionPoint π inclusion hrange v w₁ hw₁ s₁ t₁ H₁
  let : IsOpenImmersion a := neighborIntersectionPoint_open π inclusion hrange v w₀ hw₀ s₀ t₀ H₀ hU₀
  let : IsOpenImmersion b := neighborIntersectionPoint_open π inclusion hrange v w₁ hw₁ s₁ t₁ H₁ hU₁
  have hd' : Disjoint (Set.range a) (Set.range b) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x,rfl⟩ ⟨y,hy⟩
    have hh := congrArg (pullback.snd o i) hy
    change (b ≫ pullback.snd o i) y = (a ≫ pullback.snd o i) x at hh
    simp only [a,b,neighborIntersectionPoint_snd] at hh
    exact Set.disjoint_left.mp hd ⟨x,rfl⟩ ⟨y,hh⟩
  have hc' : Set.range a ∪ Set.range b = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    rcases hc ⟨z,rfl⟩ with ⟨x,hx⟩ | ⟨x,hx⟩
    · left
      refine ⟨x,(pullback.snd o i).injective ?_⟩
      change (a ≫ pullback.snd o i) x = _
      simpa only [a,neighborIntersectionPoint_snd] using hx
    · right
      refine ⟨x,(pullback.snd o i).injective ?_⟩
      change (b ≫ pullback.snd o i) x = _
      simpa only [b,neighborIntersectionPoint_snd] using hx
  have hset : IsCompl (Set.range a) (Set.range b) := ⟨hd',codisjoint_iff.mpr hc'⟩
  have hopens : IsCompl a.opensRange b.opensRange := by
    convert! hset
    simp only [isCompl_iff,disjoint_iff,codisjoint_iff,← TopologicalSpace.Opens.coe_inj]
    rfl
  have ha : a ≫ componentOtherIntersectionStructure π inclusion v = 𝟙 _ := by
    simpa only [a,componentOtherIntersectionStructure,neighborIntersectionPoint_snd_assoc] using hb₀
  have hb : b ≫ componentOtherIntersectionStructure π inclusion v = 𝟙 _ := by
    simpa only [b,componentOtherIntersectionStructure,neighborIntersectionPoint_snd_assoc] using hb₁
  exact Scheme.TwoPoint.DisjointOpenGluing.overIso k a b hopens
    (componentOtherIntersectionStructure π inclusion v) ha hb


end TwoPoints

end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber.ComponentFamily
