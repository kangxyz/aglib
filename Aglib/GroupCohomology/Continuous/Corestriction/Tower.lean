/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupCohomology.Continuous.Corestriction.Basic

/-!
# Coset-section independence and subgroup-tower transitivity

Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source: `lean/R5Lab/Aglib/GroupCohomology/ContinuousCorestrictionTower.lean`.
SHA-256: `4efbe8f9c2b98cb390b8f9477e3ad04f3dcdf34cc6baa90240af30a980e5aebe`.
Actual coefficient carriers, topologies, actions, maps and primitive hypotheses are retained.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open GroupCohomology

namespace GroupCohomology.Continuous.Corestriction
open GroupCohomology.H2.Continuous (Cocycle complex d₀ d₁ d₀_apply d₁_apply
  d₁_d₀ d₁_eq_zero_iff d₁_cocycle cocycle₁OfClosed classOf classOf_d₁
  classOf_eq_zero_iff classOf_surjective)
namespace CosetSection
variable {G : Type*} [_root_.Group G] {H : Subgroup G}
variable (r : CosetSection G H)
variable [TopologicalSpace G] [IsTopologicalGroup G] (hH : IsOpen (H : Set G))
variable (A : Type*) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A] [H.FiniteIndex]
local instance : Fintype (G ⧸ H) := H.fintypeQuotientOfFiniteIndex

variable (s : CosetSection G H)

/-- The unique subgroup element relating two representatives of a coset. -/
def changeElement (x : G ⧸ H) : H :=
  ⟨(r.rep x)⁻¹ * s.rep x,
    QuotientGroup.eq.mp ((r.proj x).trans (s.proj x).symm)⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [H.FiniteIndex] in
theorem rep_change (x : G ⧸ H) :
    s.rep x = r.rep x * (changeElement r s x : G) := by
  change s.rep x = r.rep x * ((r.rep x)⁻¹ * s.rep x)
  group

omit [TopologicalSpace G] [IsTopologicalGroup G] [H.FiniteIndex] in
theorem change_factor (g : G) (x : G ⧸ H) :
    changeElement r s x * factor s g x =
      factor r g x * changeElement r s (shift G H g x) := by
  apply Subtype.ext
  change ((r.rep x)⁻¹ * s.rep x) *
    ((s.rep x)⁻¹ * g * s.rep (shift G H g x)) =
    ((r.rep x)⁻¹ * g * r.rep (shift G H g x)) *
      ((r.rep (shift G H g x))⁻¹ * s.rep (shift G H g x))
  group

omit [H.FiniteIndex] in
include hH in
theorem continuous_changeElement : Continuous (changeElement r s) := by
  let := QuotientGroup.discreteTopology hH
  exact continuous_of_discreteTopology

/-- The actual degree-zero correction for section independence in H1. -/
def correction₁ (b : ContinuousH1.Cocycle H A) : A :=
  ∑ x : G ⧸ H, r.rep x • b.val (changeElement r s x)

omit [IsTopologicalGroup G] [ContinuousSMul G A] [H.FiniteIndex] in
theorem change_oneCocycle (b : ContinuousH1.Cocycle H A) (g : G) (x : G ⧸ H) :
    changeElement r s x • b.val (factor s g x) =
      b.val (factor r g x) + factor r g x • b.val (changeElement r s (shift G H g x)) -
        b.val (changeElement r s x) := by
  have he := congrArg b.val (change_factor r s g x)
  rw [b.map_mul, b.map_mul] at he
  rw [← he]
  abel

/-- The degree-one transfers differ by the explicit principal cocycle. -/
theorem section_change₁ (b : ContinuousH1.Cocycle H A) :
    transferCocycles₁ s hH A b = transferCocycles₁ r hH A b +
      ContinuousH1.principal G A (correction₁ r A s b) := by
  apply ContinuousH1.Cocycle.ext
  intro g
  change (∑ x : G ⧸ H, s.rep x • b.val (factor s g x)) =
    (∑ x : G ⧸ H, r.rep x • b.val (factor r g x)) +
      (g • correction₁ r A s b - correction₁ r A s b)
  simp_rw [rep_change r s, mul_smul]
  change (∑ x : G ⧸ H, r.rep x • (changeElement r s x • b.val (factor s g x))) = _
  simp_rw [change_oneCocycle r A s b, smul_sub, smul_add]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_factor_smul r A g (fun x => b.val (changeElement r s x))]
  abel

/-- The local degree-one primitive for section independence in H2. -/
def localCorrection₂ (c : Cocycle H A) (g : G) (x : G ⧸ H) : A :=
  c.val (changeElement r s x, factor s g x) -
    c.val (factor r g x, changeElement r s (shift G H g x))

/-- The section-comparison primitive is genuinely continuous. -/
def correction₂ (c : Cocycle H A) : C(G, A) :=
  ⟨fun g => ∑ x : G ⧸ H, r.rep x • localCorrection₂ r A s c g x, by
    apply continuous_finsetSum
    intro x hx
    apply Continuous.smul continuous_const
    apply Continuous.sub
    · exact c.val.continuous.comp
        (continuous_const.prodMk ((continuous_factor s hH).comp
          (continuous_id.prodMk continuous_const)))
    · exact c.val.continuous.comp
        (((continuous_factor r hH).comp (continuous_id.prodMk continuous_const)).prodMk
          ((continuous_changeElement r hH s).comp
            ((continuous_shift G H).comp (continuous_id.prodMk continuous_const))))⟩

omit [IsTopologicalGroup G] [ContinuousSMul G A] [H.FiniteIndex] in
/-- The section comparison is the ordinary bar-cochain prism identity, proved
only from the three displayed instances of the actual two-cocycle identity. -/
theorem change_twoCocycle (c : Cocycle H A) (g h : G) (x : G ⧸ H) :
    changeElement r s x •
      c.val (factor s g x, factor s h (shift G H g x)) =
    c.val (factor r g x, factor r h (shift G H g x)) +
      factor r g x • localCorrection₂ r A s c h (shift G H g x) -
      localCorrection₂ r A s c (g * h) x + localCorrection₂ r A s c g x := by
  have h₁ := c.property (changeElement r s x) (factor s g x)
    (factor s h (shift G H g x))
  have h₂ := c.property (factor r g x) (changeElement r s (shift G H g x))
    (factor s h (shift G H g x))
  have h₃ := c.property (factor r g x) (factor r h (shift G H g x))
    (changeElement r s (shift G H h (shift G H g x)))
  rw [change_factor] at h₁
  rw [change_factor] at h₂
  simp only [localCorrection₂, factor_mul, shift_mul, smul_sub]
  have e₁ := eq_sub_of_add_eq h₁.symm
  have e₂ := eq_sub_of_add_eq (by simpa only [add_comm] using h₂)
  have e₃ := eq_sub_of_add_eq (by simpa only [add_comm] using h₃.symm)
  rw [e₁, e₂, e₃]
  abel

/-- Section changes alter the actual continuous degree-two transfer by a
boundary of the explicit continuous finite-sum primitive. -/
theorem section_change₂ (c : Cocycle H A) :
    transferCocycles₂ s hH A c = transferCocycles₂ r hH A c +
      d₁ G A (correction₂ r hH A s c) := by
  apply Cocycle.ext
  intro g h
  change (∑ x : G ⧸ H, s.rep x •
    c.val (factor s g x, factor s h (shift G H g x))) =
    (∑ x : G ⧸ H, r.rep x •
      c.val (factor r g x, factor r h (shift G H g x))) +
      (g • correction₂ r hH A s c h - correction₂ r hH A s c (g * h) +
        correction₂ r hH A s c g)
  simp_rw [rep_change r s, mul_smul]
  change (∑ x : G ⧸ H, r.rep x •
    (changeElement r s x • c.val (factor s g x, factor s h (shift G H g x)))) = _
  simp_rw [change_twoCocycle r A s c, smul_add, smul_sub]
  simp only [smul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_factor_smul r A g (fun x => localCorrection₂ r A s c h x)]
  abel

/-- Native H1 corestriction is independent of the chosen actual coset section. -/
theorem corestriction₁_independent :
    corestriction₁ s hH A = corestriction₁ r hH A := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨b, rfl⟩ := ContinuousH1.classOf_surjective H A z
  rw [corestriction₁_class, corestriction₁_class, section_change₁ r hH A s,
    map_add, ContinuousH1.classOf_principal, add_zero]

/-- Native H2 corestriction is independent of the chosen actual coset section. -/
theorem corestriction₂_independent :
    corestriction₂ s hH A = corestriction₂ r hH A := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨c, rfl⟩ := classOf_surjective H A z
  rw [corestriction₂_class, corestriction₂_class, section_change₂ r hH A s,
    map_add, classOf_d₁, add_zero]

/-- The generalized construction specializes to the frozen native H1 map. -/
@[simp] theorem chosen_corestriction₁ :
    corestriction₁ (chosen (G := G) (H := H)) hH A =
      Corestriction.corestriction₁ G H hH A := rfl

/-- The generalized construction specializes to the frozen native H2 map. -/
@[simp] theorem chosen_corestriction₂ :
    corestriction₂ (chosen (G := G) (H := H)) hH A =
      Corestriction.corestriction₂ G H hH A := rfl


end CosetSection
end GroupCohomology.Continuous.Corestriction


namespace GroupCohomology.Continuous.Corestriction.Tower
open GroupCohomology.H2.Continuous (Cocycle complex d₀ d₁ d₀_apply d₁_apply
  d₁_d₀ d₁_eq_zero_iff d₁_cocycle cocycle₁OfClosed classOf classOf_d₁
  classOf_eq_zero_iff classOf_surjective)

variable {G : Type*} [_root_.Group G]
variable (K H : Subgroup G) (hKH : K ≤ H)
variable (r : CosetSection G H) (s : CosetSection H (K.subgroupOf H))

/-- The actual bijection of cosets in a subgroup tower, using the outer section. -/
def cosetEquiv : G ⧸ K ≃ (G ⧸ H) × (H ⧸ K.subgroupOf H) :=
  Subgroup.quotientEquivProdOfLE' hKH r.rep r.proj

/-- The inverse coset bijection is multiplication of actual representatives. -/
theorem cosetEquiv_symm (x : G ⧸ H) (y : H ⧸ K.subgroupOf H) :
    (cosetEquiv K H hKH r).symm (x, y) = QuotientGroup.mk (r.rep x * (s.rep y : G)) := by
  conv_lhs => rw [← s.proj y]
  rfl

/-- The product representatives are an actual section for the smallest subgroup. -/
def productSection : CosetSection G K where
  rep z := r.rep ((cosetEquiv K H hKH r) z).1 *
    (s.rep ((cosetEquiv K H hKH r) z).2 : G)
  proj z := by
    rw [← cosetEquiv_symm K H hKH r s]
    exact (cosetEquiv K H hKH r).symm_apply_apply z

/-- The canonical inclusion from the nested subgroup to the original subgroup. -/
def nestedInclusion : K.subgroupOf H →* K where
  toFun k := ⟨(k.val : G), k.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

include s in
/-- Backward coset transport respects the actual tower decomposition. -/
theorem cosetEquiv_shift (g : G) (z : G ⧸ K) :
    cosetEquiv K H hKH r (shift G K g z) =
      (shift G H g ((cosetEquiv K H hKH r) z).1,
        shift H (K.subgroupOf H) (r.factor g ((cosetEquiv K H hKH r) z).1)
          ((cosetEquiv K H hKH r) z).2) := by
  apply (cosetEquiv K H hKH r).symm.injective
  rw [Equiv.symm_apply_apply, cosetEquiv_symm K H hKH r s]
  conv_lhs => rw [← (productSection K H hKH r s).proj z]
  change QuotientGroup.mk (g⁻¹ *
      (r.rep ((cosetEquiv K H hKH r) z).1 * (s.rep ((cosetEquiv K H hKH r) z).2 : G))) =
    QuotientGroup.mk (r.rep (shift G H g ((cosetEquiv K H hKH r) z).1) *
      (s.rep (shift H (K.subgroupOf H) (r.factor g ((cosetEquiv K H hKH r) z).1)
        ((cosetEquiv K H hKH r) z).2) : G))
  apply QuotientGroup.eq.mpr
  have hm : ((s.factor (r.factor g ((cosetEquiv K H hKH r) z).1)
      ((cosetEquiv K H hKH r) z).2 : H) : G) ∈ K :=
    (s.factor (r.factor g ((cosetEquiv K H hKH r) z).1)
      ((cosetEquiv K H hKH r) z).2).property
  convert hm using 2
  change ((g⁻¹ * (r.rep ((cosetEquiv K H hKH r) z).1 *
      (s.rep ((cosetEquiv K H hKH r) z).2 : G)))⁻¹ *
      (r.rep (shift G H g ((cosetEquiv K H hKH r) z).1) *
        (s.rep (shift H (K.subgroupOf H) (r.factor g ((cosetEquiv K H hKH r) z).1)
          ((cosetEquiv K H hKH r) z).2) : G))) =
    (s.rep ((cosetEquiv K H hKH r) z).2 : G)⁻¹ *
      ((r.rep ((cosetEquiv K H hKH r) z).1)⁻¹ * g *
        r.rep (shift G H g ((cosetEquiv K H hKH r) z).1)) *
      (s.rep (shift H (K.subgroupOf H) (r.factor g ((cosetEquiv K H hKH r) z).1)
        ((cosetEquiv K H hKH r) z).2) : G)
  group

/-- Product representatives factor through the actual inner transition function. -/
theorem productSection_factor (g : G) (z : G ⧸ K) :
    (productSection K H hKH r s).factor g z =
      nestedInclusion K H (s.factor (r.factor g ((cosetEquiv K H hKH r) z).1)
        ((cosetEquiv K H hKH r) z).2) := by
  apply Subtype.ext
  change (r.rep ((cosetEquiv K H hKH r) z).1 *
      (s.rep ((cosetEquiv K H hKH r) z).2 : G))⁻¹ * g *
      (r.rep ((cosetEquiv K H hKH r) (shift G K g z)).1 *
        (s.rep ((cosetEquiv K H hKH r) (shift G K g z)).2 : G)) = _
  rw [cosetEquiv_shift K H hKH r s]
  change (r.rep ((cosetEquiv K H hKH r) z).1 *
      (s.rep ((cosetEquiv K H hKH r) z).2 : G))⁻¹ * g *
      (r.rep (shift G H g ((cosetEquiv K H hKH r) z).1) *
        (s.rep (shift H (K.subgroupOf H) (r.factor g ((cosetEquiv K H hKH r) z).1)
          ((cosetEquiv K H hKH r) z).2) : G)) =
    (s.rep ((cosetEquiv K H hKH r) z).2 : G)⁻¹ *
      ((r.rep ((cosetEquiv K H hKH r) z).1)⁻¹ * g *
        r.rep (shift G H g ((cosetEquiv K H hKH r) z).1)) *
      (s.rep (shift H (K.subgroupOf H) (r.factor g ((cosetEquiv K H hKH r) z).1)
        ((cosetEquiv K H hKH r) z).2) : G)
  group


include hKH in
/-- This inclusion is a group identification when the given tower is nested. -/
theorem nestedInclusion_bijective : Function.Bijective (nestedInclusion K H) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun k : K => (k : G)) hab
  · intro k
    exact ⟨⟨⟨k.val, hKH k.property⟩, k.property⟩, rfl⟩

/-- The actual group equivalence identifying the nested and original subgroups. -/
def nestedEquiv : K.subgroupOf H ≃* K where
  toFun := nestedInclusion K H
  invFun k := ⟨⟨k.val, hKH k.property⟩, k.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The actual subgroup identification is continuous in the inherited topology. -/
def nestedHom : ContinuousMonoidHom (K.subgroupOf H) K where
  toMonoidHom := nestedInclusion K H
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) (fun k => k.property)

omit [IsTopologicalGroup G] in
/-- The group identification is continuous in the forward direction. -/
theorem nestedEquiv_continuous : Continuous (nestedEquiv K H hKH) :=
  (nestedHom K H).continuous

omit [IsTopologicalGroup G] in
/-- Its explicit inverse is also continuous, so this is the genuine
identification for native continuous cochains and cohomology. -/
theorem nestedEquiv_symm_continuous : Continuous (nestedEquiv K H hKH).symm := by
  exact Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val (fun k : K => hKH k.property))
    (fun k : K => k.property)

variable (A : Type*) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]

/-- Actual continuous cochains pulled back along the canonical subgroup identification. -/
def nestedCochain₁ : C(K, A) →+ C(K.subgroupOf H, A) where
  toFun b := ⟨fun k => b (nestedInclusion K H k), b.continuous.comp (nestedHom K H).continuous⟩
  map_zero' := by ext k; rfl
  map_add' _ _ := by ext k; rfl

/-- Actual degree-two cochains pulled back along the canonical subgroup identification. -/
def nestedCochain₂ : C(K × K, A) →+ C((K.subgroupOf H) × (K.subgroupOf H), A) where
  toFun c := ⟨fun p => c (nestedInclusion K H p.1, nestedInclusion K H p.2),
    c.continuous.comp (((nestedHom K H).continuous.comp continuous_fst).prodMk
      ((nestedHom K H).continuous.comp continuous_snd))⟩
  map_zero' := by ext p; rfl
  map_add' _ _ := by ext p; rfl

abbrev nestedCocycles₁ : ContinuousH1.Cocycle K A →+
    ContinuousH1.Cocycle (K.subgroupOf H) A :=
  ContinuousH1.restrictionCocycles A (nestedHom K H)

def nestedCocycles₂ : Cocycle K A →+ Cocycle (K.subgroupOf H) A where
  toFun c := ⟨nestedCochain₂ K H A c.val, fun h k l =>
    c.property (nestedInclusion K H h) (nestedInclusion K H k) (nestedInclusion K H l)⟩
  map_zero' := Subtype.ext (map_zero (nestedCochain₂ K H A))
  map_add' c d := Subtype.ext (map_add (nestedCochain₂ K H A) c.val d.val)

omit [IsTopologicalGroup G] in
theorem nested_principal (a : A) :
    nestedCocycles₁ K H A (ContinuousH1.principal K A a) =
      ContinuousH1.principal (K.subgroupOf H) A a := by
  apply ContinuousH1.Cocycle.ext
  intro k
  rfl

abbrev nestedH1 : ContinuousH1.H1 K A →+
    ContinuousH1.H1 (K.subgroupOf H) A :=
  ContinuousH1.restriction A (nestedHom K H)

omit [IsTopologicalGroup G] in
@[simp] theorem nestedH1_class (b : ContinuousH1.Cocycle K A) :
    nestedH1 K H A (ContinuousH1.classOf K A b) =
      ContinuousH1.classOf (K.subgroupOf H) A (nestedCocycles₁ K H A b) := rfl

theorem nested_d₁ (b : C(K, A)) :
    nestedCocycles₂ K H A (d₁ K A b) = d₁ (K.subgroupOf H) A (nestedCochain₁ K H A b) := rfl

def nestedCycles₂ : (complex K A).Cycles₂ →+ (complex (K.subgroupOf H) A).Cycles₂ where
  toFun c := ⟨nestedCocycles₂ K H A c.val, rfl⟩
  map_zero' := Subtype.ext (map_zero (nestedCocycles₂ K H A))
  map_add' c d := Subtype.ext (map_add (nestedCocycles₂ K H A) c.val d.val)

theorem nested_boundary₂ (b : C(K, A)) :
    nestedCycles₂ K H A ((complex K A).boundary₂ b) =
      (complex (K.subgroupOf H) A).boundary₂ (nestedCochain₁ K H A b) :=
  Subtype.ext (nested_d₁ K H A b)

/-- Native H2 transport along the actual continuous subgroup identification. -/
def nestedH2 : H2.Continuous.Group K A →+ H2.Continuous.Group (K.subgroupOf H) A :=
  QuotientAddGroup.map _ _ (nestedCycles₂ K H A) (by
    rintro c ⟨b, rfl⟩
    exact ⟨nestedCochain₁ K H A b, (nested_boundary₂ K H A b).symm⟩)

@[simp] theorem nestedH2_class (c : Cocycle K A) :
    nestedH2 K H A (classOf K A c) =
      classOf (K.subgroupOf H) A (nestedCocycles₂ K H A c) := rfl

variable (hK : IsOpen (K : Set G)) (hH : IsOpen (H : Set G))
variable [K.FiniteIndex] [H.FiniteIndex]
local instance : Fintype (G ⧸ K) := K.fintypeQuotientOfFiniteIndex
local instance : Fintype (G ⧸ H) := H.fintypeQuotientOfFiniteIndex
local instance : Fintype (H ⧸ K.subgroupOf H) := (K.subgroupOf H).fintypeQuotientOfFiniteIndex

omit [IsTopologicalGroup G] [K.FiniteIndex] [H.FiniteIndex] in
include hK in
/-- Openness of the inner subgroup is proved from the actual tower. -/
theorem innerOpen : IsOpen ((K.subgroupOf H : Subgroup H) : Set H) :=
  hK.preimage continuous_subtype_val

/-- For product representatives, degree-one transfer is literally the composite
of the two actual continuous cochain transfers. -/
theorem transfer₁_product (b : C(K, A)) :
    (productSection K H hKH r s).transfer₁ hK A b =
      r.transfer₁ hH A (s.transfer₁ (innerOpen K H hK) A (nestedCochain₁ K H A b)) := by
  ext g
  change (∑ z : G ⧸ K, (productSection K H hKH r s).rep z •
      b ((productSection K H hKH r s).factor g z)) =
    ∑ x : G ⧸ H, r.rep x • ∑ y : H ⧸ K.subgroupOf H,
      (s.rep y : G) • b (nestedInclusion K H (s.factor (r.factor g x) y))
  simp_rw [Finset.smul_sum, ← mul_smul]
  rw [← Fintype.sum_prod_type (fun p : (G ⧸ H) × (H ⧸ K.subgroupOf H) =>
    (r.rep p.1 * (s.rep p.2 : G)) • b (nestedInclusion K H (s.factor (r.factor g p.1) p.2)))]
  exact Fintype.sum_equiv (cosetEquiv K H hKH r) _ _ (fun z => by
    rw [productSection_factor K H hKH r s]
    rfl)

/-- The product-section equality holds on every actual continuous two-cochain,
so it does not need a cocycle, symbol or norm compatibility premise. -/
theorem transfer₂_product (c : C(K × K, A)) :
    (productSection K H hKH r s).transfer₂ hK A c =
      r.transfer₂ hH A (s.transfer₂ (innerOpen K H hK) A (nestedCochain₂ K H A c)) := by
  ext p
  rcases p with ⟨g, h⟩
  change (∑ z : G ⧸ K, (productSection K H hKH r s).rep z •
      c ((productSection K H hKH r s).factor g z,
        (productSection K H hKH r s).factor h (shift G K g z))) =
    ∑ x : G ⧸ H, r.rep x • ∑ y : H ⧸ K.subgroupOf H, (s.rep y : G) •
      c (nestedInclusion K H (s.factor (r.factor g x) y),
        nestedInclusion K H (s.factor (r.factor h (shift G H g x))
          (shift H (K.subgroupOf H) (r.factor g x) y)))
  simp_rw [Finset.smul_sum, ← mul_smul]
  rw [← Fintype.sum_prod_type (fun p : (G ⧸ H) × (H ⧸ K.subgroupOf H) =>
    (r.rep p.1 * (s.rep p.2 : G)) • c
      (nestedInclusion K H (s.factor (r.factor g p.1) p.2),
        nestedInclusion K H (s.factor (r.factor h (shift G H g p.1))
          (shift H (K.subgroupOf H) (r.factor g p.1) p.2))))]
  exact Fintype.sum_equiv (cosetEquiv K H hKH r) _ _ (fun z => by
    rw [productSection_factor K H hKH r s, productSection_factor K H hKH r s,
      cosetEquiv_shift K H hKH r s]
    rfl)


/-- The native H1 maps compose exactly for the actual product section. -/
theorem corestriction₁_product :
    (r.corestriction₁ hH A).comp
      ((s.corestriction₁ (innerOpen K H hK) A).comp (nestedH1 K H A)) =
        (productSection K H hKH r s).corestriction₁ hK A := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨b, rfl⟩ := ContinuousH1.classOf_surjective K A z
  simp only [AddMonoidHom.comp_apply, nestedH1_class, CosetSection.corestriction₁_class]
  apply congrArg (ContinuousH1.classOf G A)
  exact Subtype.ext (transfer₁_product K H hKH r s A hK hH b.val).symm

/-- The native H2 maps compose exactly for the actual product section. -/
theorem corestriction₂_product :
    (r.corestriction₂ hH A).comp
      ((s.corestriction₂ (innerOpen K H hK) A).comp (nestedH2 K H A)) =
        (productSection K H hKH r s).corestriction₂ hK A := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨c, rfl⟩ := classOf_surjective K A z
  simp only [AddMonoidHom.comp_apply, nestedH2_class, CosetSection.corestriction₂_class]
  apply congrArg (classOf G A)
  exact Subtype.ext (transfer₂_product K H hKH r s A hK hH c.val).symm

include hKH in
/-- Transitivity of the original native continuous H1 corestriction along an
actual finite-index open subgroup tower, after its canonical subgroup identification. -/
theorem corestriction₁_transitive :
    (Corestriction.corestriction₁ G H hH A).comp
      ((Corestriction.corestriction₁ H (K.subgroupOf H) (innerOpen K H hK) A).comp
        (nestedH1 K H A)) = Corestriction.corestriction₁ G K hK A := by
  let r₀ : CosetSection G H := CosetSection.chosen
  let s₀ : CosetSection H (K.subgroupOf H) := CosetSection.chosen
  have hp := corestriction₁_product K H hKH r₀ s₀ A hK hH
  rw [CosetSection.corestriction₁_independent
    (CosetSection.chosen (G := G) (H := K)) hK A (productSection K H hKH r₀ s₀)] at hp
  simpa only [r₀, s₀, CosetSection.chosen_corestriction₁] using hp

include hKH in
/-- Transitivity of the original native continuous H2 corestriction along an
actual finite-index open subgroup tower, after its canonical subgroup identification. -/
theorem corestriction₂_transitive :
    (Corestriction.corestriction₂ G H hH A).comp
      ((Corestriction.corestriction₂ H (K.subgroupOf H) (innerOpen K H hK) A).comp
        (nestedH2 K H A)) = Corestriction.corestriction₂ G K hK A := by
  let r₀ : CosetSection G H := CosetSection.chosen
  let s₀ : CosetSection H (K.subgroupOf H) := CosetSection.chosen
  have hp := corestriction₂_product K H hKH r₀ s₀ A hK hH
  rw [CosetSection.corestriction₂_independent
    (CosetSection.chosen (G := G) (H := K)) hK A (productSection K H hKH r₀ s₀)] at hp
  simpa only [r₀, s₀, CosetSection.chosen_corestriction₂] using hp


end GroupCohomology.Continuous.Corestriction.Tower
