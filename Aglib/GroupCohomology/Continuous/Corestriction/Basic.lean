/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupCohomology.Continuous.Corestriction.Sections

/-!
# Canonical continuous corestriction from the chosen section

Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source: `lean/R5Lab/Aglib/GroupCohomology/ContinuousCorestriction.lean`.
SHA-256: `479e6eeeb40e0da2f9def4a40653e65cb8d5fe17062a5420175c1384ba90eca7`.
Actual coefficient carriers, topologies, actions, maps and primitive hypotheses are retained.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open GroupCohomology

namespace GroupCohomology.Continuous.Corestriction
open GroupCohomology.H2.Continuous (Cocycle complex d₀ d₁ d₀_apply d₁_apply
  d₁_d₀ d₁_eq_zero_iff d₁_cocycle cocycle₁OfClosed classOf classOf_d₁
  classOf_eq_zero_iff classOf_surjective)

variable (G : Type*) [_root_.Group G]
variable (H : Subgroup G)

theorem factor_mem (g : G) (x : G ⧸ H) :
    (representative G H x)⁻¹ * g * representative G H (shift G H g x) ∈ H := by
  rw [mul_assoc]
  apply QuotientGroup.eq.mp
  change QuotientGroup.mk (representative G H x) =
    QuotientGroup.mk (g * representative G H (shift G H g x))
  simp only [representative, QuotientGroup.out_eq', ← smul_eq_mul,
    MulAction.Quotient.mk_smul_out, shift, smul_inv_smul]

/-- The subgroup-valued transition function of the chosen coset representatives. -/
abbrev factor (g : G) (x : G ⧸ H) : H :=
  CosetSection.factor (CosetSection.chosen (G := G) (H := H)) g x

theorem factor_mul (g h : G) (x : G ⧸ H) :
    factor G H (g * h) x = factor G H g x * factor G H h (shift G H g x) := by
  apply Subtype.ext
  change (representative G H x)⁻¹ * (g * h) * representative G H (shift G H (g * h) x) =
    ((representative G H x)⁻¹ * g * representative G H (shift G H g x)) *
      ((representative G H (shift G H g x))⁻¹ * h *
        representative G H (shift G H h (shift G H g x)))
  rw [shift_mul]
  group

theorem representative_factor (g : G) (x : G ⧸ H) :
    representative G H x * (factor G H g x : G) =
      g * representative G H (shift G H g x) := by
  change representative G H x *
    ((representative G H x)⁻¹ * g * representative G H (shift G H g x)) = _
  group

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable (hH : IsOpen (H : Set G))

include hH in
theorem continuous_representative : Continuous (representative G H) := by
  let := QuotientGroup.discreteTopology hH
  exact continuous_of_discreteTopology

include hH in
theorem continuous_factor : Continuous (fun p : G × (G ⧸ H) => factor G H p.1 p.2) := by
  apply Continuous.subtype_mk
  exact (((continuous_representative G H hH).comp continuous_snd).inv.mul continuous_fst).mul
    ((continuous_representative G H hH).comp (continuous_shift G H))

variable (A : Type*) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]
variable [H.FiniteIndex]
/-- The finite coset enumeration used by transfer for the chosen section. -/
local instance : Fintype (G ⧸ H) := H.fintypeQuotientOfFiniteIndex

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [ContinuousSMul G A] [H.FiniteIndex] in
theorem representative_factor_smul (g : G) (x : G ⧸ H) (a : A) :
    representative G H x • (factor G H g x • a) =
      g • (representative G H (shift G H g x) • a) := by
  change representative G H x • ((factor G H g x : G) • a) = _
  rw [← mul_smul, representative_factor, mul_smul]

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [ContinuousSMul G A] in
theorem sum_factor_smul (g : G) (f : G ⧸ H → A) :
    ∑ x : G ⧸ H, representative G H x • (factor G H g x • f (shift G H g x)) =
      g • ∑ x : G ⧸ H, representative G H x • f x := by
  simp only [representative_factor_smul, ← Finset.smul_sum]
  exact congrArg (g • ·) (sum_shift G H A g (fun x => representative G H x • f x))

/-- The actual degree-zero transfer cochain. -/
abbrev transfer₀ : A →+ A :=
  CosetSection.transfer₀ (CosetSection.chosen (G := G) (H := H)) A

/-- The actual continuous degree-one cochain transfer. -/
abbrev transfer₁ : C(H, A) →+ C(G, A) :=
  CosetSection.transfer₁ (CosetSection.chosen (G := G) (H := H)) hH A

theorem transfer₁_apply (b : C(H, A)) (g : G) :
    transfer₁ G H hH A b g =
      ∑ x : G ⧸ H, representative G H x • b (factor G H g x) := rfl

/-- The actual continuous degree-two cochain transfer. -/
abbrev transfer₂ : C(H × H, A) →+ C(G × G, A) :=
  CosetSection.transfer₂ (CosetSection.chosen (G := G) (H := H)) hH A

theorem transfer₂_apply (c : C(H × H, A)) (g h : G) :
    transfer₂ G H hH A c (g, h) =
      ∑ x : G ⧸ H, representative G H x •
        c (factor G H g x, factor G H h (shift G H g x)) := rfl

/-- Transfer takes genuine continuous two-cocycles to genuine two-cocycles. -/
theorem transfer₂_cocycle (c : Cocycle H A) (g h k : G) :
    transfer₂ G H hH A c.val (g, h) + transfer₂ G H hH A c.val (g * h, k) =
      g • transfer₂ G H hH A c.val (h, k) + transfer₂ G H hH A c.val (g, h * k) := by
  simp only [transfer₂_apply, ← Finset.sum_add_distrib, ← smul_add, factor_mul, shift_mul]
  have hp : ∀ x : G ⧸ H,
      c.val (factor G H g x, factor G H h (shift G H g x)) +
        c.val (factor G H g x * factor G H h (shift G H g x),
          factor G H k (shift G H h (shift G H g x))) =
      factor G H g x • c.val (factor G H h (shift G H g x),
        factor G H k (shift G H h (shift G H g x))) +
        c.val (factor G H g x,
          factor G H h (shift G H g x) * factor G H k (shift G H h (shift G H g x))) :=
    fun x => c.property _ _ _
  simp_rw [hp, smul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  exact sum_factor_smul G H A g (fun x =>
    c.val (factor G H h x, factor G H k (shift G H h x)))

/-- Transfer restricted to genuine continuous two-cocycles. -/
abbrev transferCocycles₂ : Cocycle H A →+ Cocycle G A :=
  CosetSection.transferCocycles₂ (CosetSection.chosen (G := G) (H := H)) hH A

/-- The cochain transfer commutes with the genuine bar differential. -/
theorem transfer_d₁ (b : C(H, A)) :
    transferCocycles₂ G H hH A (d₁ H A b) = d₁ G A (transfer₁ G H hH A b) := by
  apply Cocycle.ext
  intro g h
  change (∑ x : G ⧸ H, representative G H x •
    ((factor G H g x) • b (factor G H h (shift G H g x)) -
      b (factor G H g x * factor G H h (shift G H g x)) + b (factor G H g x))) =
    g • (∑ x : G ⧸ H, representative G H x • b (factor G H h x)) -
      (∑ x : G ⧸ H, representative G H x • b (factor G H (g * h) x)) +
      (∑ x : G ⧸ H, representative G H x • b (factor G H g x))
  simp_rw [← factor_mul, smul_add, smul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_factor_smul G H A g (fun x => b (factor G H h x))]

/-- The constructed transfer also preserves continuous one-cocycles. -/
abbrev transferCocycles₁ : ContinuousH1.Cocycle H A →+
    ContinuousH1.Cocycle G A :=
  CosetSection.transferCocycles₁ (CosetSection.chosen (G := G) (H := H)) hH A

/-- The same formula transfers principal cocycles to principal cocycles. -/
theorem transfer_principal (a : A) :
    transferCocycles₁ G H hH A (ContinuousH1.principal H A a) =
      ContinuousH1.principal G A (transfer₀ G H A a) := by
  apply ContinuousH1.Cocycle.ext
  intro g
  change (∑ x : G ⧸ H, representative G H x • (factor G H g x • a - a)) =
    g • (∑ x : G ⧸ H, representative G H x • a) -
      (∑ x : G ⧸ H, representative G H x • a)
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  exact sum_factor_smul G H A g (fun _ => a)

/-- The induced native continuous H1 corestriction. -/
abbrev corestriction₁ : ContinuousH1.H1 H A →+
    ContinuousH1.H1 G A :=
  CosetSection.corestriction₁ (CosetSection.chosen (G := G) (H := H)) hH A

@[simp] theorem corestriction₁_class (c : ContinuousH1.Cocycle H A) :
    corestriction₁ G H hH A (ContinuousH1.classOf H A c) =
      ContinuousH1.classOf G A (transferCocycles₁ G H hH A c) := rfl

/-- Transfer on the existing smart-truncation cycle subtype. -/
abbrev transferCycles₂ : (complex H A).Cycles₂ →+ (complex G A).Cycles₂ :=
  CosetSection.transferCycles₂ (CosetSection.chosen (G := G) (H := H)) hH A

/-- The actual boundary subgroup is preserved by the constructed cochain map. -/
theorem transfer_boundary₂ (b : C(H, A)) :
    transferCycles₂ G H hH A ((complex H A).boundary₂ b) =
      (complex G A).boundary₂ (transfer₁ G H hH A b) :=
  Subtype.ext (transfer_d₁ G H hH A b)

/-- Native continuous H2 corestriction, constructed on its actual quotient. -/
abbrev corestriction₂ : H2.Continuous.Group H A →+ H2.Continuous.Group G A :=
  CosetSection.corestriction₂ (CosetSection.chosen (G := G) (H := H)) hH A

@[simp] theorem corestriction₂_class (c : Cocycle H A) :
    corestriction₂ G H hH A (classOf H A c) =
      classOf G A (transferCocycles₂ G H hH A c) := rfl


end GroupCohomology.Continuous.Corestriction
