/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupCohomology.H2.Continuous

/-!
# Continuous equivariant coefficient pairings and cup cocycles

Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source: `lean/R5Lab/Aglib/GroupCohomology/ContinuousCorestriction.lean`.
SHA-256: `479e6eeeb40e0da2f9def4a40653e65cb8d5fe17062a5420175c1384ba90eca7`.
Actual coefficient carriers, topologies, actions, maps and primitive hypotheses are retained.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open GroupCohomology

namespace GroupCohomology.H2.Continuous.Cup
open GroupCohomology.H2.Continuous (Cocycle complex d₀ d₁ d₀_apply d₁_apply
  d₁_d₀ d₁_eq_zero_iff d₁_cocycle cocycle₁OfClosed classOf classOf_d₁
  classOf_eq_zero_iff classOf_surjective)

variable (G : Type*) [_root_.Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (A B C : Type*)
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [DistribMulAction G B] [ContinuousSMul G B]
  [AddCommGroup C] [TopologicalSpace C] [IsTopologicalAddGroup C]
  [DistribMulAction G C] [ContinuousSMul G C]

/-- A continuous equivariant bilinear coefficient pairing. The transfer and
projection identities below are proved from this data, rather than assumed. -/
structure Pairing where
  /-- The coefficient pairing, additive in each argument. -/
  bilinear : A →+ B →+ C
  continuous : Continuous (fun p : A × B => bilinear p.1 p.2)
  equivariant : ∀ (g : G) (a : A) (b : B),
    bilinear (g • a) (g • b) = g • bilinear a b

variable {G A B C}
variable (p : Pairing G A B C)

/-- The genuine continuous cup of two continuous one-cocycles. -/
def cupCocycle (a : ContinuousH1.Cocycle G A) (b : ContinuousH1.Cocycle G B) :
    Cocycle G C :=
  ⟨⟨fun z => p.bilinear (a.val z.1) (z.1 • b.val z.2),
    p.continuous.comp ((a.continuous.comp continuous_fst).prodMk
      (continuous_fst.smul (b.continuous.comp continuous_snd)))⟩, by
    intro g h k
    change p.bilinear (a.val g) (g • b.val h) +
      p.bilinear (a.val (g * h)) ((g * h) • b.val k) =
      g • p.bilinear (a.val h) (h • b.val k) +
        p.bilinear (a.val g) (g • b.val (h * k))
    rw [a.map_mul, b.map_mul, ← p.equivariant g (a.val h) (h • b.val k)]
    simp only [map_add, AddMonoidHom.add_apply, smul_add, mul_smul]
    abel⟩

omit [IsTopologicalGroup G] [ContinuousSMul G A] [ContinuousSMul G C] in
@[simp] theorem cupCocycle_apply (a : ContinuousH1.Cocycle G A)
    (b : ContinuousH1.Cocycle G B) (g h : G) :
    (cupCocycle p a b).val (g, h) = p.bilinear (a.val g) (g • b.val h) := rfl

variable (H : Subgroup G)

/-- Restriction uses the existing continuous cocycle type and inherited action. -/
abbrev restrictCocycle (a : ContinuousH1.Cocycle G A) :
    ContinuousH1.Cocycle H A :=
  ContinuousH1.restrictionCocycles A
    { toMonoidHom := H.subtype, continuous_toFun := continuous_subtype_val } a


/-- The coefficient pairing with equivariance restricted from `G` to the subgroup `H`. -/
def restrictPairing : Pairing H A B C where
  bilinear := p.bilinear
  continuous := p.continuous
  equivariant h a b := p.equivariant (h : G) a b

end GroupCohomology.H2.Continuous.Cup
