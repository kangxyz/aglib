/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.GroupCohomology.H1.Continuous

/-!
# The affine torsor of a continuous cocycle

A continuous cocycle with discrete additive coefficients constructs a tagged
affine carrier with its translation and jointly continuous group actions.
The transport and displacement formulas retain the positive cocycle convention.
Extracted without changed declarations from `R5Lab.Cohomology.EtaleH1.ContinuousTorsors`
at R5Lab revision `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`; original
construction basis `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`,
`K2-018#eq:k2018-pointed-character`. No scheme or finiteness premise is added.
-/

@[expose] public section

noncomputable section
namespace GroupCohomology.ContinuousH1.AffineTorsors
open GroupCohomology.ContinuousH1
section Affine
universe v
variable {G : Type*} [Group G] [TopologicalSpace G]
variable {B : Type v} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
variable [DistribMulAction G B] [ContinuousSMul G B]

/-- The affine torsor's carrier is a tagged copy of the coefficient group, so
its affine G-action is kept distinct from the linear coefficient action. -/
structure AffinePoint (c : Cocycle G B) where
  /-- The element of the coefficient group underlying this tagged affine point. -/
  val : B

namespace AffinePoint
variable (c : Cocycle G B)

set_option linter.unusedSectionVars false in
-- Preserve the original auto-included hypothesis and binder order.
-- Keep the original supplied class/data inputs and binder order of this interface.
@[ext, nolint unusedArguments] theorem ext {x y : AffinePoint c} (h : x.val = y.val) : x = y := by
  cases x; cases y; cases h; rfl

/-- The affine carrier is canonically the coefficient set. -/
def equiv : AffinePoint c ≃ B :=
  ⟨val, mk, fun _ => rfl, fun _ => rfl⟩

instance [Finite B] : Finite (AffinePoint c) := Finite.of_equiv B (equiv c).symm
instance : Nonempty (AffinePoint c) := ⟨⟨0⟩⟩
instance : TopologicalSpace (AffinePoint c) := ⊥
instance : DiscreteTopology (AffinePoint c) := ⟨rfl⟩

/-- The actual additive translation action on the affine carrier. -/
instance : AddAction B (AffinePoint c) where
  vadd a t := ⟨a + t.val⟩
  zero_vadd t := ext c (zero_add t.val)
  add_vadd a b t := ext c (add_assoc a b t.val)

/-- A common continuous cocycle constructs the affine action g⋆a=c(g)+g·a. -/
instance : MulAction G (AffinePoint c) where
  smul g t := ⟨c.val g + g • t.val⟩
  one_smul t := by
    apply ext c
    change c.val 1 + (1 : G) • t.val = t.val
    rw [Cocycle.map_one, one_smul, zero_add]
  mul_smul g h t := by
    apply ext c
    change c.val (g * h) + (g * h) • t.val = c.val g + g • (c.val h + h • t.val)
    rw [Cocycle.map_mul, smul_add, mul_smul, add_assoc]

@[simp] theorem smul_val (g : G) (t : AffinePoint c) :
    (g • t).val = c.val g + g • t.val := rfl

@[simp] theorem vadd_val (a : B) (t : AffinePoint c) : (a +ᵥ t).val = a + t.val := rfl

/-- The actual affine action is jointly continuous. -/
instance : ContinuousSMul G (AffinePoint c) where
  continuous_smul :=
    (continuous_of_discreteTopology (f := mk (c := c))).comp
      ((c.continuous.comp continuous_fst).add
        (continuous_fst.smul ((continuous_of_discreteTopology (f := val (c := c))).comp
          continuous_snd)))

/-- The linear coefficient action is exactly the affine translation compatibility. -/
theorem compatible (g : G) (a : B) (t : AffinePoint c) :
    g • (a +ᵥ t) = (g • a) +ᵥ (g • t) := by
  apply ext c
  simp only [smul_val, vadd_val, smul_add]
  abel

/-- Unique transport of the constructed affine torsor is literal subtraction. -/
theorem unique_transport (s t : AffinePoint c) : ∃! a : B, a +ᵥ s = t := by
  refine ⟨t.val - s.val, ext c (sub_add_cancel _ _), ?_⟩
  intro a ha
  exact eq_sub_iff_add_eq.mpr (congrArg val ha)

/-- At the canonical zero point the affine displacement is the original cocycle. -/
-- Keep this original specific simp shortcut alongside the lower generic normalization rules.
@[simp, nolint simpNF]
theorem displacement_zero (g : G) : (g • (⟨0⟩ : AffinePoint c)).val = c.val g := by
  simp only [smul_val, smul_zero, add_zero]

/-- Multiplicative notation for the same geometric translation action. -/
instance translationMulAction : MulAction (Multiplicative B) (AffinePoint c) where
  smul a t := a.toAdd +ᵥ t
  one_smul t := zero_vadd B t
  mul_smul a b t := add_vadd a.toAdd b.toAdd t

/-- Compatibility in the multiplicative notation used by actual group schemes. -/
theorem multiplicative_compatible [MulDistribMulAction G (Multiplicative B)]
    (h : ∀ (g : G) (a : Multiplicative B), (g • a).toAdd = g • a.toAdd)
    (g : G) (a : Multiplicative B) (t : AffinePoint c) :
    g • (a • t) = (g • a) • (g • t) := by
  change g • (a.toAdd +ᵥ t) = (g • a).toAdd +ᵥ (g • t)
  rw [h]
  exact compatible c g a.toAdd t

/-- Unique multiplicative transport remains literal additive subtraction. -/
theorem multiplicative_transport (s t : AffinePoint c) :
    ∃! a : Multiplicative B, a • s = t := by
  obtain ⟨a, ha, hu⟩ := unique_transport c s t
  refine ⟨Multiplicative.ofAdd a, ha, ?_⟩
  intro b hb
  exact congrArg Multiplicative.ofAdd (hu b.toAdd hb)

end AffinePoint
end Affine

end GroupCohomology.ContinuousH1.AffineTorsors

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 c37cccfd350a68776d2f9f79878a1c83b54b91e6a172edb126a45d9c0a76241f.
Definitions, hypotheses and universes are retained modulo native names. -/
