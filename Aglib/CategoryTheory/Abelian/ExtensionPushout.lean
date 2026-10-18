/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-!
# Actual pushout of an abelian extension

Construction prerequisite for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. This generic construction provides
the actual pushout extension in Stacks 03AJ; exactness and the Ext-class
coefficient-change formula are proved, not retained inputs.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Abelian.ExtensionPushout
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (S : ShortComplex C) {L : C} (a : S.X₁ ⟶ L)

/-- The pushout of `S.f` along `a` , used as the new middle object. -/
abbrev middle := pushout S.f a
/-- The pushout inclusion from `L` into the new middle object. -/
abbrev inclusion : L ⟶ middle S a := pushout.inr S.f a

/-- The morphism from the pushout middle object to `S.X₃` induced by `S.g` and the zero map
from `L` . -/
def projection : middle S a ⟶ S.X₃ :=
  pushout.desc S.g 0 (by simp [S.zero])

@[simp] theorem inl_projection : pushout.inl S.f a ≫ projection S a = S.g := by
  exact pushout.inl_desc _ _ _
@[simp] theorem inclusion_projection : inclusion S a ≫ projection S a = 0 := by
  exact pushout.inr_desc _ _ _

/-- The short complex from `L` through the pushout middle object to `S.X₃` . -/
def complex : ShortComplex C :=
  ShortComplex.mk (inclusion S a) (projection S a) (inclusion_projection S a)

variable (hS : S.ShortExact)

theorem inclusion_mono (hS : S.ShortExact) : Mono (inclusion S a) := by
  let := hS.mono_f
  infer_instance

theorem projection_epi (hS : S.ShortExact) : Epi (projection S a) := by
  let := hS.epi_g
  exact epi_of_epi_fac (inl_projection S a)

/-- The pushout projection is the cokernel of the pushed-out inclusion. -/
def projectionIsCokernel (hS : S.ShortExact) :
    IsColimit (CokernelCofork.ofπ (projection S a) (inclusion_projection S a)) := by
  let := hS.epi_g
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun {Z} q hq => hS.exact.desc (pushout.inl S.f a ≫ q) ?_) ?_ ?_
  · rw [← Category.assoc, pushout.condition, Category.assoc, hq, comp_zero]
  · intro Z q hq
    apply pushout.hom_ext
    · rw [← Category.assoc, inl_projection, hS.exact.g_desc]
    · rw [← Category.assoc, inclusion_projection, zero_comp]
      exact hq.symm
  · intro Z q hq m hm
    apply (cancel_epi S.g).mp
    rw [hS.exact.g_desc, ← inl_projection S a, Category.assoc, hm]

/-- Pushout preserves short exactness in an abelian category. -/
theorem shortExact (hS : S.ShortExact) : (complex S a).ShortExact := by
  let := inclusion_mono S a hS
  let := projection_epi S a hS
  exact { exact := (complex S a).exact_of_g_is_cokernel (projectionIsCokernel S a hS)
          mono_f := inclusion_mono S a hS
          epi_g := projection_epi S a hS }

/-- The actual morphism from the original extension to its pushout. -/
def map : S ⟶ complex S a where
  τ₁ := a
  τ₂ := pushout.inl S.f a
  τ₃ := 𝟙 _
  comm₁₂ := pushout.condition.symm
  comm₂₃ := by simp [complex]

variable [HasExt.{w} C]

/-- The pushout extension class is coefficient change of the original class. -/
theorem extClass : hS.extClass.comp (CategoryTheory.Abelian.Ext.mk₀ a) (add_zero 1) =
    (shortExact S a hS).extClass := by
  have h := ShortComplex.ShortExact.extClass_naturality hS (shortExact S a hS) (map S a)
  change hS.extClass.comp (CategoryTheory.Abelian.Ext.mk₀ a) (add_zero 1) =
    (CategoryTheory.Abelian.Ext.mk₀ (𝟙 S.X₃)).comp (shortExact S a hS).extClass (zero_add 1) at h
  simpa only [CategoryTheory.Abelian.Ext.mk₀_id_comp] using h

end CategoryTheory.Abelian.ExtensionPushout

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 30ff8c882671bdbcad19c5fdb46d01e3dd502fc00d15568dd9a07e8fd8b3c945.
Definitions, hypotheses and universes are retained modulo native names. -/
