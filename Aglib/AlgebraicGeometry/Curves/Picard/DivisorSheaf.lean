/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.RationalFunctions
public import Aglib.AlgebraicGeometry.Curves.Divisors.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/



/-!
# Actual fractional-ideal sheaves for divisors

C2 local construction, K2-018 `lem:k2018-geometric-exact-order`, frozen basis
`7f86e4a`. On a nonempty open, the sections are actual rational functions
satisfying `ord_x(f) + D(x) ≥ 0`, with zero included separately. The module
structure is that induced by the actual generic germ of regular functions.
The actual sheaf `divisorSheaf` is constructed as a subsheaf of the generic
pushforward of the structure sheaf, with membership proved local. Its empty
open sections form a subsingleton, and on every nonempty open its sections
are linearly equivalent to the displayed fractional-ideal module. Local
trivializations are constructed separately in `LocalTrivialization`; the
divisor-class/Picard equivalence is not asserted here. Sources: Stacks Tags 02SG and 02SH for
the subsequent meromorphic-section construction.
-/
@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Modules.RationalFunctions
open AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass
universe u
variable (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
variable [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]

/-- Actual local fractional-ideal membership with the positive-divisor convention. -/
def IsFractionalSection (D : Divisor X) (U : X.Opens) (f : X.functionField) : Prop :=
  f = 0 ∨ ∀ x : ClosedPoint X, x.val ∈ U → 0 ≤ X.ord f x.val + D x

/-- The actual module of fractional sections on a nonempty open. -/
def fractionalSections (D : Divisor X) (U : X.Opens) [Nonempty U] :
    Submodule Γ(X, U) X.functionField where
  carrier := IsFractionalSection X D U
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro f g hf hg
    by_cases hfg : f + g = 0
    · exact Or.inl hfg
    right
    intro x hx
    rcases hf with rfl | hf
    · simpa using hg.resolve_left (by simpa using hfg) x hx
    rcases hg with rfl | hg
    · simpa using hf x hx
    have : IsDiscreteValuationRing (X.presheaf.stalk x.val) := inferInstance
    have hv := Scheme.ord_add (x := x.val) hfg
    have hmin : -D x ≤ min (X.ord f x.val) (X.ord g x.val) := by
      exact le_min (by linarith [hf x hx]) (by linarith [hg x hx])
    linarith
  smul_mem' := by
    intro a f hf
    by_cases ha : a = 0
    · left; simp [ha]
    rcases hf with rfl | hf
    · left; simp
    right
    intro x hx
    have hv := Scheme.ord_le_smul hx ha f
    linarith [hf x hx]

omit [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)] in
/-- Restriction preserves the actual valuation inequalities. -/
theorem isFractionalSection_restrict {D : Divisor X} {U V : X.Opens}
    (hUV : U ≤ V) {f : X.functionField} (hf : IsFractionalSection X D V f) :
    IsFractionalSection X D U f := by
  rcases hf with rfl | hf
  · exact Or.inl rfl
  · exact Or.inr (fun x hx => hf x (hUV hx))

omit [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)] in
/-- Multiplication adds actual divisors at the level of fractional sections. -/
theorem isFractionalSection_mul {D E : Divisor X} {U : X.Opens}
    {f g : X.functionField} (hf : IsFractionalSection X D U f)
    (hg : IsFractionalSection X E U g) : IsFractionalSection X (D + E) U (f * g) := by
  by_cases hf0 : f = 0
  · left; simp [hf0]
  by_cases hg0 : g = 0
  · left; simp [hg0]
  right
  intro x hx
  have h1 := hf.resolve_left hf0 x hx
  have h2 := hg.resolve_left hg0 x hx
  rw [Scheme.ord_mul hf0 hg0, Finsupp.add_apply]
  linarith

def fractionalPresheaf (D : Divisor X) : (rationalFunctions X).val.Submodule where
  obj U := if h : Nonempty U.unop then
    letI := h
    (fractionalSections X D U.unop).comap (rationalValue X U.unop)
    else ⊤
  map {U V} f := by
    intro s hs
    by_cases hV : Nonempty V.unop
    · have hU : Nonempty U.unop := ⟨⟨hV.some.val, f.unop.le hV.some.property⟩⟩
      let := hV
      let := hU
      simp only [dite_eq_left hV, dite_eq_left hU, Submodule.mem_comap] at hs ⊢
      change IsFractionalSection X D V.unop
        (rationalValue X V.unop ((rationalFunctions X).val.map f s))
      have he := rationalValue_restrict X f.unop s
      rw [Quiver.Hom.op_unop] at he
      exact he.symm ▸ isFractionalSection_restrict X f.unop.le hs
    · simp [hV]

def fractionalSubsheaf (D : Divisor X) : SheafOfModules.Submodule (rationalFunctions X) where
  toSubmodule := fractionalPresheaf X D
  isSheaf {U} s hs := by
    by_cases hU : Nonempty U.unop
    · let := hU
      change s ∈ (fractionalPresheaf X D).obj U
      simp only [fractionalPresheaf, dite_eq_left hU, Submodule.mem_comap]
      change IsFractionalSection X D U.unop (rationalValue X U.unop s)
      by_cases hz : rationalValue X U.unop s = 0
      · exact Or.inl hz
      right
      intro x hx
      obtain ⟨V, i, hi, hxV⟩ := hs x.val hx
      let : Nonempty V := ⟨⟨x.val, hxV⟩⟩
      have hv : (rationalFunctions X).val.map i.op s ∈
          (fractionalPresheaf X D).obj (op V) := hi
      simp only [fractionalPresheaf, dite_eq_left (inferInstance : Nonempty V),
        Submodule.mem_comap] at hv
      change IsFractionalSection X D V
        (rationalValue X V ((rationalFunctions X).val.map i.op s)) at hv
      rw [rationalValue_restrict] at hv
      exact hv.resolve_left hz x hxV
    · simp only [fractionalPresheaf, dite_eq_right hU, Submodule.mem_top]

/-- The actual fractional-ideal module sheaf O(D), including its empty-open value. -/
def divisorSheaf (D : Divisor X) : SheafOfModules.{u} X.ringCatSheaf :=
  (fractionalSubsheaf X D).toSheafOfModules

/-- Empty-open sections are the zero module, not the function field. -/
theorem divisorSheaf_empty_subsingleton (D : Divisor X) : Subsingleton ((divisorSheaf X D).val.obj
  (op ⊥)) := by
  change Subsingleton ↥((fractionalPresheaf X D).obj (op ⊥))
  have : Subsingleton ((rationalFunctions X).val.obj (op ⊥)) := by
    change Subsingleton Γ(Spec X.functionField, (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ ⊥)
    rw [Scheme.Hom.preimage_bot]
    infer_instance
  infer_instance

def divisorSheafSectionsEquiv (D : Divisor X) (U : X.Opens) [hU : Nonempty U] :
    (divisorSheaf X D).val.obj (op U) ≃ₗ[Γ(X, U)] fractionalSections X D U := by
  change ↥((fractionalPresheaf X D).obj (op U)) ≃ₗ[Γ(X, U)] _
  simp only [fractionalPresheaf]
  rw [dite_eq_left hU]
  exact LinearEquiv.ofSubmodule' (rationalValueEquiv X U) (fractionalSections X D U)

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.DivisorClass
