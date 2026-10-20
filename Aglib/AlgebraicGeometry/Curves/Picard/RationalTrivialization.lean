/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.RationalTrivialization
public import Aglib.AlgebraicGeometry.Curves.Picard.DivisorTensor
public import Aglib.AlgebraicGeometry.Modules.Invertible.Basic
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible
  (IsLocallyRankOne isLocallyRankOne_iff_local_unit)

/-!
# Rational trivialization of an actual invertible sheaf

C2, K2-018 `lem:k2018-geometric-exact-order`, frozen source basis `7f86e4a`.
For an integral scheme, restrictions of a locally rank-one module sheaf to
nonempty subopens are injective. A chosen nonempty trivializing chart gives
an injective function-field coordinate, with the actual restriction and
scalar laws. The actual morphism into the generic direct-image rational
sheaf has zero empty-open sections, rather than a constant-field value there.

On a Noetherian integral scheme, the negative orders of the local generator
coordinates give a genuine finitely supported closed-point divisor. Changing
the local chart preserves its coefficient: both change-of-basis directions
are regular. Support lies in the codimension-one part of the complement of
the generic chart, which is finite by Noetherianity. The degree-one case is
consumed by the subsequent O(D) inverse construction. No divisor/Picard
identification or rational-trivialization existence is assumed. The DVR
hypotheses used by the fractional-section infrastructure remain explicit.
Sources: Stacks Tags 02SG and 02SH (meromorphic sections and their divisors).
-/
@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.RationalFunctions
open AlgebraicGeometry.Scheme.Modules.Invertible.RationalTrivialization
open AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.OverField.Curve.Divisors
namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard.RationalTrivialization
universe u
variable (X : Scheme.{u}) [IsIntegral X]

variable (M : SheafOfModules.{u} X.ringCatSheaf)
variable (U₀ : X.Opens) [Nonempty U₀]
variable (e : M.over U₀ ≅ SheafOfModules.unit (X.ringCatSheaf.over U₀))

open DivisorClass
variable [AlgebraicGeometry.IsNoetherian X]
variable [hDVR : ∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]

omit [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)] in
theorem generator_order_le (hM : IsLocallyRankOne X M)
    (W Z : X.Opens) [Nonempty W] [Nonempty Z]
    (d : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    (c : M.over Z ≅ SheafOfModules.unit (X.ringCatSheaf.over Z))
    (x : ClosedPoint X) (hxW : x.val ∈ W) (hxZ : x.val ∈ Z) :
    X.ord (coordinate X M U₀ e W (chartGenerator X M W d)) x.val ≤
      X.ord (coordinate X M U₀ e Z (chartGenerator X M Z c)) x.val := by
  let A := W ⊓ Z
  let : Nonempty A := ⟨⟨x.val, hxW, hxZ⟩⟩
  let s := M.val.map (homOfLE inf_le_right : A ⟶ Z).op (chartGenerator X M Z c)
  let a := chartSectionEquiv X M W d A inf_le_left s
  have he : coordinate X M U₀ e Z (chartGenerator X M Z c) =
      X.germToFunctionField A a * coordinate X M U₀ e W (chartGenerator X M W d) := by
    rw [← coordinate_naturality X M U₀ e (homOfLE inf_le_right : A ⟶ Z)]
    exact coordinate_chart X M U₀ e W d A inf_le_left s
  have ha : a ≠ 0 := by
    intro ha
    rw [ha, map_zero, zero_mul] at he
    exact coordinate_generator_ne_zero X M U₀ e hM Z c he
  rw [he]
  exact Scheme.ord_le_smul (show x.val ∈ A from ⟨hxW, hxZ⟩) ha _

omit hDVR in
theorem generator_order_eq
    [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
    (hM : IsLocallyRankOne X M)
    (W Z : X.Opens) [Nonempty W] [Nonempty Z]
    (d : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    (c : M.over Z ≅ SheafOfModules.unit (X.ringCatSheaf.over Z))
    (x : ClosedPoint X) (hxW : x.val ∈ W) (hxZ : x.val ∈ Z) :
    X.ord (coordinate X M U₀ e W (chartGenerator X M W d)) x.val =
      X.ord (coordinate X M U₀ e Z (chartGenerator X M Z c)) x.val :=
  le_antisymm (generator_order_le X M U₀ e hM W Z d c x hxW hxZ)
    (generator_order_le X M U₀ e hM Z W c d x hxZ hxW)

def localChart (hM : IsLocallyRankOne X M) (x : X) :
    Σ W : X.Opens, {_d : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W) // x ∈ W} := by
  let h := (isLocallyRankOne_iff_local_unit X M).mp hM x
  exact ⟨h.choose, h.choose_spec.2.some, h.choose_spec.1⟩

def divisorCoefficient (hM : IsLocallyRankOne X M) (x : ClosedPoint X) : ℤ :=
  let c := localChart X M hM x.val
  letI : Nonempty c.1 := ⟨⟨x.val, c.2.property⟩⟩;
  -X.ord (coordinate X M U₀ e c.1 (chartGenerator X M c.1 c.2.val)) x.val

theorem divisorCoefficient_chart (hM : IsLocallyRankOne X M)
    (W : X.Opens) [Nonempty W]
    (d : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))
    (x : ClosedPoint X) (hxW : x.val ∈ W) :
    divisorCoefficient X M U₀ e hM x =
      -X.ord (coordinate X M U₀ e W (chartGenerator X M W d)) x.val := by
  let : Nonempty (localChart X M hM x.val).1 := ⟨⟨x.val, (localChart X M hM x.val).2.property⟩⟩
  dsimp only [divisorCoefficient]
  congr 1
  exact generator_order_eq X M U₀ e hM _ W _ d x (localChart X M hM x.val).2.property hxW

omit [AlgebraicGeometry.IsNoetherian X]
  [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)] in
theorem coordinate_own_generator :
    coordinate X M U₀ e U₀ (chartGenerator X M U₀ e) = 1 := by
  let := nonempty_inf X U₀ U₀
  let j : U₀ ⊓ U₀ ⟶ U₀ := homOfLE inf_le_left
  change X.germToFunctionField (U₀ ⊓ U₀)
    (chartSectionEquiv X M U₀ e (U₀ ⊓ U₀) inf_le_right
      (M.val.map j.op (chartGenerator X M U₀ e))) = 1
  rw [chartGenerator_restrict]
  simp only [LinearEquiv.apply_symm_apply, map_one]

theorem divisorCoefficient_zero_on_chart (hM : IsLocallyRankOne X M)
    (x : ClosedPoint X) (hx : x.val ∈ U₀) : divisorCoefficient X M U₀ e hM x = 0 := by
  rw [divisorCoefficient_chart X M U₀ e hM U₀ e x hx, coordinate_own_generator]
  have ho : X.ord (1 : X.functionField) x.val = 0 := (localOrder X x).map_zero
  rw [ho, neg_zero]

theorem divisorCoefficient_finite_support (hM : IsLocallyRankOne X M) :
    (Function.support (divisorCoefficient X M U₀ e hM)).Finite := by
  have hc : IsClosed ((U₀ : Set X)ᶜ) := U₀.isOpen.isClosed_compl
  let : QuasiSober ↥((U₀ : Set X)ᶜ) := hc.isClosedEmbedding_subtypeVal.quasiSober
  have hp : closure ((U₀ : Set X)ᶜ) ≠ Set.univ := by
    rw [hc.closure_eq]
    intro he
    have hm : (Classical.choice ‹Nonempty U₀›).val ∈ (U₀ : Set X)ᶜ := he ▸ Set.mem_univ _
    exact hm (Classical.choice ‹Nonempty U₀›).property
  apply ((NoetherianSpace.finite_coheight_one_of_closure_ne_univ hp).preimage_embedding
    ⟨Subtype.val, Subtype.val_injective⟩).subset
  intro x hx
  refine ⟨?_, ?_⟩
  · intro hxU
    exact hx (divisorCoefficient_zero_on_chart X M U₀ e hM x hxU)
  · by_contra h
    change Order.coheight x.val ≠ 1 at h
    apply hx
    dsimp only [divisorCoefficient]
    rw [Scheme.ord_eq_zero_of_coheight_neq_one h, neg_zero]

/-- The actual finite divisor obtained from a generic-point trivialization. -/
def divisor (hM : IsLocallyRankOne X M) : Divisor X :=
  Finsupp.ofSupportFinite (divisorCoefficient X M U₀ e hM)
    (divisorCoefficient_finite_support X M U₀ e hM)

@[simp] theorem divisor_apply (hM : IsLocallyRankOne X M) (x : ClosedPoint X) :
    divisor X M U₀ e hM x = divisorCoefficient X M U₀ e hM x := rfl

end AlgebraicGeometry.Scheme.OverField.Curve.Picard.RationalTrivialization
