/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Tactic.Abel

/-!
# The augmentation-kernel difference map of a possibly empty torsor

Section-level algebra for the canonical torsor extension in Stacks 03AJ,
and `K2-018#eq:k2018-pointed-character` at frozen interface basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

Sections of a sheaf torsor need not be globally nonempty. No `Nonempty P`
assumption is imposed on the construction or its naturality. The kernel map
sends `[s] - [t]` to the unique `a` with `a +ᵥ t = s`; this fixes the positive
cocycle convention. This module does not construct a sheaf or claim an Ext
comparison. Sheafification and the pushout extension are separate consumers.
-/

@[expose] public section

noncomputable section

namespace AddAction.TorsorAugmentation

universe u v u' v'
variable (M : Type u) (P : Type v) [AddCommGroup M] [AddAction M P]

/-- Unique transport between any two existing sections, allowing no sections. -/
def UniqueTransport : Prop := ∀ s t : P, ∃! a : M, a +ᵥ s = t

variable {M P}

/-- The difference has the orientation `difference s t +ᵥ t = s`. -/
def difference (h : UniqueTransport M P) (s t : P) : M :=
  Classical.choose (h t s).exists

theorem difference_vadd (h : UniqueTransport M P) (s t : P) :
    difference h s t +ᵥ t = s := Classical.choose_spec (h t s).exists

theorem difference_eq (h : UniqueTransport M P) (s t : P) (a : M)
    (ha : a +ᵥ t = s) : difference h s t = a :=
  (h t s).unique (difference_vadd h s t) ha

@[simp] theorem difference_self (h : UniqueTransport M P) (s : P) :
    difference h s s = 0 := difference_eq h s s 0 (zero_vadd _ _)

@[simp] theorem difference_action (h : UniqueTransport M P) (a : M) (t : P) :
    difference h (a +ᵥ t) t = a := difference_eq h _ t a rfl

theorem difference_chain (h : UniqueTransport M P) (s t p : P) :
    difference h s p = difference h s t + difference h t p := by
  apply difference_eq
  rw [add_vadd, difference_vadd, difference_vadd]

/-- The actual free-abelian augmentation. -/
def augmentation (P : Type v) : FreeAbelianGroup P →+ ℤ :=
  FreeAbelianGroup.lift fun _ => 1

@[simp] theorem augmentation_of (p : P) : augmentation P (.of p) = 1 := by
  simp [augmentation]

/-- The actual additive kernel, rather than a second presentation of it. -/
abbrev AugmentationKernel (P : Type v) := (augmentation P).ker

/-- The additive map sending the generator at `t` to its unique transport difference from `p`,
using `h`. -/
def basedDifference (h : UniqueTransport M P) (p : P) : FreeAbelianGroup P →+ M :=
  FreeAbelianGroup.lift fun t => difference h t p

@[simp] theorem basedDifference_of (h : UniqueTransport M P) (p s : P) :
    basedDifference h p (.of s) = difference h s p := by
  simp [basedDifference]

theorem basedDifference_change (h : UniqueTransport M P) (p q : P)
    (x : FreeAbelianGroup P) :
    basedDifference h p x = basedDifference h q x + augmentation P x • difference h q p := by
  induction x using FreeAbelianGroup.induction_on with
  | zero => simp
  | of t => simpa using difference_chain h t q p
  | neg t ht =>
      simp only [map_neg] at *
      rw [ht, neg_zsmul]
      abel
  | add x y hx hy =>
      simp only [map_add, hx, hy, add_zsmul]
      abel

/-- Canonical on augmentation-zero elements; a basepoint is chosen only inside
the definition, and its independence is proved below. Empty section types give
the unique map out of the trivial free-abelian kernel. -/
def kernelDifference (h : UniqueTransport M P) : AugmentationKernel P →+ M := by
  classical
  exact if hp : Nonempty P then
    (basedDifference h (Classical.choice hp)).comp (augmentation P).ker.subtype
  else 0

theorem kernelDifference_eq_based (h : UniqueTransport M P) (p : P)
    (x : AugmentationKernel P) : kernelDifference h x = basedDifference h p x.val := by
  classical
  have hp : Nonempty P := ⟨p⟩
  rw [kernelDifference, dite_eq_left hp]
  change basedDifference h (Classical.choice hp) x.val = _
  rw [basedDifference_change h (Classical.choice hp) p]
  have hz : augmentation P x.val = 0 := x.property
  rw [hz, zero_zsmul, add_zero]

/-- The augmentation-kernel element represented by the difference of the generators at `s` and
`t`. -/
def generatorDifference (s t : P) : AugmentationKernel P :=
  ⟨FreeAbelianGroup.of s - FreeAbelianGroup.of t, by simp⟩

@[simp] theorem kernelDifference_generatorDifference (h : UniqueTransport M P) (s t : P) :
    kernelDifference h (generatorDifference s t) = difference h s t := by
  rw [kernelDifference_eq_based h t]
  simp [generatorDifference]

theorem kernelDifference_surjective (h : UniqueTransport M P) [Nonempty P] :
    Function.Surjective (kernelDifference h) := by
  let p : P := Classical.choice inferInstance
  intro a
  exact ⟨generatorDifference (a +ᵥ p) p, by simp⟩

theorem augmentation_surjective (P : Type v) [Nonempty P] :
    Function.Surjective (augmentation P) := by
  let p : P := Classical.choice inferInstance
  intro z
  exact ⟨z • FreeAbelianGroup.of p, by simp⟩

variable {N : Type u'} {Q : Type v'} [AddCommGroup N] [AddAction N Q]

theorem difference_naturality (h : UniqueTransport M P) (k : UniqueTransport N Q)
    (q : M →+ N) (r : P → Q)
    (heq : ∀ a p, r (a +ᵥ p) = q a +ᵥ r p) (s t : P) :
    difference k (r s) (r t) = q (difference h s t) := by
  apply difference_eq
  rw [← heq, difference_vadd]

theorem augmentation_map (r : P → Q) :
    (augmentation Q).comp (FreeAbelianGroup.map r) = augmentation P := by
  apply FreeAbelianGroup.lift_ext
  intro p
  simp [FreeAbelianGroup.map_of_apply]

/-- The additive map on augmentation kernels induced by the free-abelian map of `r`. -/
def kernelMap (r : P → Q) : AugmentationKernel P →+ AugmentationKernel Q where
  toFun x := ⟨FreeAbelianGroup.map r x.val, by
    have he := DFunLike.congr_fun (augmentation_map r) x.val
    exact he.trans x.property⟩
  map_zero' := by apply Subtype.ext; exact (FreeAbelianGroup.map r).map_zero
  map_add' x y := by apply Subtype.ext; exact (FreeAbelianGroup.map r).map_add _ _

theorem basedDifference_naturality (h : UniqueTransport M P) (k : UniqueTransport N Q)
    (q : M →+ N) (r : P → Q)
    (heq : ∀ a p, r (a +ᵥ p) = q a +ᵥ r p) (p : P) :
    (basedDifference k (r p)).comp (FreeAbelianGroup.map r) =
      q.comp (basedDifference h p) := by
  apply FreeAbelianGroup.lift_ext
  intro s
  simpa [FreeAbelianGroup.map_of_apply] using difference_naturality h k q r heq s p

/-- Naturality requires no choice of compatible global sections. -/
theorem kernelDifference_naturality (h : UniqueTransport M P) (k : UniqueTransport N Q)
    (q : M →+ N) (r : P → Q)
    (heq : ∀ a p, r (a +ᵥ p) = q a +ᵥ r p) (x : AugmentationKernel P) :
    kernelDifference k (kernelMap r x) = q (kernelDifference h x) := by
  classical
  by_cases hp : Nonempty P
  · let p : P := Classical.choice hp
    rw [kernelDifference_eq_based k (r p), kernelDifference_eq_based h p]
    exact DFunLike.congr_fun (basedDifference_naturality h k q r heq p) x.val
  · let : IsEmpty P := not_nonempty_iff.mp hp
    have hx : x = 0 := Subtype.ext (Subsingleton.elim _ _)
    subst x
    simp

end AddAction.TorsorAugmentation

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 098fde129b812ab248917566efab6985c1dd32e247d6598ab11a210a71d52457.
Definitions, hypotheses and universes are retained modulo native names. -/
