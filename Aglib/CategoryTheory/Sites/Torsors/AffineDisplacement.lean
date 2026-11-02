/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Group.Action.TorsorAugmentation
public import Aglib.GroupCohomology.H1.AffineTorsor
public import Mathlib.Algebra.Group.Action.End

/-! # Positive displacement on an actual continuous affine torsor

The carrier, translation action and permutation action are supplied actual
objects. UniqueTransport is the existing predicate, also meaningful for an
empty carrier. A basepoint is required only where used. Continuity is a property
of the original displacement maps; no cocycle, class or comparison conclusion
is assumed. The inverse affine carrier is the existing AffinePoint.
-/

@[expose] public noncomputable section

open AddAction.TorsorAugmentation

namespace GroupCohomology.ContinuousH1.AffineTorsors

universe uG uA uP uH uB uQ

section Coordinates

variable {A : Type uA} {P : Type uP} [AddCommGroup A] [AddAction A P]
  (h : UniqueTransport A P)

/-- The same actual positive transporter gives coordinates at a supplied point. -/
def coordinates (t : P) : P ≃ A where
  toFun x := difference h x t
  invFun a := a +ᵥ t
  left_inv x := difference_vadd h x t
  right_inv a := difference_action h a t

@[simp] theorem coordinates_apply (t x : P) : coordinates h t x = difference h x t := rfl

@[simp] theorem coordinates_symm_apply (t : P) (a : A) :
    (coordinates h t).symm a = a +ᵥ t := rfl

theorem coordinates_self (t : P) : coordinates h t t = 0 := difference_self h t

/-- Actual translation adds its coefficient in the original coordinates. -/
theorem coordinates_vadd (t x : P) (a : A) :
    coordinates h t (a +ᵥ x) = a + coordinates h t x := by
  exact (difference_chain h (a +ᵥ x) x t).trans
    (congrArg (fun b => b + difference h x t) (difference_action h a x))

/-- Changing the basepoint subtracts its old positive coordinate. -/
theorem coordinates_change (t t' x : P) :
    coordinates h t' x = coordinates h t x - coordinates h t t' := by
  apply (eq_sub_iff_add_eq).mpr
  exact (difference_chain h x t' t).symm

variable {B : Type uB} {Q : Type uQ} [AddCommGroup B] [AddAction B Q]
  (k : UniqueTransport B Q) (q : A →+ B) (r : P → Q)
  (heq : ∀ a x, r (a +ᵥ x) = q a +ᵥ r x)

include heq in
/-- An actual coefficient-relative equivariant map preserves the same coordinates. -/
theorem coordinates_naturality (t x : P) :
    coordinates k (r t) (r x) = q (coordinates h t x) :=
  difference_naturality h k q r heq x t

end Coordinates

section Displacement

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]
  {P : Type uP} [AddAction A P]
  (h : UniqueTransport A P) (ρ : G →* Equiv.Perm P)
  (haff : ∀ (g : G) (a : A) (x : P), ρ g (a +ᵥ x) = (g • a) +ᵥ ρ g x)

/-- The actual linear coefficient action at one group element. -/
def smulAddHom (g : G) : A →+ A where
  toFun a := g • a
  map_zero' := smul_zero g
  map_add' := smul_add g

omit [TopologicalSpace G] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [ContinuousSMul G A] in
include haff in
/-- Coordinates of an actual affine permutation retain the positive convention. -/
theorem coordinates_monodromy (t x : P) (g : G) :
    coordinates h t (ρ g x) = coordinates h t (ρ g t) + g • coordinates h t x := by
  have hn := coordinates_naturality h h (smulAddHom g) (ρ g) (haff g) t x
  have hc := difference_chain h (ρ g x) (ρ g t) t
  change coordinates h t (ρ g x) = coordinates h (ρ g t) (ρ g x) +
    coordinates h t (ρ g t) at hc
  exact hc.trans ((congrArg (fun a => a + coordinates h t (ρ g t)) hn).trans
    (add_comm _ _))

variable (hc : ∀ t : P, Continuous (fun g : G => coordinates h t (ρ g t)))

/-- Positive displacement constructs the actual continuous cocycle. -/
def basedCocycle (t : P) : Cocycle G A :=
  ⟨⟨fun g => coordinates h t (ρ g t), hc t⟩, by
    intro g k
    change coordinates h t (ρ (g * k) t) = _
    rw [map_mul]
    exact coordinates_monodromy h ρ haff t (ρ k t) g⟩

omit [ContinuousSMul G A] in
@[simp] theorem basedCocycle_apply (t : P) (g : G) :
    (basedCocycle h ρ haff hc t).val g = coordinates h t (ρ g t) := rfl

omit [ContinuousSMul G A] in
/-- Its defining equation is the original positive translation on the same carrier. -/
theorem basedCocycle_action (t : P) (g : G) :
    (basedCocycle h ρ haff hc t).val g +ᵥ t = ρ g t :=
  difference_vadd h (ρ g t) t

/-- A basepoint change is precisely the positive principal cocycle. -/
theorem basedCocycle_change (t t' : P) :
    basedCocycle h ρ haff hc t' = basedCocycle h ρ haff hc t +
      principal G A (coordinates h t t') := by
  apply Cocycle.ext
  intro g
  rw [Cocycle.add_apply, principal_apply, basedCocycle_apply, basedCocycle_apply,
    coordinates_change, coordinates_monodromy h ρ haff]
  abel

/-- The constructed class is independent of the supplied point. -/
theorem basedCocycle_class_independent (t t' : P) :
    classOf G A (basedCocycle h ρ haff hc t') =
      classOf G A (basedCocycle h ρ haff hc t) := by
  rw [basedCocycle_change, map_add, classOf_principal, add_zero]

/-- A point is chosen internally only for the class of a genuinely nonempty carrier. -/
def torsorClass [Nonempty P] : H1 G A :=
  classOf G A (basedCocycle h ρ haff hc (Classical.choice inferInstance))

theorem torsorClass_eq [Nonempty P] (t : P) :
    torsorClass h ρ haff hc = classOf G A (basedCocycle h ρ haff hc t) :=
  basedCocycle_class_independent h ρ haff hc t _

section Naturality

variable {H : Type uH} [Group H] [TopologicalSpace H]
  {B : Type uB} [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [DistribMulAction H B] [ContinuousSMul H B]
  {Q : Type uQ} [AddAction B Q]
  (k : UniqueTransport B Q) (σ : H →* Equiv.Perm Q)
  (haff' : ∀ (g : H) (a : B) (x : Q), σ g (a +ᵥ x) = (g • a) +ᵥ σ g x)
  (hc' : ∀ t : Q, Continuous (fun g : H => coordinates k t (σ g t)))
  {φ : ContinuousMonoidHom H G} (q : PullbackMap (A := A) (B := B) φ)
  (r : P → Q) (heq : ∀ (a : A) (x : P), r (a +ᵥ x) = q a +ᵥ r x)
  (hρ : ∀ (g : H) (x : P), r (ρ (φ g) x) = σ g (r x))

omit [ContinuousSMul G A] [ContinuousSMul H B] in
include heq hρ in
/-- Restriction and coefficient maps preserve the literal displacement cocycle. -/
theorem basedCocycle_naturality (t : P) :
    basedCocycle k σ haff' hc' (r t) = q.onCocycles (basedCocycle h ρ haff hc t) := by
  apply Cocycle.ext
  intro g
  rw [PullbackMap.onCocycles_apply, basedCocycle_apply, basedCocycle_apply, ← hρ]
  exact coordinates_naturality h k q.toAddMonoidHom r heq t _

include heq hρ in
/-- The same representative construction supplies the actual class square. -/
theorem torsorClass_naturality [Nonempty P] [Nonempty Q] :
    torsorClass k σ haff' hc' = q.onH1 (torsorClass h ρ haff hc) := by
  let t : P := Classical.choice inferInstance
  rw [torsorClass_eq k σ haff' hc' (r t), torsorClass_eq h ρ haff hc t,
    basedCocycle_naturality h ρ haff hc k σ haff' hc' q r heq hρ t,
    PullbackMap.onH1_classOf]

end Naturality

section EqualCocycles

variable {Q : Type uQ} [AddAction A Q] (k : UniqueTransport A Q)
  (σ : G →* Equiv.Perm Q)
  (haff' : ∀ (g : G) (a : A) (x : Q), σ g (a +ᵥ x) = (g • a) +ᵥ σ g x)
  (hc' : ∀ t : Q, Continuous (fun g : G => coordinates k t (σ g t)))

/-- The original based coordinate equivalence on the two actual carriers. -/
def basedEquiv (t : P) (u : Q) : P ≃ Q :=
  (coordinates h t).trans (coordinates k u).symm

omit [TopologicalSpace A] [IsTopologicalAddGroup A] in
theorem basedEquiv_coordinate (t : P) (u : Q) (x : P) :
    coordinates k u (basedEquiv h k t u x) = coordinates h t x :=
  (coordinates k u).apply_symm_apply _

omit [TopologicalSpace A] [IsTopologicalAddGroup A] in
/-- The complete coordinate equivalence preserves the actual translations. -/
theorem basedEquiv_vadd (t : P) (u : Q) (a : A) (x : P) :
    basedEquiv h k t u (a +ᵥ x) = a +ᵥ basedEquiv h k t u x := by
  apply (coordinates k u).injective
  rw [basedEquiv_coordinate, coordinates_vadd, coordinates_vadd, basedEquiv_coordinate]

omit [ContinuousSMul G A] in
/-- Equal original cocycles make this same coordinate equivalence equivariant. -/
theorem basedEquiv_monodromy (t : P) (u : Q)
    (he : basedCocycle h ρ haff hc t = basedCocycle k σ haff' hc' u)
    (g : G) (x : P) :
    basedEquiv h k t u (ρ g x) = σ g (basedEquiv h k t u x) := by
  apply (coordinates k u).injective
  rw [basedEquiv_coordinate, coordinates_monodromy h ρ haff,
    coordinates_monodromy k σ haff', basedEquiv_coordinate]
  exact congrArg (fun a => a + g • coordinates h t x)
    (congrArg (fun c : Cocycle G A => c.val g) he)

end EqualCocycles
end Displacement

section AffineRoundtrip

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A]

/-- Use the canonical permutation homomorphism of the existing affine action. -/
def affinePermutation (c : Cocycle G A) : G →* Equiv.Perm (AffinePoint c) :=
  MulAction.toPermHom G (AffinePoint c)

/-- Coordinates on the existing affine carrier are its literal coefficient difference. -/
theorem coordinates_affine (c : Cocycle G A) (t x : AffinePoint c) :
    coordinates (AffinePoint.unique_transport c) t x = x.val - t.val := by
  change difference (AffinePoint.unique_transport c) x t = x.val - t.val
  exact difference_eq (AffinePoint.unique_transport c) x t (x.val - t.val) (by
    apply AffinePoint.ext c
    exact sub_add_cancel x.val t.val)

/-- The same affine action has continuous original displacement at every point. -/
theorem affine_displacement_continuous (c : Cocycle G A) (t : AffinePoint c) :
    Continuous (fun g : G => coordinates (AffinePoint.unique_transport c) t
      (affinePermutation c g t)) := by
  have he (g : G) : coordinates (AffinePoint.unique_transport c) t
      (affinePermutation c g t) = c.val g + g • t.val - t.val :=
    coordinates_affine c t (g • t)
  exact ((c.continuous.add (continuous_id.smul continuous_const)).sub continuous_const).congr
    (fun g => (he g).symm)

/-- Forward displacement at the original zero point recovers exactly the input cocycle. -/
theorem basedCocycle_affine_zero (c : Cocycle G A) :
    basedCocycle (AffinePoint.unique_transport c) (affinePermutation c)
      (AffinePoint.compatible c) (affine_displacement_continuous c) (⟨0⟩ : AffinePoint c) = c := by
  apply Cocycle.ext
  intro g
  change coordinates (AffinePoint.unique_transport c) (⟨0⟩ : AffinePoint c)
    (g • (⟨0⟩ : AffinePoint c)) = c.val g
  rw [coordinates_affine, AffinePoint.displacement_zero, sub_zero]

end AffineRoundtrip
end GroupCohomology.ContinuousH1.AffineTorsors
