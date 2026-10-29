/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupCohomology.H1.Continuous
public import Aglib.GroupCohomology.H1.SplitExtension

/-! # Explicit inverse group restriction on the original continuous H1

Both directions are the supplied actual pullback maps on the existing
continuous cocycles and quotient. Their group and coefficient functions are
mutually inverse; the inverse laws are proved on those same cocycles.
The character construction uses a trivial action only on its H1 target.
-/

@[expose] public noncomputable section

namespace GroupCohomology.ContinuousH1.GroupEquivalence

universe u v w z

section InverseMaps
variable {G : Type u} {H : Type v} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  {A : Type w} {B : Type z} [AddCommGroup A] [AddCommGroup B]
  [TopologicalSpace A] [TopologicalSpace B]
  [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]
  [DistribMulAction G A] [DistribMulAction H B]
  [ContinuousSMul G A] [ContinuousSMul H B]
  (φ : ContinuousMonoidHom H G) (ψ : ContinuousMonoidHom G H)
  (hφψ : ∀ g : G, φ (ψ g) = g) (hψφ : ∀ h : H, ψ (φ h) = h)
  (q : PullbackMap (A := A) (B := B) φ) (r : PullbackMap (A := B) (B := A) ψ)
  (hrq : ∀ a : A, r (q a) = a) (hqr : ∀ b : B, q (r b) = b)

/-- The actual forward and inverse pullback maps give an equivalence on the
same continuous-H1 quotient, with independent group and coefficient worlds. -/
def ofInversePullbackMaps : H1 G A ≃+ H1 H B where
  toFun := q.onH1
  invFun := r.onH1
  left_inv x := by
    obtain ⟨c, rfl⟩ := classOf_surjective G A x
    change classOf G A (r.onCocycles (q.onCocycles c)) = classOf G A c
    congr 1
    apply Cocycle.ext
    intro g
    change r (q (c.val (φ (ψ g)))) = c.val g
    rw [hφψ, hrq]
  right_inv x := by
    obtain ⟨c, rfl⟩ := classOf_surjective H B x
    change classOf H B (q.onCocycles (r.onCocycles c)) = classOf H B c
    congr 1
    apply Cocycle.ext
    intro h
    change q (r (c.val (ψ (φ h)))) = c.val h
    rw [hψφ, hqr]
  map_add' := q.onH1.map_add

/-- The forward value is literally the class of the original pulled-back cocycle. -/
theorem ofInversePullbackMaps_classOf (c : Cocycle G A) :
    ofInversePullbackMaps φ ψ hφψ hψφ q r hrq hqr (classOf G A c) =
      classOf H B (q.onCocycles c) := rfl

/-- The inverse value is literally the class of the original inverse pullback. -/
theorem ofInversePullbackMaps_symm_classOf (c : Cocycle H B) :
    (ofInversePullbackMaps φ ψ hφψ hψφ q r hrq hqr).symm (classOf H B c) =
      classOf G A (r.onCocycles c) := rfl

end InverseMaps

section Characters
variable {G : Type u} {N : Type v} {H : Type w} {A : Type z}
  [Group G] [Group N] [Group H] [TopologicalSpace N] [TopologicalSpace H]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [MulDistribMulAction G N] [DistribMulAction G A] [DistribMulAction H A]
  (e : H ≃ₜ* N) (htriv : ∀ (h : H) (a : A), h • a = a)

/-- Pull the actual continuous character back along the supplied topological
group equivalence, with the given trivial action on the cohomology group. -/
def characterCocycle (c : PointedCohomology.EquivariantCharacter G N A) : Cocycle H A :=
  ⟨⟨fun h => c.toFun (e h), c.continuous_toFun.comp e.continuous⟩, by
    intro h k
    change c.toFun (e (h * k)) = c.toFun (e h) + h • c.toFun (e k)
    rw [map_mul, c.map_mul, htriv]⟩

@[simp] theorem characterCocycle_apply
    (c : PointedCohomology.EquivariantCharacter G N A) (h : H) :
    (characterCocycle e htriv c).val h = c.toFun (e h) := rfl

variable [ContinuousSMul H A]

/-- The character maps to the actual class of its original pulled-back cocycle. -/
def characterH1 : PointedCohomology.EquivariantCharacter G N A →+ H1 H A where
  toFun c := classOf H A (characterCocycle e htriv c)
  map_zero' := by
    change classOf H A 0 = 0
    exact map_zero _
  map_add' c d := by
    change classOf H A (characterCocycle e htriv c + characterCocycle e htriv d) = _
    exact map_add _ _ _

/-- The same named cocycle is the literal representative of the character class. -/
theorem characterH1_apply (c : PointedCohomology.EquivariantCharacter G N A) :
    characterH1 e htriv c = classOf H A (characterCocycle e htriv c) := rfl

/-- For the given trivial action a principal cocycle is zero. Surjectivity of
the actual group equivalence then detects equality of the original characters. -/
theorem characterH1_injective : Function.Injective (characterH1 (G := G) e htriv) := by
  intro c d hcd
  obtain ⟨a, ha⟩ := (classOf_eq_iff H A _ _).mp hcd
  apply PointedCohomology.EquivariantCharacter.ext
  intro k
  obtain ⟨h, rfl⟩ := e.surjective k
  have hh := congrArg (fun z : Cocycle H A => z.val h) ha
  change h • a - a = c.toFun (e h) - d.toFun (e h) at hh
  rw [htriv, sub_self] at hh
  exact sub_eq_zero.mp hh.symm

end Characters
end GroupCohomology.ContinuousH1.GroupEquivalence
