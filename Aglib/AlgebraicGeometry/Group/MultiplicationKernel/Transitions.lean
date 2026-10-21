/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.MultiplicationKernel.MonodromyQuotient

/-!
# Literal multiplication-cover transitions and quotient compatibility

The map from level `d*e` to level `d` is the actual multiplication-by-`e`
morphism on the same group scheme. On actual torsion points it is `e • t`.
Its naturality square identifies the two geometric-kernel quotients. For an
arbitrary divisor `d ∣ n`, the same formula uses `n/d`; the final quotient
lowering theorem retains `0 < d`, exactly as in the source. Finite etaleness
is an explicit hypothesis at both displayed levels, with no degree assertion.

Source: `R5Lab.AlgebraicGeometry.EllipticCurve.Torsion.MonodromyTransitions`,
lines 44–83 and 106–121, packet SHA-256
`a52a08afbb28fb5c54f19ddf4f769508430da72afc801fbe58581986b79b71a9`.
The point-map formulas are unfolded directly; they introduce no coefficient
map, character inflation or new theorem-family premise. Current consumer:
`AglibTest.MultiplicationKernelGeometry` and downstream finite-level systems.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.EtaleFundamentalGroups
open AlgebraicGeometry.Scheme.Group.MultiplicationKernel
open AlgebraicGeometry.Scheme.OverField (Base FScheme)

namespace AlgebraicGeometry.Scheme.Group.MultiplicationKernel.MonodromyQuotient.Transitions
universe u
attribute [local instance] Over.cartesianMonoidalCategory

variable {F : Type u} [Field F] (E : Grp (FScheme F)) [IsCommMonObj E.X]

/-- Literal multiplication-by-e on the actual (d*e)-torsion point subgroup. -/
def torsionReduction (d e : ℕ) : finiteTorsionPoints E (d * e) →+ finiteTorsionPoints E d where
  toFun x := ⟨e • x.val, by
    change d • (e • x.val) = 0
    rw [← mul_smul]
    exact torsion_killed E (d * e) x⟩
  map_zero' := by apply Subtype.ext; exact smul_zero e
  map_add' x y := by apply Subtype.ext; exact smul_add e x.val y.val

/-- The actual lowering map for a divisor, including all zero cases allowed by divisibility. -/
def torsionLowering (d n : ℕ) (h : d ∣ n) :
    finiteTorsionPoints E n →+ finiteTorsionPoints E d where
  toFun x := ⟨(n / d) • x.val, by
    change d • ((n / d) • x.val) = 0
    rw [← mul_smul, Nat.mul_div_cancel' h]
    exact torsion_killed E n x⟩
  map_zero' := by apply Subtype.ext; exact smul_zero _
  map_add' x y := by apply Subtype.ext; exact smul_add _ x.val y.val

section ProductLevels
variable {F : Type u} [Field F] (E : Grp (FScheme F)) [IsCommMonObj E.X] (d e : ℕ)

omit [IsCommMonObj E.X] in
theorem multiplication_comp :
    multiplication E e ≫ multiplication E d = multiplication E (d * e) := by
  simp only [multiplication, MonObj.comp_pow, Category.comp_id, ← pow_mul]
  rw [Nat.mul_comm e d]

variable [IsFinite (multiplication E d).left] [Etale (multiplication E d).left]
  [IsFinite (multiplication E (d * e)).left] [Etale (multiplication E (d * e)).left]

/-- The literal multiplication-by-e map between the two multiplication covers. -/
def reductionCoverMap : multiplicationCover E (d * e) ⟶ multiplicationCover E d :=
  ObjectProperty.homMk (Over.homMk (multiplication E e).left
    (congrArg Over.Hom.left (multiplication_comp E d e)))

/-- Its fibre operation is exactly the existing native torsion reduction. -/
theorem reductionCoverMap_fiber (t : finiteTorsionPoints E (d * e)) :
    fiberEquiv E (d * e) t ≫ (reductionCoverMap E d e).hom =
      fiberEquiv E d (torsionReduction E d e t) := by
  apply Over.OverMorphism.ext
  change t.val.toMul.left ≫ (multiplication E e).left = (t.val.toMul ^ e).left
  exact congrArg (fun q : Over.mk (b (F := F)) ⟶ E.X => q.left)
    (point_multiplication E e t.val.toMul)

theorem reductionCoverMap_zero :
    fiberEquiv E (d * e) 0 ≫ (reductionCoverMap E d e).hom = fiberEquiv E d 0 := by
  rw [reductionCoverMap_fiber, map_zero]

/-- Native multiplication monodromy commutes with the literal finite-level map. -/
theorem quotientMap_reduction (g : N E) :
    torsionReduction E d e (quotientMap E (d * e) g) =
      quotientMap E d g := by
  apply (fiberEquiv E d).injective
  rw [← reductionCoverMap_fiber]
  simp only [quotientMap, Equiv.apply_symm_apply]
  have h := FiberTorsorActions.evaluation_naturality (x0 E) g.val
    (reductionCoverMap E d e).hom (fiberEquiv E (d * e) 0)
  rw [reductionCoverMap_zero] at h
  exact h.symm

end ProductLevels

section DivisibilityLevels
variable {F : Type u} [Field F] (E : Grp (FScheme F)) [IsCommMonObj E.X] (d n : ℕ)
  [IsFinite (multiplication E d).left] [Etale (multiplication E d).left]
  [IsFinite (multiplication E n).left] [Etale (multiplication E n).left]

/-- The native lowering map for arbitrary divisibility has the same monodromy square. -/
theorem quotientMap_lowering (hd : 0 < d) (h : d ∣ n) (g : N E) :
    torsionLowering E d n h (quotientMap E n g) =
      quotientMap E d g := by
  obtain ⟨e, rfl⟩ := h
  have hl : torsionLowering E d (d * e) (dvd_mul_right d e) =
      torsionReduction E d e := by
    apply AddMonoidHom.ext
    intro t
    apply Subtype.ext
    change ((d * e) / d) • t.val = e • t.val
    rw [Nat.mul_div_cancel_left e hd]
  rw [hl]
  exact quotientMap_reduction E d e g

end DivisibilityLevels

end AlgebraicGeometry.Scheme.Group.MultiplicationKernel.MonodromyQuotient.Transitions
