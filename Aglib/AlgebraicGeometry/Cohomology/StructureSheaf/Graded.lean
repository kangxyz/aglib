/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.Cup
public import Aglib.Algebra.Graded.DirectSum

/-!
# The graded algebra of original structure-sheaf cohomology

The underlying module is the native direct sum of the existing
`structureCohomology k X n`. Its ring and algebra laws are supplied by
the original Yoneda cup product, its unit, and the structural field action.
The homogeneous submodules are the ranges of the original direct-sum
inclusions. Their equivalences and decomposition use the original
coordinate maps, without a second cohomology model.

No commutativity, Künneth, or coproduct assertion is made here.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {k : Type u} [Field k] (X : FScheme k)

/-- Degree identifications do not change the original cup product. -/
theorem structureCup_heq {p q n m : ℕ} (h : p + q = n) (h' : p + q = m)
    (x : structureCohomology k X p) (y : structureCohomology k X q) :
    HEq (structureCup X h x y) (structureCup X h' x y) := by
  subst n
  subst m
  rfl

/-- The native homogeneous unit is the original cup unit. -/
instance structureCohomologyGOne : GradedMonoid.GOne (structureCohomology k X) where
  one := structureCupUnit X

/-- Native homogeneous multiplication is the original cup product. -/
instance structureCohomologyGMul : GradedMonoid.GMul (structureCohomology k X) where
  mul {i j} x y := structureCup X (p := i) (q := j) rfl x y

/-- The unit and multiplication share the same native graded monoid. -/
instance structureCohomologyGMonoid : GradedMonoid.GMonoid (structureCohomology k X) where
  toGOne := structureCohomologyGOne X
  toGMul := structureCohomologyGMul X
  one_mul := by
    rintro ⟨n, x⟩
    apply Sigma.ext (Nat.zero_add n)
    exact (structureCup_heq X (p := 0) (q := n) rfl (Nat.zero_add n)
      (structureCupUnit X) x).trans
      (heq_of_eq (structureCup_unit_left X x))
  mul_one := by
    rintro ⟨n, x⟩
    apply Sigma.ext (Nat.add_zero n)
    exact (structureCup_heq X (p := n) (q := 0) rfl (Nat.add_zero n)
      x (structureCupUnit X)).trans
      (heq_of_eq (structureCup_unit_right X x))
  mul_assoc := by
    rintro ⟨p, x⟩ ⟨q, y⟩ ⟨r, z⟩
    apply Sigma.ext (Nat.add_assoc p q r)
    exact (heq_of_eq (structureCup_assoc X (p := p) (q := q) (r := r)
      rfl rfl rfl x y z)).trans
      (structureCup_heq X (p := p) (q := q + r) _ rfl x
        (structureCup X (p := q) (q := r) rfl y z))

/-- Additivity of the original cup product gives the native graded semiring. -/
instance structureCohomologyGSemiring : DirectSum.GSemiring (structureCohomology k X) where
  toGMonoid := structureCohomologyGMonoid X
  mul_zero := by
    intro p q x
    exact (structureCup X (p := p) (q := q) rfl x).map_zero
  zero_mul := by
    intro p q y
    exact LinearMap.map_zero₂ (structureCup X (p := p) (q := q) rfl) y
  mul_add := by
    intro p q x y z
    exact (structureCup X (p := p) (q := q) rfl x).map_add y z
  add_mul := by
    intro p q x y z
    exact LinearMap.map_add₂ (structureCup X (p := p) (q := q) rfl) x y z
  natCast n := n • structureCupUnit X
  natCast_zero := zero_nsmul _
  natCast_succ n := by
    change (n + 1) • structureCupUnit X = n • structureCupUnit X + structureCupUnit X
    simp only [add_nsmul, one_nsmul]

/-- The original cup product supplies the native externally graded ring. -/
instance structureCohomologyGRing : DirectSum.GRing (structureCohomology k X) where
  toGSemiring := structureCohomologyGSemiring X
  intCast n := n • structureCupUnit X
  intCast_ofNat n := by
    change (n : ℤ) • structureCupUnit X = n • structureCupUnit X
    simp
  intCast_negSucc_ofNat n := negSucc_zsmul _ n

/-- The existing structural field action is the scalar action of the
native graded algebra, through the shared constructor and actual cup bilinearity. -/
instance structureCohomologyGAlgebra : DirectSum.GAlgebra k (structureCohomology k X) :=
  DirectSum.gAlgebraOfBilinear (R := k) (structureCohomology k X)
    (fun {p q} a x y => LinearMap.map_smul₂
      (structureCup X (p := p) (q := q) rfl) a x y)
    (fun {p q} a x y =>
      (structureCup X (p := p) (q := q) rfl x).map_smul a y)

/-- The graded algebra whose pieces are the original coherent-cohomology
objects with their original structural field action. -/
abbrev structureCohomologyAlgebra : Type (u + 1) :=
  DirectSum ℕ (structureCohomology k X)

/-- The actual inclusion of a homogeneous cohomology class. -/
abbrev structureCohomologyInclusion (n : ℕ) :=
  DirectSum.homogeneousInclusion (R := k) (structureCohomology k X) n

/-- The actual degree projection to the original cohomology object. -/
abbrev structureCohomologyComponent (n : ℕ) :=
  DirectSum.homogeneousComponent (R := k) (structureCohomology k X) n

theorem structureCohomologyComponent_inclusion (n : ℕ) (x : structureCohomology k X n) :
    structureCohomologyComponent X n (structureCohomologyInclusion X n x) = x :=
  DirectSum.homogeneousComponent_inclusion (R := k) (structureCohomology k X) n x

/-- Multiplication of homogeneous inclusions is precisely the original
cup product, with the original degree sum. -/
theorem structureCohomologyInclusion_mul {p q : ℕ}
    (x : structureCohomology k X p) (y : structureCohomology k X q) :
    structureCohomologyInclusion X p x * structureCohomologyInclusion X q y =
      structureCohomologyInclusion X (p + q) (structureCup X (p := p) (q := q) rfl x y) :=
  DirectSum.homogeneousInclusion_mul (R := k) (structureCohomology k X) x y

/-- Canonical homogeneous submodules of the actual direct-sum algebra. -/
abbrev structureCohomologyGrade :=
  DirectSum.summandSubmodule (R := k) (structureCohomology k X)

/-- The canonical homogeneous submodule uses the original inclusion and
coordinate projection, through the shared native constructor. -/
abbrev structureCohomologyGradeEquiv :=
  DirectSum.summandLinearEquiv (R := k) (structureCohomology k X)

@[simp]
theorem structureCohomologyGradeEquiv_apply (n : ℕ) (x : structureCohomology k X n) :
    (structureCohomologyGradeEquiv X n x : structureCohomologyAlgebra X) =
      structureCohomologyInclusion X n x :=
  DirectSum.summandLinearEquiv_apply (R := k) (structureCohomology k X) n x

theorem structureCohomologyGradeEquiv_symm_apply (n : ℕ)
    (x : structureCohomologyGrade X n) :
    (structureCohomologyGradeEquiv X n).symm x =
      structureCohomologyComponent X n (x : structureCohomologyAlgebra X) :=
  DirectSum.summandLinearEquiv_symm_apply (R := k) (structureCohomology k X) n x

/-- The canonical homogeneous decomposition reuses the same direct-sum
constructor and original component maps. -/
abbrev structureCohomologyDecomposition :=
  DirectSum.decomposeIntoSummands (R := k) (structureCohomology k X)

/-- Recomposing the canonical homogeneous pieces is the identity. -/
theorem coe_structureCohomologyDecomposition :
    DirectSum.coeLinearMap (structureCohomologyGrade X) ∘ₗ
      (structureCohomologyDecomposition X).toLinearMap = LinearMap.id :=
  DirectSum.coeLinearMap_decomposeIntoSummands (R := k) (structureCohomology k X)

/-- The native internal grading comes from the shared constructor. -/
instance structureCohomologyGradedAlgebra : GradedAlgebra (structureCohomologyGrade X) :=
  DirectSum.summandGradedAlgebra (R := k) (structureCohomology k X)

/-- The internal grading projection is the original component followed
by its original direct-sum inclusion. -/
theorem structureCohomology_proj (n : ℕ) (x : structureCohomologyAlgebra X) :
    GradedAlgebra.proj (structureCohomologyGrade X) n x =
      structureCohomologyInclusion X n (structureCohomologyComponent X n x) :=
  DirectSum.proj_summandSubmodule (R := k) (structureCohomology k X) n x

end AlgebraicGeometry.Scheme.Cohomology
