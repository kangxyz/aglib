/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.GradedCohomology
public import Aglib.RingTheory.ReesAlgebra.GradedTransition

/-!
# Original cohomology transitions for a compatible geometric Rees action

This interface assumes only the action comparison on each original homogeneous
summand. It constructs no Rees action and assumes no finiteness or stabilization.
The geometric Rees comparison supplies the action and its comparison equation.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory DirectSum
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable (X : Scheme.{u}) {A : Type u} [CommRing A]
variable (α : A →+* Γ(X, ⊤)) (F : X.Modules) (I : Ideal A) (p : ℕ)
variable [Module (reesAlgebra I) (idealPowerCohomologyTotal X α F I p)]

/-- The explicit normalization required of the single geometric Rees action. -/
def IdealPowerCohomologyActionCompatible : Prop :=
  ∀ (r n : ℕ) (a : ↥(I ^ r)) (x : idealPowerCohomology X α F I p n),
    (reesAlgebra.homogeneous I r a : reesAlgebra I) •
        DirectSum.lof A ℕ (fun n => ↥(idealPowerCohomology X α F I p n)) n x =
      DirectSum.lof A ℕ (fun n => ↥(idealPowerCohomology X α F I p n)) (r + n)
        (moduleCohomologyMapOfHom X α (idealPowerMul X α F I r n a) p x)

variable (hact : IdealPowerCohomologyActionCompatible X α F I p)

include hact in
/-- The original homogeneous action equation in the native grading subtype. -/
theorem idealPowerCohomology_homogeneous_lof (r n : ℕ) (a : reesAlgebra.grading I r)
    (x : idealPowerCohomology X α F I p n) :
    (a : reesAlgebra I) • DirectSum.lof A ℕ (fun n => ↥(idealPowerCohomology X α F I p n)) n x =
      DirectSum.lof A ℕ (fun n => ↥(idealPowerCohomology X α F I p n)) (r + n)
        (moduleCohomologyMapOfHom X α
          (idealPowerMul X α F I r n ⟨((a : reesAlgebra I) : Polynomial A).coeff r,
            (a : reesAlgebra I).property r⟩) p x) := by
  have ha : (a : reesAlgebra I) = reesAlgebra.homogeneous I r
      ⟨((a : reesAlgebra I) : Polynomial A).coeff r, (a : reesAlgebra I).property r⟩ := by
    apply Subtype.ext
    exact reesAlgebra.eq_monomial_coeff a.property
  conv_lhs => rw [ha]
  exact hact r n _ x

include hact in
/-- The actual geometric action preserves the canonical internal homogeneous components. -/
theorem idealPowerCohomology_gradedSMul :
    SetLike.GradedSMul (reesAlgebra.grading I) (idealPowerCohomologyComponent X α F I p) where
  smul_mem := by
    intro r n a x ha hx
    obtain ⟨y, rfl⟩ := hx
    rw [idealPowerCohomology_homogeneous_lof X α F I p hact r n ⟨a, ha⟩ y]
    exact LinearMap.mem_range_self _ _

omit [Module (reesAlgebra I) (idealPowerCohomologyTotal X α F I p)] in
/-- The original internal transition applied to an original cohomology class. -/
theorem idealPowerCohomologyComponentMap_equiv {n m : ℕ} (h : m ≤ n)
    (x : idealPowerCohomology X α F I p n) :
    idealPowerCohomologyComponentMap X α F I p h
        (idealPowerCohomologyComponentEquiv X α F I p n x) =
      idealPowerCohomologyComponentEquiv X α F I p m
        (moduleCohomologyMapOfHom X α (idealPowerMap X α F I h) p x) := by
  simp only [idealPowerCohomologyComponentMap, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]
  rfl

/-- Internal homogeneous multiplication is precisely original coefficient multiplication on `H`. -/
theorem idealPowerCohomologyComponentEquiv_homogeneous (r n : ℕ)
    (a : reesAlgebra.grading I r) (x : idealPowerCohomology X α F I p n) :
    letI := idealPowerCohomology_gradedSMul X α F I p hact
    GradedModule.homogeneousSMul (reesAlgebra.grading I)
        (idealPowerCohomologyComponent X α F I p) a
        (idealPowerCohomologyComponentEquiv X α F I p n x) =
      idealPowerCohomologyComponentEquiv X α F I p (r + n)
        (moduleCohomologyMapOfHom X α
          (idealPowerMul X α F I r n ⟨((a : reesAlgebra I) : Polynomial A).coeff r,
            (a : reesAlgebra I).property r⟩) p x) := by
  apply Subtype.ext
  exact idealPowerCohomology_homogeneous_lof X α F I p hact r n a x

/-- The genuine original cohomology transitions satisfy both Rees compatibility laws. -/
def idealPowerCohomologyGradedTransition :
    letI := idealPowerCohomology_gradedSMul X α F I p hact
    reesAlgebra.GradedTransition I (idealPowerCohomologyComponent X α F I p) := by
  letI := idealPowerCohomology_gradedSMul X α F I p hact
  let H := moduleCohomologyFunctorOfHom X α p
  refine {
    map := fun h => idealPowerCohomologyComponentMap X α F I p h
    map_self := ?_
    map_comp := ?_
    map_mul := ?_
    map_mul_scalar := ?_ }
  · intro n x
    obtain ⟨x, rfl⟩ := (idealPowerCohomologyComponentEquiv X α F I p n).surjective x
    rw [idealPowerCohomologyComponentMap_equiv]
    congr 1
    have h := idealMultipleMap_refl X α F (I ^ n)
    change H.map (idealMultipleMap X α F (le_refl (I ^ n))) x = x
    rw [h, H.map_id]
    rfl
  · intro l m n hlm hmn x
    obtain ⟨x, rfl⟩ := (idealPowerCohomologyComponentEquiv X α F I p n).surjective x
    rw [idealPowerCohomologyComponentMap_equiv, idealPowerCohomologyComponentMap_equiv,
      idealPowerCohomologyComponentMap_equiv]
    congr 1
    change H.map _ (H.map _ x) = H.map _ x
    rw [← ModuleCat.comp_apply, ← H.map_comp, idealMultipleMap_comp]
  · intro r n m h a x
    obtain ⟨x, rfl⟩ := (idealPowerCohomologyComponentEquiv X α F I p n).surjective x
    rw [idealPowerCohomologyComponentEquiv_homogeneous X α F I p hact,
      idealPowerCohomologyComponentMap_equiv, idealPowerCohomologyComponentMap_equiv,
      idealPowerCohomologyComponentEquiv_homogeneous X α F I p hact]
    congr 1
    change H.map _ (H.map _ x) = H.map _ (H.map _ x)
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← H.map_comp, ← H.map_comp]
    congr 2
    apply congrArg H.map
    exact (idealMultipleMul_naturality X α F (Ideal.pow_le_pow_right h)
      (Ideal.pow_le_pow_right (Nat.add_le_add_left h r)) _ _ _).symm
  · intro r n a x
    obtain ⟨x, rfl⟩ := (idealPowerCohomologyComponentEquiv X α F I p n).surjective x
    rw [idealPowerCohomologyComponentEquiv_homogeneous X α F I p hact,
      idealPowerCohomologyComponentMap_equiv, idealPowerCohomology_mul_transition,
      _root_.map_smul]

end AlgebraicGeometry.Scheme.Cohomology
