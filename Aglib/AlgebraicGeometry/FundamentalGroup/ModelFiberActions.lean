/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.KernelFiniteStage

/-!
# Comparing fibre actions on two actual descended models

The comparison uses a common pointed stage and an actual descended arrow,
with its actual pullback square. It makes the two-model choice-independence
obligation explicit without postulating geometric exactness.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberToFinite)
open AlgebraicGeometry.Scheme.EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel.ModelActions

universe u
variable {K : Type u} [Field K] {G R S T : PointedScheme K}

/-- Transport the action of `a` on the fibre of `A` through `pointedFiberEquiv f A`
to the fibre of its pullback at `G.hom`. -/
def action (f : G ⟶ S) (a : FiberAutGroup S.hom) (A : Scheme.FiniteEtale S.right)
    (z : Fiber G.hom ((baseChange f.right).obj A)) :
    Fiber G.hom ((baseChange f.right).obj A) :=
  pointedFiberEquiv f A (a.hom.app A ((pointedFiberEquiv f A).symm z))

/-- The permutation of the pulled-back fibre obtained by conjugating the component
of `a` on `A` through `pointedFiberEquiv f A`. -/
def permutation (f : G ⟶ S) (a : FiberAutGroup S.hom) (A : Scheme.FiniteEtale S.right) :
    Equiv.Perm (Fiber G.hom ((baseChange f.right).obj A)) :=
  (pointedFiberEquiv f A).symm.trans
    ((FintypeCat.equivEquivIso.symm (a.app A)).trans (pointedFiberEquiv f A))

@[simp] theorem permutation_apply (f : G ⟶ S) (a : FiberAutGroup S.hom)
  (A : Scheme.FiniteEtale S.right)
    (z : Fiber G.hom ((baseChange f.right).obj A)) :
    permutation f a A z = action f a A z := rfl

theorem pointEquiv_naturality (f : G ⟶ S) {A B : Scheme.FiniteEtale S.right} (g : A ⟶ B)
    (q : Fiber S.hom A) :
    (fiberToFinite G.hom).map ((baseChange f.right).map g) (pointedFiberEquiv f A q) =
      pointedFiberEquiv f B ((fiberToFinite S.hom).map g q) := by
  have h := ConcreteCategory.congr_hom ((pointedFiberIso f).hom.naturality g) q
  exact h.symm

theorem action_naturality (f : G ⟶ S) (a : FiberAutGroup S.hom)
    {A B : Scheme.FiniteEtale S.right} (g : A ⟶ B) (z : Fiber G.hom ((baseChange f.right).obj A)) :
    (fiberToFinite G.hom).map ((baseChange f.right).map g) (action f a A z) =
      action f a B ((fiberToFinite G.hom).map ((baseChange f.right).map g) z) := by
  obtain ⟨q, rfl⟩ := (pointedFiberEquiv f A).surjective z
  simp only [action, Equiv.symm_apply_apply, pointEquiv_naturality]
  rw [evaluate_naturality]

theorem comparison_fiber_injective (r : G ⟶ R) (v : R ⟶ S) (A : Scheme.FiniteEtale S.right) :
    Function.Injective ((fiberToFinite G.hom).map (baseChangeComparison r.right v.right A)) := by
  intro x y h
  obtain ⟨qx, rfl⟩ := (pointedFiberEquiv (r ≫ v) A).surjective x
  obtain ⟨qy, rfl⟩ := (pointedFiberEquiv (r ≫ v) A).surjective y
  rw [← pointedFiberEquiv_comp, ← pointedFiberEquiv_comp] at h
  exact congrArg (pointedFiberEquiv (r ≫ v) A)
    ((pointedFiberEquiv v A).injective ((pointedFiberEquiv r _).injective h))

/-- Refining the actual field stage transports its fibre action compatibly. -/
theorem action_refinement (r : G ⟶ R) (v : R ⟶ S) (a : FiberAutGroup R.hom)
    (A : Scheme.FiniteEtale S.right) (z : Fiber G.hom ((baseChange (r ≫ v).right).obj A)) :
    (fiberToFinite G.hom).map (baseChangeComparison r.right v.right A)
        (action (r ≫ v) (pointedMap v a) A z) =
      action r a ((baseChange v.right).obj A)
        ((fiberToFinite G.hom).map (baseChangeComparison r.right v.right A) z) := by
  obtain ⟨q, rfl⟩ := (pointedFiberEquiv (r ≫ v) A).surjective z
  simp only [action, Equiv.symm_apply_apply]
  rw [← pointedFiberEquiv_comp, ← pointedFiberEquiv_comp, Equiv.symm_apply_apply,
    pointedMap_apply, Equiv.apply_symm_apply]

/-- Two descended models give compatible actions whenever their comparison
arrow is an actual pullback from a common stage. -/
theorem action_two_models (r : G ⟶ R) (v : R ⟶ S) (w : R ⟶ T)
    (a : FiberAutGroup R.hom) (A : Scheme.FiniteEtale S.right) (B : Scheme.FiniteEtale T.right)
    (g : (baseChange v.right).obj A ⟶ (baseChange w.right).obj B)
    (γ : (baseChange (r ≫ v).right).obj A ⟶ (baseChange (r ≫ w).right).obj B)
    (hγ : baseChangeComparison r.right v.right A ≫ (baseChange r.right).map g =
      γ ≫ baseChangeComparison r.right w.right B)
    (z : Fiber G.hom ((baseChange (r ≫ v).right).obj A)) :
    (fiberToFinite G.hom).map γ (action (r ≫ v) (pointedMap v a) A z) =
      action (r ≫ w) (pointedMap w a) B ((fiberToFinite G.hom).map γ z) := by
  apply comparison_fiber_injective r w B
  have H (q : Fiber G.hom ((baseChange (r ≫ v).right).obj A)) :
      (fiberToFinite G.hom).map (baseChangeComparison r.right w.right B)
          ((fiberToFinite G.hom).map γ q) =
        (fiberToFinite G.hom).map ((baseChange r.right).map g)
          ((fiberToFinite G.hom).map (baseChangeComparison r.right v.right A) q) := by
    exact (ConcreteCategory.congr_hom (congrArg (fiberToFinite G.hom).map hγ) q).symm
  rw [H, action_refinement, action_naturality, ← H, action_refinement]

end AlgebraicGeometry.Scheme.FiniteEtale.GeometricKernel.ModelActions

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 0e5e1ef77111c8ff2359b1ed26346651c6e53cb891ac15e31cdee51d4b70bf86.
Definitions, hypotheses and universes are retained modulo native names. -/
