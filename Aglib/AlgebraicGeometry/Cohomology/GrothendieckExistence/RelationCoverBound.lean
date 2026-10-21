/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationAffineBound
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.RelationDiagramProperties
public import Aglib.LinearAlgebra.KernelIdealBound

/-! # A common original relation-kernel cutoff on any finite affine cover -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Coherent
open AlgebraicGeometry.Scheme.Modules.Coherent.AdicSystem
namespace AlgebraicGeometry.Scheme.Cohomology
universe u v
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  {X : Scheme.{u}} [IsLocallyNoetherian X]
  (f : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType f] (I : Ideal A)
  {P F : AdicSystem X (idealThickeningIdealSheaf f I)} (φ : P ⟶ F)

omit [IsNoetherianRing A] [LocallyOfFiniteType f] in
/-- Raising the fixed target level only shrinks the original reduction kernel. -/
theorem relation_kernel_le_of_intermediate {k l m : ℕ} (h : k ≤ l) (h' : l ≤ m)
    (U : X.Opens) :
    ((relationMap φ h').val.app (op U)).hom.ker ≤
      ((relationMap φ (h.trans h')).val.app (op U)).hom.ker := by
  intro x hx
  change (relationMap φ h').app U x = 0 at hx
  change (relationMap φ (h.trans h')).app U x = 0
  have hc := congrArg (fun k => k.app U x) (relationMap_comp φ h h')
  change (relationMap φ h).app U ((relationMap φ h').app U x) = _ at hc
  rw [hx, map_zero] at hc
  exact hc.symm

/-- The maximum of finitely many actual affine cutoffs works simultaneously
on the original relation diagram. The family need not be a cover for this bound;
covering is used only by the subsequent epimorphism criterion. -/
theorem exists_relationDiagram_kernel_bound_on_finite_family
    {ι : Type v} [Finite ι] (U : ι → X.affineOpens)
    (hφ : ∀ n, Epi (φ.hom.app (op n))) :
    ∃ k : ℕ, 0 < k ∧ ∀ i m (h : k ≤ m),
      (((relationDiagram φ).map (homOfLE h).op).val.app (op (U i).1)).hom.ker ≤
        (idealThickeningIdealSheaf f I).ideal (U i) •
          (⊤ : Submodule Γ(X, (U i).1) Γ((relationDiagram φ).obj (op m), (U i).1)) := by
  classical
  let := Fintype.ofFinite ι
  choose c hc using fun i => exists_relation_kernel_bound_on_affine f I φ (U i) hφ
  let k := max 1 (Finset.univ.sup fun i => c i + 1)
  have hck (i : ι) : c i + 1 ≤ k :=
    (Finset.le_sup (f := fun i => c i + 1) (Finset.mem_univ i)).trans (le_max_right _ _)
  refine ⟨k, lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _), fun i m h => ?_⟩
  have hb := (relation_kernel_le_of_intermediate f I φ (hck i) h (U i).1).trans
    (hc i m ((hck i).trans h))
  let e : Γ((relationDiagram φ).obj (op m), (U i).1) ≃ₗ[Γ(X, (U i).1)]
      Γ(relation φ m, (U i).1) := ((SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)).mapIso
    (relationDiagramObjIso φ m)).toLinearEquiv
  let d : Γ((relationDiagram φ).obj (op k), (U i).1) ≃ₗ[Γ(X, (U i).1)]
      Γ(relation φ k, (U i).1) := ((SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)).mapIso
    (relationDiagramObjIso φ k)).toLinearEquiv
  apply LinearMap.ker_le_smul_top_of_equiv (R := Γ(X, (U i).1)) _ _ _ e d _ hb
  intro x
  exact congrArg (fun q => q.app (U i).1 x) (relationDiagramObjIso_naturality φ h)

end AlgebraicGeometry.Scheme.Cohomology
