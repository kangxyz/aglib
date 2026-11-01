/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.CurveConstants
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Data.Fintype.EquivFin

/-! # Finite constant coefficients on proper curves

The finite abelian structure theorem supplies actual split cyclic factors.
The original coefficient maps and their split identity transfer cyclic
vanishing to every finite constant value. The final endpoint includes every
finite value in the original sheaf-value universe, without a size premise.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped BigOperators DirectSum

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u e

attribute [local instance] hasSheafifyLarge

variable {k : Type u} [Field k] [IsSepClosed k]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  (hdim : topologicalKrullDim X ≤ 1)
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]

include f hdim

/-- Every finite constant abelian coefficient on a proper curve has trivial
original cohomology above degree two. The field may be imperfect. -/
theorem constantFinite_subsingleton_H_of_proper_dimension_le_one
    (A : Type u) [AddCommGroup A] [Finite A] (q : ℕ) (hq : 2 < q) :
    Subsingleton (Sheaf.H.{e} (ConstantFinite.coefficient A X) q) := by
  classical
  obtain ⟨ι, hι, p, hp, n, ⟨d⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite A
  let := hι
  let B : ι → Type u := fun i => ULift.{u} (ZMod (p i ^ n i))
  let liftA : ULift.{u + 1} A ≃+ A := AddEquiv.ulift
  let liftB (i : ι) : ULift.{u + 1} (B i) ≃+ ZMod (p i ^ n i) :=
    AddEquiv.ulift.trans AddEquiv.ulift
  let s : ∀ i, ConstantFinite.value (B i) ⟶ ConstantFinite.value A := fun i =>
    AddCommGrpCat.ofHom (liftA.symm.toAddMonoidHom.comp
      (d.symm.toAddMonoidHom.comp
        ((DirectSum.of (fun j => ZMod (p j ^ n j)) i).comp (liftB i).toAddMonoidHom)))
  let r : ∀ i, ConstantFinite.value A ⟶ ConstantFinite.value (B i) := fun i =>
    AddCommGrpCat.ofHom ((liftB i).symm.toAddMonoidHom.comp
      ((DFinsupp.evalAddMonoidHom i).comp (d.toAddMonoidHom.comp liftA.toAddMonoidHom)))
  have hs : ∑ i, r i ≫ s i = 𝟙 _ := by
    apply AddCommGrpCat.homAddEquiv.injective
    apply AddMonoidHom.ext
    intro x
    change (AddCommGrpCat.homAddEquiv (∑ i, r i ≫ s i)) x = x
    rw [map_sum, AddMonoidHom.finsetSum_apply]
    apply liftA.injective
    rw [map_sum]
    change (∑ i, d.symm (DirectSum.of (fun j => ZMod (p j ^ n j)) i
      ((d (liftA x)) i))) = liftA x
    rw [← map_sum, DirectSum.sum_univ_of, d.symm_apply_apply]
  let C := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  have hzero (x : Sheaf.H.{e} (ConstantFinite.coefficient A X) q) : x = 0 := by
    have heval (t : Finset ι) :
        Sheaf.H.map (∑ i ∈ t, C.map (r i ≫ s i)) q x =
          ∑ i ∈ t, Sheaf.H.map (C.map (r i ≫ s i)) q x := by
      induction t using Finset.induction_on with
      | empty => simp [Sheaf.H.map_apply]
      | @insert i t hi ih =>
          rw [Finset.sum_insert hi, Finset.sum_insert hi, Sheaf.H.map_add_apply, ih]
    have hsum : ∑ i, Sheaf.H.map (C.map (r i ≫ s i)) q x = x := by
      rw [← heval Finset.univ, ← CategoryTheory.Functor.map_sum, hs,
        CategoryTheory.Functor.map_id,
        Sheaf.H.map_id_apply]
    rw [← hsum]
    apply Finset.sum_eq_zero
    intro i _
    let : Subsingleton (Sheaf.H.{e} (ConstantFinite.coefficient (B i) X) q) :=
      constantCyclic_subsingleton_H_of_proper_dimension_le_one f hdim
        (p i ^ n i) (pow_pos (hp i).pos _) q hq
    rw [CategoryTheory.Functor.map_comp, Sheaf.H.map_comp_apply,
      Subsingleton.elim (Sheaf.H.map (C.map (r i)) q x) 0, map_zero]
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

/-- Finite constant vanishing in the full original coefficient universe.
Only the finite value is resized; the scheme and original Ext universe stay fixed. -/
theorem constant_subsingleton_H_of_proper_dimension_le_one
    (A : AddCommGrpCat.{u + 1}) [Finite A] (q : ℕ) (hq : 2 < q) :
    Subsingleton (Sheaf.H.{e}
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A) q) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let e₀ : A ≃ ULift.{u} (Fin (Fintype.card A)) :=
    (Fintype.equivFin A).trans Equiv.ulift.symm
  let : Small.{u} A := Small.mk' e₀
  let : Finite (Shrink.{u} A) := Finite.of_equiv A (equivShrink A)
  let d : ConstantFinite.value (Shrink.{u} A) ≅ A :=
    (AddEquiv.ulift.trans (Shrink.addEquiv (α := A))).toAddCommGrpIso
  let : Subsingleton (Sheaf.H.{e}
      (ConstantFinite.coefficient (Shrink.{u} A) X) q) :=
    constantFinite_subsingleton_H_of_proper_dimension_le_one f hdim (Shrink.{u} A) q hq
  exact (cohomologyMapIso_bijective
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso d) q).surjective.subsingleton

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
