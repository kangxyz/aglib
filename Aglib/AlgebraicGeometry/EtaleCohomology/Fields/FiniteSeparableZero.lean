/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FinitePureZeroDetection
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-! # The separable part of an actual finite field zero stage

A class killed over a finite field extension is already killed over its
literal maximal separable subextension. Only the existing finite-pure
comparison is used. No normalization-finiteness assumption is added.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite

universe u eX eE eF

attribute [local instance] hasSheafifyLarge

/-- The original zero restriction descends to the actual finite separable
subextension, without changing the original class or scheme. -/
theorem finiteField_zero_at_separableClosure
    (k F : Type u) [Field k] [Field F] [Algebra k F] [Module.Finite k F]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{eE} (AbelianSheaf.{u, u + 1}
      (pullback p (Spec.algebraMap k (separableClosure k F))))]
    [HasExt.{eF} (AbelianSheaf.{u, u + 1} (pullback p (Spec.algebraMap k F)))]
    (A : Type u) [AddCommGroup A] [Finite A] (q : ℕ)
    (c : Sheaf.H.{eX} (coefficient A X) q)
    (hc : Curves.constantRestriction.{u, eX, eF} A
      (pullback.fst p (Spec.algebraMap k F)) q c = 0) :
    Curves.constantRestriction.{u, eX, eE} A
      (pullback.fst p (Spec.algebraMap k (separableClosure k F))) q c = 0 := by
  let E := separableClosure k F
  let b := Spec.algebraMap k E
  let d := Spec.algebraMap E F
  let a := Spec.algebraMap k F
  have hd : d ≫ b = a := by
    rw [← Spec.map_comp]
    congr 1
  let P : Scheme.{u} := pullback (pullback.snd p b) d
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} P) := HasExt.standard _
  let v : P ⟶ pullback p a :=
    pullback.lift (pullback.fst (pullback.snd p b) d ≫ pullback.fst p b)
      (pullback.snd (pullback.snd p b) d) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc,
          pullback.condition, Category.assoc, hd])
  have hv : v ≫ pullback.fst p a =
      pullback.fst (pullback.snd p b) d ≫ pullback.fst p b := pullback.lift_fst _ _ _
  have hz : Curves.constantRestriction.{u, eX, u + 2} A
      (pullback.fst (pullback.snd p b) d ≫ pullback.fst p b) q c = 0 := by
    rw [← hv, Curves.constantRestriction_comp, hc, map_zero]
  exact constantRestriction_eq_zero_of_finitePure E F
    (pullback.snd p b) (pullback.fst p b) A q c hz

end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite
