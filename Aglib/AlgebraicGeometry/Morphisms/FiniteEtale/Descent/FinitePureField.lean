/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalFinitePureDescent

/-! # Actual finite etale cover descent along a finite purely inseparable field map

This is an identity-pullback adapter to the existing global equivalence, not a
second invariance proof. The output comparison uses the literal field spectrum
map and the original supplied finite etale cover.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable

universe u

/-- Descend an actual cover of the literal field spectrum, retaining an actual
isomorphism after the original field-map base change. -/
def fieldCoverDescent (K L : Type u) [Field K] [Field L] [Algebra K L]
    [IsPurelyInseparable K L] [Module.Finite K L]
    (V : Scheme.FiniteEtale (Spec (.of L))) :
    Σ U : Scheme.FiniteEtale (Spec (.of K)),
      (baseChange (Spec.algebraMap K L)).obj U ≅ V := by
  let k := Spec.algebraMap K L
  let p := pullback.fst (𝟙 (Spec (.of K))) k
  let q := pullback.snd (𝟙 (Spec (.of K))) k
  have : IsIso q := inferInstanceAs (IsIso (pullback.snd (𝟙 (Spec (.of K))) k))
  let E := Global.finitePureCoverEquivalence K L (𝟙 (Spec (.of K)))
  let VP := (baseChange q).obj V
  let U := E.inverse.obj VP
  have e : (baseChange p).obj U ≅ VP := E.counitIso.app VP
  have hp : inv q ≫ p = k := by
    have h : p = q ≫ k := by
      simpa only [Category.comp_id] using
        (pullback.condition (f := 𝟙 (Spec (.of K))) (g := k))
    rw [h, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  let eL : (baseChange k).obj U ≅ (baseChange (inv q)).obj ((baseChange p).obj U) :=
    eqToIso (congrArg (fun h => (baseChange h).obj U) hp.symm) ≪≫
      (baseChangeComp p (inv q)).app U
  let eR : (baseChange (inv q)).obj ((baseChange q).obj V) ≅ V :=
    ((baseChangeComp q (inv q)).app V).symm ≪≫
      eqToIso (congrArg (fun h => (baseChange h).obj V) (IsIso.inv_hom_id q)) ≪≫
      (baseChangeId _).app V
  exact ⟨U, eL ≪≫ (baseChange (inv q)).mapIso e ≪≫ eR⟩

end AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable
