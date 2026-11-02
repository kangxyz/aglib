/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.PointBlowupChain
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic

/-!
# Normal actual stages of an ordinary point-blowup chain

This predicate refers only to the post-blowup schemes already present in the
native chain. It neither replaces the chain nor requires its original base
to be normal. Concatenation uses the existing original composite.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Blowup.PointBlowupChain

/-- Every actual post-blowup scheme in the given ordinary chain is normal.
There is no condition on the original base of the empty chain. -/
def NormalStages : {T X : Scheme.{u}} → {g : T ⟶ X} → PointBlowupChain g → Prop
  | _, _, _, .refl _ => True
  | _, _, _, @PointBlowupChain.cons X _ x _ _ _ tail =>
      NormalStalks (blowupDatum (X.fromSpecResidueField x).ker).Y ∧ tail.NormalStages

@[simp]
theorem normalStages_refl (X : Scheme.{u}) : (PointBlowupChain.refl X).NormalStages :=
  True.intro

@[simp]
theorem normalStages_cons {X T : Scheme.{u}} (x : X)
    (hx : IsClosed ({x} : Set X)) (hd : ringKrullDim (X.presheaf.stalk x) = 2)
    (g : T ⟶ (blowupDatum (X.fromSpecResidueField x).ker).Y)
    (tail : PointBlowupChain g) :
    (PointBlowupChain.cons x hx hd g tail).NormalStages ↔
      NormalStalks (blowupDatum (X.fromSpecResidueField x).ker).Y ∧ tail.NormalStages :=
  Iff.rfl

private theorem normalStages_cast {X T : Scheme.{u}} {f g : T ⟶ X}
    (h : f = g) (e : PointBlowupChain f = PointBlowupChain g)
    (c : PointBlowupChain f) : (cast e c).NormalStages ↔ c.NormalStages := by
  subst g
  rfl

/-- Genuine normal-stage data is retained by the existing concatenation of
ordinary point chains, indexed by the original composite morphism. -/
theorem NormalStages.comp {X Y Z : Scheme.{u}} {f : Y ⟶ X} {g : Z ⟶ Y}
    {c : PointBlowupChain f} {d : PointBlowupChain g} :
    c.NormalStages → d.NormalStages → (c.comp d).NormalStages := by
  induction c generalizing Z with
  | refl X =>
    intro _ hd
    simp only [PointBlowupChain.comp, eq_mpr_eq_cast]
    rw [normalStages_cast (Category.comp_id g).symm]
    exact hd
  | @cons X Y x hx hd f tail ih =>
    intro hc hnormal
    simp only [PointBlowupChain.comp, eq_mp_eq_cast]
    rw [normalStages_cast (Category.assoc g f (blowupDatum (X.fromSpecResidueField x).ker).map)]
    exact ⟨hc.1, ih hc.2 hnormal⟩

end AlgebraicGeometry.Scheme.Blowup.PointBlowupChain
