/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.NormalizedPointBlowupChain

/-!
# Composition of literal normalized closed-point blowup chains

The resulting chain is indexed by the original composite of scheme arrows.
Every centre and every actual normalization step is retained.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Blowup.NormalizedPointBlowupChain

universe u

/-- Concatenate literal normalized-point chains on their original composite
map. This operation neither supplies nor assumes existence of a resolving
chain; it only combines chains already constructed by the geometric proof. -/
def comp {X Y Z : Scheme.{u}} {f : Y ⟶ X} {g : Z ⟶ Y}
    (c : NormalizedPointBlowupChain f) (d : NormalizedPointBlowupChain g) :
    NormalizedPointBlowupChain (g ≫ f) := by
  induction c generalizing Z with
  | refl X => simpa only [Category.comp_id] using d
  | @cons X Y hX x hx hne f tail ih =>
    simpa only [Category.assoc] using
      NormalizedPointBlowupChain.cons x hx hne (g ≫ f) (ih d)

private theorem length_cast {X Y : Scheme.{u}} {f g : Y ⟶ X}
    (h : f = g) (e : NormalizedPointBlowupChain f = NormalizedPointBlowupChain g)
    (c : NormalizedPointBlowupChain f) : (cast e c).length = c.length := by
  subst g
  rfl

/-- Concatenation has exactly the sum of the two prescribed chain lengths. -/
theorem length_comp {X Y Z : Scheme.{u}} {f : Y ⟶ X} {g : Z ⟶ Y}
    (c : NormalizedPointBlowupChain f) (d : NormalizedPointBlowupChain g) :
    (c.comp d).length = c.length + d.length := by
  induction c generalizing Z with
  | refl X =>
    simp only [comp, eq_mpr_eq_cast]
    rw [length_cast (Category.comp_id g).symm]
    simp only [length, Nat.zero_add]
  | @cons X Y hX x hx hne f tail ih =>
    simp only [comp, eq_mp_eq_cast]
    rw [length_cast (Category.assoc g f (normalizedPointBlowupMap X x hx hne))]
    change (tail.comp d).length + 1 = (tail.length + 1) + d.length
    rw [ih]
    omega

end AlgebraicGeometry.Scheme.Blowup.NormalizedPointBlowupChain
