/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Restriction of scheme intersections to open charts

Relocated unchanged declarations from R5 revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`; original namespaces and explicit
source and hypothesis boundaries are retained.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Limits.OpenIntersection` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`12be3b790a97e9b3259d10fd29ee198cb82a63078a304b3067820f0e24ccbdf6`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
universe u

section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.OpenIntersectionRestriction
variable {X U C D CU DU : Scheme.{u}}
  (u : U ⟶ X) [IsOpenImmersion u] (c : C ⟶ X) (d : D ⟶ X)
  (a : CU ⟶ U) (b : DU ⟶ U) (cu : CU ⟶ C) (du : DU ⟶ D)
  (hc : IsPullback a cu u c) (hd : IsPullback b du u d)
  (h : Set.range (pullback.fst c d ≫ c) ⊆ Set.range u)

/-- The entire actual intersection factors through the open chart when its
image lies there. This is a scheme morphism from the open immersion property. -/
def toOpen : pullback c d ⟶ U := IsOpenImmersion.lift u (pullback.fst c d ≫ c) h

@[reassoc (attr := simp)] theorem toOpen_comp :
    toOpen u c d h ≫ u = pullback.fst c d ≫ c := IsOpenImmersion.lift_fac _ _ _

/-- The component-side factor, obtained from its actual cartesian square. -/
def toLeft : pullback c d ⟶ CU :=
  pullback.lift (toOpen u c d h) (pullback.fst c d) (toOpen_comp u c d h) ≫
    hc.isoPullback.inv

/-- The complementary-side factor, obtained from its actual cartesian square. -/
def toRight : pullback c d ⟶ DU :=
  pullback.lift (toOpen u c d h) (pullback.snd c d)
    ((toOpen_comp u c d h).trans pullback.condition) ≫ hd.isoPullback.inv

@[reassoc (attr := simp)] theorem toLeft_chart :
    toLeft u c d a cu hc h ≫ cu = pullback.fst c d := by
  simp [toLeft]

@[reassoc (attr := simp)] theorem toRight_chart :
    toRight u c d b du hd h ≫ du = pullback.snd c d := by
  simp [toRight]

@[reassoc (attr := simp)] theorem toLeft_open :
    toLeft u c d a cu hc h ≫ a = toOpen u c d h := by
  simp [toLeft]

@[reassoc (attr := simp)] theorem toRight_open :
    toRight u c d b du hd h ≫ b = toOpen u c d h := by
  simp [toRight]

/-- The actual whole intersection maps to its chart restriction. -/
def toRestricted : pullback c d ⟶ pullback a b :=
  pullback.lift (toLeft u c d a cu hc h) (toRight u c d b du hd h) (by simp)

/-- The inverse is the canonical map of the actual pullbacks. -/
def fromRestricted : pullback a b ⟶ pullback c d :=
  pullback.lift (pullback.fst a b ≫ cu) (pullback.snd a b ≫ du) (by
    rw [Category.assoc, ← hc.w, Category.assoc, ← hd.w,
      ← Category.assoc, ← Category.assoc, pullback.condition])

/-- An intersection supported in an open chart is its actual restricted
intersection, with full scheme structure and both projection triangles. -/
def iso : pullback c d ≅ pullback a b where
  hom := toRestricted u c d a b cu du hc hd h
  inv := fromRestricted u c d a b cu du hc hd
  hom_inv_id := by
    apply pullback.hom_ext <;>
      simp [toRestricted, fromRestricted, Category.assoc]
  inv_hom_id := by
    let : IsOpenImmersion cu := MorphismProperty.of_isPullback hc inferInstance
    let : IsOpenImmersion du := MorphismProperty.of_isPullback hd inferInstance
    apply pullback.hom_ext
    · apply (cancel_mono cu).mp
      simp [toRestricted, fromRestricted, Category.assoc]
    · apply (cancel_mono du).mp
      simp [toRestricted, fromRestricted, Category.assoc]

@[reassoc] theorem iso_hom_fst :
    (iso u c d a b cu du hc hd h).hom ≫ pullback.fst a b ≫ cu = pullback.fst c d := by
  simp [iso, toRestricted]

@[reassoc] theorem iso_hom_snd :
    (iso u c d a b cu du hc hd h).hom ≫ pullback.snd a b ≫ du = pullback.snd c d := by
  simp [iso, toRestricted]

end AlgebraicGeometry.OpenIntersectionRestriction

end -- original noncomputable section
end

namespace AlgebraicGeometry.Scheme.Pullback.OpenIntersection

/-- The range identity of a cartesian square of schemes, obtained from the
actual scheme pullback and its canonical comparison isomorphism. -/
theorem schemePullback_range_snd {P X Y Z : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {c : X ⟶ Z} {d : Y ⟶ Z}
    (h : IsPullback a b c d) : Set.range b = d ⁻¹' Set.range c := by
  rw [← h.isoPullback_hom_snd]
  change Set.range ((pullback.snd c d) ∘ h.isoPullback.hom) = _
  rw [Set.range_comp, (h.isoPullback.hom).surjective.range_eq, Set.image_univ]
  exact Scheme.Pullback.range_snd c d

/-- The open-range version of the scheme pullback range identity. -/
theorem schemePullback_preimage_opensRange {P X Y Z : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {c : X ⟶ Z} {d : Y ⟶ Z}
    [IsOpenImmersion b] [IsOpenImmersion c] (h : IsPullback a b c d) :
    d ⁻¹ᵁ c.opensRange = b.opensRange := by
  ext y
  exact Set.ext_iff.mp (schemePullback_range_snd h).symm y

end AlgebraicGeometry.Scheme.Pullback.OpenIntersection
