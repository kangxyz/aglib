/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Actual pointwise etale local preimages

A locally surjective original presheaf map has a local preimage on an actual
etale chart above every scheme point. The chart arrow belongs to the original
image sieve; no substitute covering family is used.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Etale

universe u v

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem coveringSieve_point {X : Scheme.{u}} {U : X.Etale} (R : Sieve U)
    (hR : R ∈ X.smallEtaleTopology U) (x : U.left) :
    ∃ (V : X.Etale) (f : V ⟶ U) (y : V.left), R f ∧ f.left y = x := by
  have he := Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology X
    (P := @AlgebraicGeometry.Etale) (Q := @AlgebraicGeometry.Etale) le_rfl
  have hR' : R ∈ (X.smallPretopology @AlgebraicGeometry.Etale
      @AlgebraicGeometry.Etale).toGrothendieck U :=
    (congrArg (fun J => R ∈ J U) he).mp hR
  obtain ⟨V, f, y, hf, _, hy⟩ :=
    (Scheme.mem_toGrothendieck_smallPretopology U R).mp hR' x
  exact ⟨V, f, y, hf, hy⟩

/-- A local preimage at each original scheme point, with the actual etale restriction equality. -/
theorem exists_localPreimage_at_point {X : Scheme.{u}}
    {F G : X.Etaleᵒᵖ ⥤ Ab.{v}} (φ : F ⟶ G)
    [Presheaf.IsLocallySurjective X.smallEtaleTopology φ] {U : X.Etale}
    (a : G.obj (op U)) (x : U.left) :
    ∃ (V : X.Etale) (f : V ⟶ U) (y : V.left) (b : F.obj (op V)),
      f.left y = x ∧ φ.app (op V) b = G.map f.op a := by
  obtain ⟨V, f, y, hf, hy⟩ := coveringSieve_point (Presheaf.imageSieve φ a)
    (Presheaf.imageSieve_mem X.smallEtaleTopology φ a) x
  obtain ⟨b, hb⟩ := hf
  exact ⟨V, f, y, b, hy, hb⟩

end AlgebraicGeometry.Scheme.Etale
