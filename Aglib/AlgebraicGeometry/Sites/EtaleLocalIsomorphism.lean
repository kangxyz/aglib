/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Category.Grp.Limits

/-! # Isomorphisms detected on original pointed etale refinements

A map of original abelian sheaves is invertible when its component is
bijective on an etale refinement above every point of every original test.
The proof uses the native image and equalizer sieves and the existing
locally-bijective sheaf criterion, without a new cover or stalk model.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Etale
universe u v

/-- Bijective original components on point-covering refinements detect an
isomorphism of abelian sheaves. The refinement may depend on the original
etale test and its point; no global section surjectivity is assumed. -/
theorem isIso_of_pointed_refinement_bijective {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{v}} (m : F ⟶ G)
    (H : ∀ (T : X.Etale) (t : T.left),
      ∃ (U : X.Etale) (a : U ⟶ T) (u : U.left),
        a.left u = t ∧ Function.Bijective (m.hom.app (op U))) : IsIso m := by
  let : @MorphismProperty.IsStableUnderComposition Scheme.{u} _
      (@AlgebraicGeometry.Etale.{u}) := {
    comp_mem := fun f g hf hg => @AlgebraicGeometry.Etale.etale_comp _ _ f _ g hf hg }
  let : Presheaf.IsLocallyInjective X.smallEtaleTopology m.hom := {
    equalizerSieve_mem := by
      intro T s t hst
      change _ ∈ X.smallGrothendieckTopology @AlgebraicGeometry.Etale T.unop
      have he := Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology X
        (P := @AlgebraicGeometry.Etale) (Q := @AlgebraicGeometry.Etale) le_rfl
      apply (congrArg (fun J => Presheaf.equalizerSieve s t ∈ J T.unop) he).mpr
      apply (Scheme.mem_toGrothendieck_smallPretopology T.unop _).mpr
      intro x
      obtain ⟨U, a, u, hu, ha⟩ := H T.unop x
      refine ⟨U, a, u, ?_, inferInstance, hu⟩
      change F.obj.map a.op s = F.obj.map a.op t
      apply ha.injective
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hst] }
  let : Presheaf.IsLocallySurjective X.smallEtaleTopology m.hom := {
    imageSieve_mem := by
      intro T s
      change _ ∈ X.smallGrothendieckTopology @AlgebraicGeometry.Etale T
      have he := Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology X
        (P := @AlgebraicGeometry.Etale) (Q := @AlgebraicGeometry.Etale) le_rfl
      apply (congrArg (fun J => Presheaf.imageSieve m.hom s ∈ J T) he).mpr
      apply (Scheme.mem_toGrothendieck_smallPretopology T _).mpr
      intro x
      obtain ⟨U, a, u, hu, ha⟩ := H T x
      refine ⟨U, a, u, ?_, inferInstance, hu⟩
      exact ha.surjective (G.obj.map a.op s) }
  exact (Sheaf.isLocallyBijective_iff_isIso m).mp ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme.Etale
