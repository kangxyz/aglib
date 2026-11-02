/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.Abelian

/-! # Sheafification of an original locally zero etale presheaf

Pointed refinements annihilating each original section make the original zero
endomorphism locally surjective. Sheafification preserves that property, so
its zero endomorphism is epi and its actual target is zero. No alternative
cover or sheafification model is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Etale

universe u v

/-- Actual pointed local annihilation of every section kills the original
abelian presheaf's sheafification. Refinements may depend on the section. -/
theorem isZero_sheafification_of_pointed_localZero {X : Scheme.{u}}
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{v}]
    [X.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{v}]
    [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{v})]
    (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{v})
    (H : ∀ (U : X.Etale) (c : P.obj (op U)) (x : U.left),
      ∃ (V : X.Etale) (a : V ⟶ U) (y : V.left),
        a.left y = x ∧ P.map a.op c = 0) :
    IsZero ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{v}).obj P) := by
  let : @MorphismProperty.IsStableUnderComposition Scheme.{u} _
      (@AlgebraicGeometry.Etale.{u}) := {
    comp_mem := fun f g hf hg => @AlgebraicGeometry.Etale.etale_comp _ _ f _ g hf hg }
  let : Presheaf.IsLocallySurjective X.smallEtaleTopology (0 : P ⟶ P) := {
    imageSieve_mem := by
      intro U c
      change _ ∈ X.smallGrothendieckTopology @AlgebraicGeometry.Etale U
      have he := Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology X
        (P := @AlgebraicGeometry.Etale) (Q := @AlgebraicGeometry.Etale) le_rfl
      apply (congrArg (fun J => Presheaf.imageSieve (0 : P ⟶ P) c ∈ J U) he).mpr
      apply (Scheme.mem_toGrothendieck_smallPretopology U _).mpr
      intro x
      obtain ⟨V, a, y, hy, hz⟩ := H U c x
      refine ⟨V, a, y, ?_, inferInstance, hy⟩
      refine ⟨0, ?_⟩
      simpa using hz.symm }
  let L := presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{v}
  let : Sheaf.IsLocallySurjective (L.map (0 : P ⟶ P)) :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff
      X.smallEtaleTopology (0 : P ⟶ P)).mpr inferInstance
  exact IsZero.of_epi_eq_zero (L.map (0 : P ⟶ P)) (L.map_zero _ _)

end AlgebraicGeometry.Scheme.Etale
