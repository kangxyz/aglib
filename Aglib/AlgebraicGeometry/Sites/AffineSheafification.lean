/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.Basic
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.AlgebraicGeometry.ResidueField

/-! # Sheafification detects original maps on affine etale tests

The actual affine open charts of every test object form a covering family.
No quasi-compactness of that test object is required, and the presheaves need
not already be separated.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable (X : Scheme.{u})
  {P Q : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (a : P ⟶ Q)

/-- Injectivity on affine tests implies local injectivity on the original site. -/
theorem locallyInjective_of_affine
    (h : ∀ U : X.Etale, IsAffine U.left → Function.Injective (a.app (op U))) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology a where
  equalizerSieve_mem {U} x y hxy := by
    change _ ∈ X.smallGrothendieckTopology (@Etale : MorphismProperty Scheme.{u}) U.unop
    rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
      Scheme.mem_toGrothendieck_smallPretopology]
    intro z
    obtain ⟨R, f, hf, t, ht⟩ := Scheme.exists_Spec_apply_eq z
    let : IsOpenImmersion f := hf
    let V : X.Etale := Etale.mk (f ≫ U.unop.hom)
    let g : V ⟶ U.unop := MorphismProperty.Over.homMk f rfl
    refine ⟨V, g, t, ?_, inferInstanceAs (Etale f), ht⟩
    change P.map g.op x = P.map g.op y
    apply h V (inferInstanceAs (IsAffine (Spec R)))
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]

/-- Surjectivity on affine tests implies local surjectivity on the original site. -/
theorem locallySurjective_of_affine
    (h : ∀ U : X.Etale, IsAffine U.left → Function.Surjective (a.app (op U))) :
    Presheaf.IsLocallySurjective X.smallEtaleTopology a where
  imageSieve_mem {U} x := by
    change _ ∈ X.smallGrothendieckTopology (@Etale : MorphismProperty Scheme.{u}) U
    rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
      Scheme.mem_toGrothendieck_smallPretopology]
    intro z
    obtain ⟨R, f, hf, t, ht⟩ := Scheme.exists_Spec_apply_eq z
    let : IsOpenImmersion f := hf
    let V : X.Etale := Etale.mk (f ≫ U.hom)
    let g : V ⟶ U := MorphismProperty.Over.homMk f rfl
    refine ⟨V, g, t, ?_, inferInstanceAs (Etale f), ht⟩
    exact h V (inferInstanceAs (IsAffine (Spec R))) (Q.map g.op x)

attribute [local instance] EtaleCohomology.hasSheafifyLarge

/-- Actual sheafification sends an affinewise bijection to an isomorphism. -/
theorem isIso_sheafify_map_of_affine
    (h : ∀ U : X.Etale, IsAffine U.left → Function.Bijective (a.app (op U))) :
    IsIso ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map a) := by
  let : Presheaf.IsLocallyInjective X.smallEtaleTopology a :=
    locallyInjective_of_affine X a (fun U hU => (h U hU).injective)
  let : Presheaf.IsLocallySurjective X.smallEtaleTopology a :=
    locallySurjective_of_affine X a (fun U hU => (h U hU).surjective)
  exact (X.smallEtaleTopology.W_iff a).mp (X.smallEtaleTopology.W_of_isLocallyBijective a)

/-- A presheaf zero on affine tests has zero original sheafification. -/
theorem isZero_sheafify_of_affine
    (h : ∀ U : X.Etale, IsAffine U.left → Subsingleton (P.obj (op U))) :
    IsZero ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj P) := by
  let L := presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  have hzero : IsIso (L.map (0 : P ⟶ P)) :=
    isIso_sheafify_map_of_affine X _ (fun U hU => by
      let := h U hU
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun x => ⟨0, Subsingleton.elim _ _⟩⟩)
  have hz : L.map (0 : P ⟶ P) = 0 := L.map_zero _ _
  let : IsIso (0 : L.obj P ⟶ L.obj P) := by rw [← hz]; exact hzero
  exact IsZero.of_epi_zero (L.obj P) (L.obj P)

end AlgebraicGeometry.Scheme.Etale
