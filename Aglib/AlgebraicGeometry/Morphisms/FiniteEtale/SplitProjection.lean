/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The actual split coproduct projection and its finite-flat rank

Finite coproduct projection has actual finite-etale structure and rank Nat.card I. Native
trivialCover constructs the same split cover, but the source statement includes the exact
Sigma.desc scheme map and native finrank.

Source: `R5Lab.Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.SplitProjection`, frozen R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`0647b69c5cff36a0c68f73ab2031e45dcae47a347da99bc4661c6edc4fd54dc6`. Selected lines: [[40, 117]].
The actual objects, canonical maps, universes and stated premises are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.SplitProjection

variable (I : Type u) [Finite I]

/-- The actual coproduct projection, not an abstract cover model. -/
def projection (X : Scheme.{u}) : (∐ fun _ : I => X) ⟶ X :=
  Sigma.desc fun _ => 𝟙 X

/-- Every split coproduct projection is etale. -/
instance instEtale (X : Scheme.{u}) : Etale (projection I X) := by
  exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) (fun _ => inferInstance)

omit [Finite I] in
lemma spec_comparison (R : CommRingCat.{u}) :
    projection I (Spec R) = sigmaSpec (fun _ : I => R) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (I → R))) := by
  apply Sigma.hom_ext
  intro i
  simp only [projection, Sigma.ι_comp_desc, ι_sigmaSpec_assoc]
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

/-- The spectrum of the finite product algebra is finite over its base. -/
instance instFiniteAlgebraMap (R : CommRingCat.{u}) :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R (I → R)))) := by
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- The spectrum of the product algebra is flat over its base. -/
instance instFlatAlgebraMap (R : CommRingCat.{u}) :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap R (I → R)))) := by
  rw [Flat.SpecMap_iff]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The actual split projection over an affine scheme is finite. -/
instance instFiniteSpec (R : CommRingCat.{u}) : IsFinite (projection I (Spec R)) := by
  rw [spec_comparison]
  infer_instance

lemma rank_spec (R : CommRingCat.{u}) (x : Spec R) :
    (projection I (Spec R)).finrank x = Nat.card I := by
  have : Nontrivial R := x.nontrivial
  rw [spec_comparison, Scheme.Hom.finrank_comp_left_of_isIso,
    Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  classical
  let := Fintype.ofFinite I
  simp [Nat.card_eq_fintype_card]

/-- The actual split projection is preserved by every base change. -/
lemma baseChange {X Y : Scheme.{u}} (g : Y ⟶ X) :
    IsPullback (Limits.Sigma.map (fun _ : I => g)) (projection I Y) (projection I X) g := by
  have h := (FinitaryPreExtensive.isUniversal_finiteCoproducts
    (coproductIsCoproduct (fun _ : I => X))).isPullback_of_isColimit_right
      (fun _ => 𝟙 X) (projection I X) g (fun _ => g) (fun _ => 𝟙 Y)
      (fun _ => IsPullback.id_vert g) (coproductIsCoproduct (fun _ : I => Y))
      (fun i => by simp [projection])
  convert! h using 1

/-- The actual split projection over every scheme is finite. -/
instance instFinite (X : Scheme.{u}) : IsFinite (projection I X) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsFinite) X.affineCover
  intro i
  change IsFinite (pullback.snd (projection I X) (X.affineCover.f i))
  let h := baseChange I (X.affineCover.f i)
  apply (MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) h.isoPullback.hom _).mp
  rw [h.isoPullback_hom_snd]
  change IsFinite (projection I (Spec _))
  infer_instance

/-- Over any scheme, each actual split cover has the expected instFinite-flat rank. -/
lemma rank (X : Scheme.{u}) (x : X) :
    (projection I X).finrank x = Nat.card I := by
  obtain ⟨R, g, _, y, rfl⟩ := X.exists_Spec_apply_eq x
  rw [← Scheme.Hom.finrank_of_isPullback _ _ _ _ (baseChange I g)]
  exact rank_spec I R y

/-- Direct statement for the categorical coproduct projection. -/
theorem sigmaDesc_finite_etale_finrank (X : Scheme.{u}) :
    IsFinite (Sigma.desc (fun _ : I => 𝟙 X)) ∧
    Etale (Sigma.desc (fun _ : I => 𝟙 X)) ∧
    ∀ x : X, (Sigma.desc (fun _ : I => 𝟙 X)).finrank x = Nat.card I :=
  ⟨instFinite I X, instEtale I X, rank I X⟩

end AlgebraicGeometry.Scheme.SplitProjection
