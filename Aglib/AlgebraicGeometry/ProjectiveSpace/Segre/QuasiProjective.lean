/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Segre.ClosedImmersion

/-!
# Products of quasi-projective schemes over an affine base

For H-quasi-projective `f : X ⟶ Spec R` and `g : Y ⟶ Spec R`, the fibre product `X ×_R Y` is
H-quasi-projective over `Spec R` (`isHQuasiProjective_pullback_fst_comp`): the immersions
`X ⟶ P(ι)_R` and `Y ⟶ P(κ)_R` induce an immersion `X ×_R Y ⟶ P(ι)_R ×_R P(κ)_R`
(`MorphismProperty.pullbackMap`), followed by the Segre closed immersion
`ProjectiveSpace.Segre.embedding R ι κ` into `P(ι × κ)_R`; the composite is
`ProjectiveSpace.Segre.productEmbedding`. The same argument with closed immersions
shows that products of H-projective schemes are H-projective (`isHProjective_pullback_fst_comp`).
For H-projective morphisms this is the affine-base case of Stacks, Lemma 29.44.8 (Tag 01WF: base
change) and Lemma 29.44.7 (Tag 01WE: composition), applied to `X ×_R Y ⟶ Y` and `Y ⟶ Spec R`;
Stacks states no such lemma for H-quasi-projective morphisms, and both cases are proved here
directly by the Segre embedding.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}} {X Y : Scheme.{u}}

namespace ProjectiveSpace.Segre

variable {ι κ : Type u} (i : X ⟶ ProjectiveSpace R ι) (j : Y ⟶ ProjectiveSpace R κ)

/-- The **Segre morphism of a fibre product**: for `i : X ⟶ P(ι)_R` and `j : Y ⟶ P(κ)_R`, the
induced morphism `X ×_R Y ⟶ P(ι)_R ×_R P(κ)_R` followed by the Segre embedding into
`P(ι × κ)_R`. -/
def productEmbedding :
    pullback (i ≫ toSpec R ι) (j ≫ toSpec R κ) ⟶ ProjectiveSpace R (ι × κ) :=
  pullback.map (i ≫ toSpec R ι) (j ≫ toSpec R κ) (toSpec R ι) (toSpec R κ) i j (𝟙 _)
    ((Category.comp_id _).trans rfl) ((Category.comp_id _).trans rfl) ≫ embedding R ι κ

/-- The Segre morphism of a fibre product lies over the composite of the first projection with
the structure morphism of `X`. -/
theorem productEmbedding_toSpec :
    productEmbedding i j ≫ toSpec R (ι × κ) =
      pullback.fst (i ≫ toSpec R ι) (j ≫ toSpec R κ) ≫ i ≫ toSpec R ι := by
  rw [productEmbedding, Category.assoc, embedding_toSpec, ← Category.assoc, pullback.lift_fst,
    Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- The Segre morphism of a fibre product of immersions is an immersion. -/
instance isImmersion_productEmbedding [IsImmersion i] [IsImmersion j] :
    IsImmersion (productEmbedding i j) := by
  have : IsImmersion (pullback.map (i ≫ toSpec R ι) (j ≫ toSpec R κ) (toSpec R ι) (toSpec R κ)
      i j (𝟙 _) ((Category.comp_id _).trans rfl) ((Category.comp_id _).trans rfl)) :=
    MorphismProperty.pullbackMap (P := @IsImmersion) ‹_› ‹_› rfl rfl
  rw [productEmbedding]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- The Segre morphism of a fibre product of quasi-compact morphisms is quasi-compact. -/
instance quasiCompact_productEmbedding [QuasiCompact i] [QuasiCompact j] :
    QuasiCompact (productEmbedding i j) := by
  have : QuasiCompact (pullback.map (i ≫ toSpec R ι) (j ≫ toSpec R κ) (toSpec R ι)
      (toSpec R κ) i j (𝟙 _) ((Category.comp_id _).trans rfl) ((Category.comp_id _).trans rfl)) :=
    MorphismProperty.pullbackMap (P := @QuasiCompact) ‹_› ‹_› rfl rfl
  rw [productEmbedding]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- The Segre morphism of a fibre product of closed immersions is a closed immersion. -/
instance isClosedImmersion_productEmbedding [IsClosedImmersion i] [IsClosedImmersion j] :
    IsClosedImmersion (productEmbedding i j) := by
  have : IsClosedImmersion (pullback.map (i ≫ toSpec R ι) (j ≫ toSpec R κ) (toSpec R ι)
      (toSpec R κ) i j (𝟙 _) ((Category.comp_id _).trans rfl) ((Category.comp_id _).trans rfl)) :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion) ‹_› ‹_› rfl rfl
  rw [productEmbedding]
  infer_instance

end ProjectiveSpace.Segre

open ProjectiveSpace.Segre in
/-- **Products of H-quasi-projective schemes over `Spec R` are H-quasi-projective**, by the Segre
embedding. -/
instance isHQuasiProjective_pullback_fst_comp (f : X ⟶ Spec R) (g : Y ⟶ Spec R)
    [IsHQuasiProjective f] [IsHQuasiProjective g] :
    IsHQuasiProjective (pullback.fst f g ≫ f) := by
  obtain ⟨ι, _, i, _, _, rfl⟩ := IsHQuasiProjective.exists_isImmersion (f := f)
  obtain ⟨κ, _, j, _, _, rfl⟩ := IsHQuasiProjective.exists_isImmersion (f := g)
  exact ⟨ι × κ, inferInstance, productEmbedding i j, inferInstance, inferInstance,
    productEmbedding_toSpec i j⟩

open ProjectiveSpace.Segre in
/-- **Products of H-projective schemes over `Spec R` are H-projective**, by the Segre embedding. -/
instance isHProjective_pullback_fst_comp (f : X ⟶ Spec R) (g : Y ⟶ Spec R) [IsHProjective f]
    [IsHProjective g] : IsHProjective (pullback.fst f g ≫ f) := by
  obtain ⟨ι, _, i, _, rfl⟩ := IsHProjective.exists_isClosedImmersion (f := f)
  obtain ⟨κ, _, j, _, rfl⟩ := IsHProjective.exists_isClosedImmersion (f := g)
  exact ⟨ι × κ, inferInstance, productEmbedding i j, inferInstance, productEmbedding_toSpec i j⟩

/-- The fibre product of H-quasi-projective schemes is H-quasi-projective over `Spec R` through
the second factor. -/
theorem isHQuasiProjective_pullback_snd_comp (f : X ⟶ Spec R) (g : Y ⟶ Spec R)
    [IsHQuasiProjective f] [IsHQuasiProjective g] :
    IsHQuasiProjective (pullback.snd f g ≫ g) :=
  pullback.condition (f := f) (g := g) ▸ inferInstance

/-- The fibre product of H-projective schemes is H-projective over `Spec R` through the second
factor. -/
theorem isHProjective_pullback_snd_comp (f : X ⟶ Spec R) (g : Y ⟶ Spec R) [IsHProjective f]
    [IsHProjective g] : IsHProjective (pullback.snd f g ≫ g) :=
  pullback.condition (f := f) (g := g) ▸ inferInstance

end AlgebraicGeometry
