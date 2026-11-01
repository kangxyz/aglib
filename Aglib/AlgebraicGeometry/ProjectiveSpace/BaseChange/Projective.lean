/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian
public import Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective

/-!
# Native projectivity under affine base change

The original finite-coordinate closed embedding is base changed by the
actual pullback map. The existing Cartesian comparison for polynomial
projective space identifies its target with projective space over the new
ring. The original fibre-product projection is the resulting structure map.

No field, nontriviality or choice of a replacement source scheme is required.
The embedding witness is chosen only inside the proof of the existing
`IsHProjective` predicate.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {R S : CommRingCat.{u}} {X : Scheme.{u}}

/-- The actual base change along a ring map of a native projective
morphism is projective over the new affine base. -/
theorem IsHProjective.pullback_snd_specMap
    (p : X ⟶ Spec R) [IsHProjective p] (φ : R ⟶ S) :
    IsHProjective (pullback.snd p (Spec.map φ)) := by
  obtain ⟨ι, hι, i, hi, hp⟩ := IsHProjective.exists_isClosedImmersion (f := p)
  let : Finite ι := hι
  let : IsClosedImmersion i := hi
  let t := Spec.map φ
  have h₁ : p ≫ 𝟙 (Spec R) = i ≫ ProjectiveSpace.toSpec R ι := by simpa using hp.symm
  have h₂ : t ≫ 𝟙 (Spec R) = 𝟙 (Spec S) ≫ t := by simp
  let b : pullback p t ⟶ pullback (ProjectiveSpace.toSpec R ι) t :=
    pullback.map p t (ProjectiveSpace.toSpec R ι) t i (𝟙 _) (𝟙 _) h₁ h₂
  let : MorphismProperty.IsStableUnderComposition (@IsClosedImmersion.{u}) :=
    { comp_mem := fun f g hf hg => @IsClosedImmersion.comp _ _ _ f g hf hg }
  let : IsClosedImmersion b :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion.{u})
      (inferInstanceAs (IsClosedImmersion i)) (inferInstanceAs (IsClosedImmersion (𝟙 (Spec S))))
      h₁ h₂
  let e := ProjectiveSpace.baseChangeIso φ.hom ι
  have he : e.inv ≫ ProjectiveSpace.toSpec S ι =
      pullback.snd (ProjectiveSpace.toSpec R ι) t := by
    apply (cancel_epi e.hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact (ProjectiveSpace.baseChangeIso_hom_snd φ.hom ι).symm
  refine ⟨ι, inferInstance, b ≫ e.inv, inferInstance, ?_⟩
  rw [Category.assoc, he]
  simp only [b, pullback.map, pullback.lift_snd, Category.comp_id, t]

/-- Native projectivity is preserved by the original pullback along any
morphism between affine schemes, including arbitrary field extension. -/
instance IsHProjective.pullback_snd
    (p : X ⟶ Spec R) [IsHProjective p] (t : Spec S ⟶ Spec R) :
    IsHProjective (pullback.snd p t) := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective t
  exact IsHProjective.pullback_snd_specMap p φ

end AlgebraicGeometry
