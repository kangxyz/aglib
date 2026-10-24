/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.MappingCone.Identity

/-!
# Mapping cones as native identity-cone attachments

The original cone of a map is the pushout of the original identity-cone
inclusion along that map. The universal property is verified degreewise
using the native cone projections and inclusions. The resulting canonical
isomorphism retains the actual pushout inclusion, with no boundedness premise.
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.mappingCone

variable {C : Type u} [Category.{v} C] [Abelian C]
  {A K : CochainComplex C ℤ} (f : A ⟶ K)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual cone of `f` is the pushout attaching the identity cone along `f`. -/
lemma isPushout_inr_identity :
    IsPushout f (inr (𝟙 A)) (inr f) (map (𝟙 A) f (𝟙 A) f (by simp)) := by
  apply CochainComplex.isPushout_of_degreewise
  intro n
  apply IsPushout.mk' (by simp [map])
  · intro X a b hi hj
    apply ext_from f (n + 1) n rfl
    · have h := congrArg (fun t => (inl (𝟙 A)).v (n + 1) n (by omega) ≫ t) hj
      simpa [map, Category.assoc] using h
    · exact hi
  · intro X a b hab
    refine ⟨(fst f).1.v n (n + 1) rfl ≫
      (inl (𝟙 A)).v (n + 1) n (by omega) ≫ b +
      (snd f).v n n (add_zero n) ≫ a, ?_, ?_⟩
    · simp [Preadditive.comp_add]
    · apply ext_from (𝟙 A) (n + 1) n rfl
      · simp [map, Preadditive.comp_add]
      · simpa [map, Preadditive.comp_add] using hab

/-- The canonical pushout-cone comparison is an isomorphism of native complexes. -/
def pushoutIdentityIso : pushout f (inr (𝟙 A)) ≅ mappingCone f :=
  (IsPushout.of_hasPushout f (inr (𝟙 A))).isoIsPushout _ _
    (isPushout_inr_identity f)

@[reassoc (attr := simp)]
lemma inl_pushoutIdentityIso_hom :
    pushout.inl f (inr (𝟙 A)) ≫ (pushoutIdentityIso f).hom = inr f :=
  IsPushout.inl_isoIsPushout_hom _ _
    (IsPushout.of_hasPushout f (inr (𝟙 A))) (isPushout_inr_identity f)

end CochainComplex.mappingCone
