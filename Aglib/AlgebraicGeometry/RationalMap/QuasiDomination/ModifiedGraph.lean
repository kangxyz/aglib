/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.Range
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# The actual original graph after modification

This is ordinary Cartesian base change of a section graph. Its protected
closed range is transported by an actual continuous map of restricted
products. No schematic-image base-change assertion is used.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

variable {X Y B : Scheme.{u}} (U : X.Opens) (f : Y ⟶ X)
    (g : U.toScheme ⟶ Y) (hg : g ≫ f = U.ι) (β : B ⟶ X)

/-- The original section graph on the entire inverse image of its domain. -/
def modifiedGraph : (β ⁻¹ᵁ U).toScheme ⟶ pullback β f :=
  pullback.lift (β ⁻¹ᵁ U).ι ((β ∣_ U) ≫ g)
    ((morphismRestrict_ι β U).symm.trans
      ((congrArg (fun k ↦ (β ∣_ U) ≫ k) hg.symm).trans
        (Category.assoc (β ∣_ U) g f).symm))

@[reassoc (attr := simp)]
lemma modifiedGraph_fst : modifiedGraph U f g hg β ≫ pullback.fst β f = (β ⁻¹ᵁ U).ι :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma modifiedGraph_snd : modifiedGraph U f g hg β ≫ pullback.snd β f = (β ∣_ U) ≫ g :=
  pullback.lift_snd _ _ _

/-- The modified graph is the literal pullback of the original section along
its target projection. -/
lemma isPullback_modifiedGraph :
    IsPullback (modifiedGraph U f g hg β) (β ∣_ U) (pullback.snd β f) g := by
  have H : IsPullback (modifiedGraph U f g hg β ≫ pullback.fst β f)
      (β ∣_ U) β (g ≫ f) := by
    rw [modifiedGraph_fst, hg]
    exact (isPullback_morphismRestrict β U).flip
  exact H.of_right (modifiedGraph_snd U f g hg β) (IsPullback.of_hasPullback β f)

/-- The actual product map to the unmodified section product. -/
def modifiedGraphProductMap : pullback β f ⟶ pullback (𝟙 X) f :=
  pullback.lift (pullback.fst β f ≫ β) (pullback.snd β f)
    ((Category.comp_id _).trans pullback.condition)

@[reassoc (attr := simp)]
lemma modifiedGraphProductMap_fst :
    modifiedGraphProductMap f β ≫ pullback.fst (𝟙 X) f = pullback.fst β f ≫ β :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma modifiedGraphProductMap_snd :
    modifiedGraphProductMap f β ≫ pullback.snd (𝟙 X) f = pullback.snd β f :=
  pullback.lift_snd _ _ _

/-- Exact graph range after modification, with no flatness assumption. -/
lemma range_modifiedGraph :
    Set.range (modifiedGraph U f g hg β) = modifiedGraphProductMap f β ⁻¹'
      Set.range (pullback.lift U.ι g (by simpa using hg.symm)) := by
  have H₀ : IsPullback (pullback.lift U.ι g (by simpa using hg.symm))
      (𝟙 U.toScheme) (pullback.snd (𝟙 X) f) g :=
    IsPullback.of_vert_isIso ⟨(pullback.lift_snd U.ι g (by simpa using hg.symm)).trans
      (Category.id_comp g).symm⟩
  rw [Scheme.Pullback.Transport.range_eq_preimage_of_isPullback
    (isPullback_modifiedGraph U f g hg β),
    Scheme.Pullback.Transport.range_eq_preimage_of_isPullback H₀]
  ext x
  change pullback.snd β f x ∈ Set.range g ↔
    (modifiedGraphProductMap f β ≫ pullback.snd (𝟙 X) f) x ∈ Set.range g
  rw [modifiedGraphProductMap_snd]

/-- Closedness of the original graph over the protected open survives its
actual base change, independently of whether the modification is flat. -/
lemma isClosed_modifiedGraph_over (V : X.Opens)
    (hclosed : IsClosed ((pullback.fst (𝟙 X) f ⁻¹ᵁ V).ι ⁻¹'
      Set.range (pullback.lift U.ι g (by simpa using hg.symm)))) :
    IsClosed ((pullback.fst β f ⁻¹ᵁ (β ⁻¹ᵁ V)).ι ⁻¹'
      Set.range (modifiedGraph U f g hg β)) := by
  let A := pullback.fst (𝟙 X) f ⁻¹ᵁ V
  let C := pullback.fst β f ⁻¹ᵁ (β ⁻¹ᵁ V)
  let m := modifiedGraphProductMap f β
  let mV : C.toScheme → A.toScheme := fun x ↦ ⟨m x.1, by
    change (m ≫ pullback.fst (𝟙 X) f) x.1 ∈ V
    rw [modifiedGraphProductMap_fst]
    exact x.property⟩
  have hmV : Continuous mV := (m.continuous.comp continuous_subtype_val).subtype_mk _
  have heq : C.ι ⁻¹' Set.range (modifiedGraph U f g hg β) =
      mV ⁻¹' (A.ι ⁻¹' Set.range (pullback.lift U.ι g (by simpa using hg.symm))) := by
    rw [range_modifiedGraph]
    rfl
  change IsClosed (C.ι ⁻¹' Set.range (modifiedGraph U f g hg β))
  rw [heq]
  exact hclosed.preimage hmV

end AlgebraicGeometry.Scheme.QuasiDomination
