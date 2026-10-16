/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Localization.LocalizerMorphism


/-!
# Fully faithful localization restriction by actual approximations

A fully faithful inclusion becomes fully faithful after localization when
weak-equivalence-preserving approximation functors have actual counits which
become invertible on each pair of source objects. We construct both localized
counits and prove their compatibility before proving injectivity and surjectivity
on hom sets. No localized full-faithfulness or equivalence hypothesis is used.
-/
/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/CategoryTheory/Localization/Approximation.lean`.
SHA-256: `53a76c2322e29b8dee220fb7b3d6a994e49cd309bfcc0f479c60a72ffab96dc3`.
Selected source lines: 1–176.
Actual source objects, maps, hypotheses and independent universes are preserved.
-/

@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
namespace CategoryTheory.Localization.Restriction

variable {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [F.Full] [F.Faithful] (W : MorphismProperty D)

/-- The morphisms of `C` whose images under `F` belong to `W`. -/
abbrev sourceWeak : MorphismProperty C := W.inverseImage F

/-- The functor from the localization of `C` at the inverse image of `W` to the localization of `D`
at `W`, induced by `F`. -/
def inclusion : (sourceWeak F W).Localization ⥤ W.Localization :=
  Localization.Construction.lift (F ⋙ W.Q) (fun _ _ f hf => W.Q_inverts (F.map f) hf)

omit [F.Full] [F.Faithful] in
@[simp]
theorem inclusion_map_Q {X Y : C} (f : X ⟶ Y) :
    (inclusion F W).map ((sourceWeak F W).Q.map f) = W.Q.map (F.map f) := by
  have h := (eqToHom (Localization.Construction.fac (W := sourceWeak F W) (F ⋙ W.Q)
    (fun _ _ f hf => W.Q_inverts (F.map f) hf))).naturality f
  simpa only [inclusion, Functor.comp_map, eqToHom_app, eqToHom_refl, Category.comp_id,
    Category.id_comp, NatTrans.id_app] using h

variable {ι : Type*} (T : ι → D ⥤ C)
    (ε : ∀ i, T i ⋙ F ⟶ 𝟭 D)
    (hT : ∀ i, W ≤ (sourceWeak F W).inverseImage (T i))

/-- A weak-equivalence-preserving approximation really descends to localization. -/
def approximation (i : ι) : W.Localization ⥤ (sourceWeak F W).Localization :=
  Localization.Construction.lift (T i ⋙ (sourceWeak F W).Q)
    (fun _ _ f hf => (sourceWeak F W).Q_inverts ((T i).map f) (hT i f hf))

omit [F.Full] [F.Faithful] in
@[simp]
theorem approximation_map_Q (i : ι) {X Y : D} (f : X ⟶ Y) :
    (approximation F W T hT i).map (W.Q.map f) = (sourceWeak F W).Q.map ((T i).map f) := by
  have h := (eqToHom (Localization.Construction.fac (T i ⋙ (sourceWeak F W).Q)
    (fun _ _ f hf => (sourceWeak F W).Q_inverts ((T i).map f) (hT i f hf)))).naturality f
  simpa only [approximation, Functor.comp_map, eqToHom_app, eqToHom_refl, Category.comp_id,
    Category.id_comp, NatTrans.id_app] using h

/-- The counit restricts through the actual fully faithful inclusion. -/
def restrictionCounit (i : ι) : F ⋙ T i ⟶ 𝟭 C where
  app X := F.preimage ((ε i).app (F.obj X))
  naturality {X Y} f := by
    apply F.map_injective
    simp only [Functor.map_comp, Functor.map_preimage]
    exact (ε i).naturality (F.map f)

@[simp]
theorem map_restrictionCounit_app (i : ι) (X : C) :
    F.map ((restrictionCounit F T ε i).app X) = (ε i).app (F.obj X) := F.map_preimage _

/-- The restricted counit descends to the source localization. -/
def sourceCounit (i : ι) : inclusion F W ⋙ approximation F W T hT i ⟶
    𝟭 (sourceWeak F W).Localization :=
  Localization.Construction.natTransExtension
    { app X := (sourceWeak F W).Q.map ((restrictionCounit F T ε i).app X)
      naturality := by
        intro X Y f
        change (approximation F W T hT i).map
          ((inclusion F W).map ((sourceWeak F W).Q.map f)) ≫
            (sourceWeak F W).Q.map ((restrictionCounit F T ε i).app Y) =
          (sourceWeak F W).Q.map ((restrictionCounit F T ε i).app X) ≫ (sourceWeak F W).Q.map f
        rw [inclusion_map_Q, approximation_map_Q, ← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (sourceWeak F W).Q.map ((restrictionCounit F T ε i).naturality f) }

@[simp]
theorem sourceCounit_app_Q (i : ι) (X : C) :
    (sourceCounit F W T ε hT i).app ((sourceWeak F W).Q.obj X) =
      (sourceWeak F W).Q.map ((restrictionCounit F T ε i).app X) := by
  simp [sourceCounit, Localization.Construction.NatTransExtension.app_eq]

/-- The original counit also descends to the ambient localization. -/
def targetCounit (i : ι) : approximation F W T hT i ⋙ inclusion F W ⟶ 𝟭 W.Localization :=
  Localization.Construction.natTransExtension
    { app X := W.Q.map ((ε i).app X)
      naturality := by
        intro X Y f
        change (inclusion F W).map ((approximation F W T hT i).map (W.Q.map f)) ≫
          W.Q.map ((ε i).app Y) = W.Q.map ((ε i).app X) ≫ W.Q.map f
        rw [approximation_map_Q, inclusion_map_Q, ← Functor.map_comp, ← Functor.map_comp]
        exact congrArg W.Q.map ((ε i).naturality f) }

omit [F.Full] [F.Faithful] in
@[simp]
theorem targetCounit_app_Q (i : ι) (X : D) :
    (targetCounit F W T ε hT i).app (W.Q.obj X) = W.Q.map ((ε i).app X) := by
  simp [targetCounit, Localization.Construction.NatTransExtension.app_eq]

/-- Compatibility is inherited from the actual full inclusion, not postulated after localization. -/
@[simp]
theorem map_sourceCounit_app (i : ι) (X : (sourceWeak F W).Localization) :
    (inclusion F W).map ((sourceCounit F W T ε hT i).app X) =
      (targetCounit F W T ε hT i).app ((inclusion F W).obj X) := by
  obtain ⟨X, rfl⟩ := (Localization.Construction.objEquiv (sourceWeak F W)).surjective X
  change (inclusion F W).map ((sourceCounit F W T ε hT i).app ((sourceWeak F W).Q.obj X)) =
    (targetCounit F W T ε hT i).app (W.Q.obj (F.obj X))
  simp

variable (hε : ∀ X Y : C, ∃ i, W ((ε i).app (F.obj X)) ∧ W ((ε i).app (F.obj Y)))

include hε in
/-- Every pair of localized source objects admits a genuinely invertible approximation counit. -/
theorem exists_isIso_sourceCounit (X Y : (sourceWeak F W).Localization) :
    ∃ i, IsIso ((sourceCounit F W T ε hT i).app X) ∧
      IsIso ((sourceCounit F W T ε hT i).app Y) := by
  obtain ⟨X, rfl⟩ := (Localization.Construction.objEquiv (sourceWeak F W)).surjective X
  obtain ⟨Y, rfl⟩ := (Localization.Construction.objEquiv (sourceWeak F W)).surjective Y
  obtain ⟨i, hX, hY⟩ := hε X Y
  refine ⟨i, ?_, ?_⟩
  · change IsIso ((sourceCounit F W T ε hT i).app ((sourceWeak F W).Q.obj X))
    rw [sourceCounit_app_Q]
    apply (sourceWeak F W).Q_inverts
    change W (F.map ((restrictionCounit F T ε i).app X))
    simpa using hX
  · change IsIso ((sourceCounit F W T ε hT i).app ((sourceWeak F W).Q.obj Y))
    rw [sourceCounit_app_Q]
    apply (sourceWeak F W).Q_inverts
    change W (F.map ((restrictionCounit F T ε i).app Y))
    simpa using hY

include hε in
/-- An inclusion with actual weak-equivalence-preserving approximations, eventually invertible
on every pair of source objects, becomes fully faithful after localization. -/
def fullyFaithful : (inclusion F W).FullyFaithful := by
  let : (inclusion F W).Faithful :=
    { map_injective := by
        intro X Y f g h
        obtain ⟨i, hX, hY⟩ := exists_isIso_sourceCounit F W T ε hT hε X Y
        apply (cancel_epi ((sourceCounit F W T ε hT i).app X)).mp
        have hf := (sourceCounit F W T ε hT i).naturality f
        have hg := (sourceCounit F W T ε hT i).naturality g
        dsimp only [Functor.id_map, Functor.comp_map] at hf hg
        rw [← hf, ← hg, h] }
  let : (inclusion F W).Full :=
    { map_surjective := by
        intro X Y f
        obtain ⟨i, hX, hY⟩ := exists_isIso_sourceCounit F W T ε hT hε X Y
        refine ⟨inv ((sourceCounit F W T ε hT i).app X) ≫
          (approximation F W T hT i).map f ≫ (sourceCounit F W T ε hT i).app Y, ?_⟩
        simp only [Functor.map_comp, Functor.map_inv, map_sourceCounit_app]
        have h := (targetCounit F W T ε hT i).naturality f
        dsimp only [Functor.id_map, Functor.comp_map] at h
        rw [h]
        have : IsIso ((targetCounit F W T ε hT i).app ((inclusion F W).obj X)) := by
          rw [← map_sourceCounit_app]
          infer_instance
        simp }
  exact Functor.FullyFaithful.ofFullyFaithful _

end CategoryTheory.Localization.Restriction
