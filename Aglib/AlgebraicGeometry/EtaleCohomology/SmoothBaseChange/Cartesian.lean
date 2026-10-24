/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.EtaleDerived
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.PullbackIsomorphism
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.HorizontalComposition

/-! # Canonical étale exchange for arbitrary cartesian squares

The actual pullback-corner isomorphism, native horizontal pasting and original
mate conjugation transport the literal-pullback theorem. The original derived
and higher exchange transformations are unchanged. The four displayed derived
category universes remain independent; the auxiliary pullback uses its standard
category internally.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u dX dS dX' dS'

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{dX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{dS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : IsPullback g' f' f g)

/-- The original D+ étale exchange for any specified cartesian square. -/
theorem derivedBaseChangeMap_etale_isIso_of_isPullback [Etale g] :
    IsIso (derivedBaseChangeMap f f' g g' h.w.symm) := by
  let : HasDerivedCategory (AbelianSheaf.{u, u + 1} (pullback g f)) :=
    HasDerivedCategory.standard _
  let e : X' ≅ pullback g f := h.flip.isoPullback
  have he₁ : e.hom ≫ pullback.fst g f = f' := h.flip.isoPullback_hom_fst
  have he₂ : e.hom ≫ pullback.snd g f = g' := h.flip.isoPullback_hom_snd
  have h₂ : f' ≫ 𝟙 S' = e.hom ≫ pullback.fst g f := by simpa using he₁.symm
  have hc : f' ≫ (𝟙 S' ≫ g) = (e.hom ≫ pullback.snd g f) ≫ f := by
    simpa only [Category.id_comp, he₂] using h.w.symm
  let : IsIso (derivedBaseChangeMap f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition) := derivedBaseChangeMap_etale_isIso f g
  let : IsIso (derivedBaseChangeMap (pullback.fst g f) f' (𝟙 S') e.hom h₂) :=
    derivedBaseChangeMap_isIso_of_horizontal_isIso _ _ _ _ h₂
  have hi := derivedBaseChangeMap_isIso_hComp f (pullback.fst g f) f' g (𝟙 S')
    (pullback.snd g f) e.hom pullback.condition h₂ hc
  exact (derivedBaseChangeMap_isIso_congr f f' (𝟙 S' ≫ g) g
    (e.hom ≫ pullback.snd g f) g' hc h.w.symm (Category.id_comp g) he₂).mp hi

/-- Every original higher étale exchange for any specified cartesian square. -/
theorem higherBaseChangeMap_etale_isIso_of_isPullback [Etale g] (q : ℕ) :
    IsIso (higherBaseChangeMap f f' g g' h.w.symm q) := by
  let := derivedBaseChangeMap_etale_isIso_of_isPullback f f' g g' h
  rw [higherBaseChangeMap_eq_transport]
  infer_instance

/-- Relative-dimension-zero smooth comparison for an arbitrary cartesian square. -/
theorem derivedBaseChangeMap_smoothOfRelativeDimension_zero_isIso_of_isPullback
    [SmoothOfRelativeDimension 0 g] :
    IsIso (derivedBaseChangeMap f f' g g' h.w.symm) := by
  let : Etale g := (AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero g).mpr
    inferInstance
  exact derivedBaseChangeMap_etale_isIso_of_isPullback f f' g g' h

/-- All-degree relative-dimension-zero comparison for an arbitrary cartesian square. -/
theorem higherBaseChangeMap_smoothOfRelativeDimension_zero_isIso_of_isPullback
    [SmoothOfRelativeDimension 0 g] (q : ℕ) :
    IsIso (higherBaseChangeMap f f' g g' h.w.symm q) := by
  let : Etale g := (AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero g).mpr
    inferInstance
  exact higherBaseChangeMap_etale_isIso_of_isPullback f f' g g' h q

end AlgebraicGeometry.Scheme.EtaleCohomology
