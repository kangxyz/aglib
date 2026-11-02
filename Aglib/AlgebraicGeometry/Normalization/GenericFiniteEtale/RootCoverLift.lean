/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.RootOpenLift
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange

/-! # The original cover at the same coefficient stage

The genuine lift into the original root normalization restricts to the original
open cover and then lifts to its ordinary coefficient base change. Both lifts
retain their original projections. Normalization is never base changed here.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Algebra.Kummer

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] (N : ℕ) (f : R)

local notation "T" => RootAlgebra N f
local notation "TB" => RootAlgebra N (algebraMap R B f)
local notation "V" => Localization.Away (AdjoinRoot.root (rootPolynomial N f))
local notation "VB" => Localization.Away (AdjoinRoot.root (rootPolynomial N (algebraMap R B f)))
local notation "U" => Localization.Away f
local notation "UB" => Localization.Away (algebraMap R B f)
local notation "g" => Spec.map (CommRingCat.ofHom (rootComplementHom N f))
local notation "u" => Spec.map (CommRingCat.ofHom (parameterComplementBaseChangeHom B f))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Ordinary base change constructs the open lift at the same original stage.
No integrality or connectedness of the whole pulled-back cover is assumed. -/
theorem exists_rootStageCoverLift
    [IsIntegral (Spec (.of T))] [Nonempty (Spec (.of V))]
    [∀ t : Spec (.of T), IsIntegrallyClosed ((Spec (.of T)).presheaf.stalk t)]
    (Y : FiniteEtale (Spec (.of U)))
    (a : Spec (.of TB) ⟶ (genericMap (Spec.algebraMap T V)
      ((baseChange g).obj Y).obj.hom).normalization)
    (ha : a ≫ (genericMap (Spec.algebraMap T V) ((baseChange g).obj Y).obj.hom).fromNormalization =
      Spec.map (CommRingCat.ofHom (rootBaseChangeHom B N f).toRingHom)) :
    ∃ (b : Spec (.of VB) ⟶ ((baseChange g).obj Y).obj.left)
      (t : Spec (.of VB) ⟶ ((baseChange u).obj Y).obj.left),
      b ≫ inclusion (Spec.algebraMap T V) ((baseChange g).obj Y).obj.hom =
        Spec.algebraMap TB VB ≫ a ∧
      b ≫ ((baseChange g).obj Y).obj.hom =
        Spec.map (CommRingCat.ofHom (rootComplementBaseChangeHom B N f)) ∧
      t ≫ ((baseChange u).obj Y).obj.hom =
        Spec.map (CommRingCat.ofHom (rootComplementHom N (algebraMap R B f))) ∧
      t ≫ pullback.fst Y.obj.hom u = b ≫ pullback.fst Y.obj.hom g := by
  obtain ⟨b, hb, hbp⟩ := exists_rootOpenLift R B N f ((baseChange g).obj Y).obj.hom a ha
  have hsq : Spec.map (CommRingCat.ofHom (rootComplementBaseChangeHom B N f)) ≫ g =
      Spec.map (CommRingCat.ofHom (rootComplementHom N (algebraMap R B f))) ≫ u := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (rootComplementBaseChangeHom_comp_rootComplementHom B N f)
  have h : (b ≫ pullback.fst Y.obj.hom g) ≫ Y.obj.hom =
      Spec.map (CommRingCat.ofHom (rootComplementHom N (algebraMap R B f))) ≫ u := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (b ≫ ((baseChange g).obj Y).obj.hom) ≫ g = _
    rw [hbp, hsq]
  exact ⟨b, pullback.lift (b ≫ pullback.fst Y.obj.hom g)
      (Spec.map (CommRingCat.ofHom (rootComplementHom N (algebraMap R B f)))) h,
    hb, hbp, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
