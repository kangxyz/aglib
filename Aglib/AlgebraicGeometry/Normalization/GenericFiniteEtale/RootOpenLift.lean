/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.OpenLift
public import Aglib.RingTheory.Kummer.RootComplementBaseChange

/-! # The original root-stage lift on the original complement

Restrict the genuine descended lift into the unchanged native normalization.
The original localization square and open-recovery pullback construct the
lift to the original covering source. There is no normalization/base-change
comparison, dominance premise for the lift, or extra root model.
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

/-- The complete original root-complement structural square on spectra. -/
theorem rootComplementBaseChange_spec_square :
    Spec.algebraMap TB VB ≫
        Spec.map (CommRingCat.ofHom (rootBaseChangeHom B N f).toRingHom) =
      Spec.map (CommRingCat.ofHom (rootComplementBaseChangeHom B N f)) ≫
        Spec.algebraMap T V := by
  simp only [Spec.algebraMap, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (rootComplementBaseChangeHom_comp B N f).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual descended root lift gives an original open-cover lift, with
both the normalization inclusion and the original complement map retained. -/
theorem exists_rootOpenLift :
    let T₀ := RootAlgebra N f
    let V₀ := Localization.Away (AdjoinRoot.root (rootPolynomial N f))
    ∀ [IsIntegral (Spec (.of T₀))] [Nonempty (Spec (.of V₀))]
      [∀ t : Spec (.of T₀), IsIntegrallyClosed ((Spec (.of T₀)).presheaf.stalk t)]
      {E : Scheme.{u}} (p : E ⟶ Spec (.of V₀)) [IsFinite p] [Etale p]
      (a : Spec (.of TB) ⟶ (genericMap (X := Spec (.of T₀)) (U := Spec (.of V₀)) (E := E)
      (Spec.algebraMap T₀ V₀) p).normalization)
    (_ha : a ≫ (genericMap (X := Spec (.of T₀)) (U := Spec (.of V₀)) (E := E)
      (Spec.algebraMap T₀ V₀) p).fromNormalization =
      Spec.map (CommRingCat.ofHom (rootBaseChangeHom B N f).toRingHom)),
    ∃ b : Spec (.of VB) ⟶ E,
      b ≫ inclusion (Spec.algebraMap T₀ V₀) p = Spec.algebraMap TB VB ≫ a ∧
      b ≫ p = Spec.map (CommRingCat.ofHom (rootComplementBaseChangeHom B N f)) := by
  dsimp only
  intro hT hV hn E p hp he a ha
  apply exists_openLift (Spec.algebraMap T V) p a (Spec.algebraMap TB VB)
    (Spec.map (CommRingCat.ofHom (rootComplementBaseChangeHom B N f)))
  rw [Category.assoc, ha]
  exact rootComplementBaseChange_spec_square R B N f

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
