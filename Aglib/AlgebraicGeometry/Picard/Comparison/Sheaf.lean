/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Comparison.LocallyTrivial
public import Aglib.AlgebraicGeometry.Picard.Comparison.Rigidified

/-!
# Separatedness of the relative Picard functor, and the gluing premise

Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Thm 2.5, p. 18, and
[Stacks 0B9N](https://stacks.math.columbia.edu/tag/0B9N).

* `isSeparated_relativePicardFunctor_of_isProper_of_flat_of_geometricallyIntegral`: for `S` locally
  Noetherian and `p` proper, flat, with geometrically integral fibres, `P_{X/S}` (as a presheaf of
  types) is separated for the fppf topology, because it injects into its sheafification (the fppf
  comparison map of Thm 2.5(1),
  `toFppfPicardSheaf_app_injective_of_isProper_of_flat_of_geometricallyIntegral`); hence so is the
  rigidified functor
  (`isSeparated_rigidifiedPicardFunctor_of_isProper_of_flat_of_geometricallyIntegral`, through
  Lemma 2.9, `rigidifiedRelativeIso`). Separatedness fails without these hypotheses: for the fold
  map `S ⊔ S ⟶ S`, `P_{X/S}(T) ≅ Pic(T)`.
* `RigidifiedGluing p o ho`: every compatible family of isomorphism classes of rigidified pairs
  along an fppf covering sieve has an amalgamation (the gluing step of Stacks 0B9N). It is proved
  in [Isomorphism](Isomorphism.lean) (`rigidifiedGluing_of_isIso_c`), which derives the sheaf
  property and the comparison isomorphism with a global section.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.RelativePicard

universe u

variable {S X : Scheme.{u}} (p : X ⟶ S)

/-- **Separatedness of `P_{X/S}`**, from the injectivity of the fppf comparison map (Kleiman,
Thm 2.5(1)). For `S` locally Noetherian and `p` proper, flat, with geometrically integral fibres,
the relative Picard functor, as a presheaf of types, is separated for the fppf topology on
`Over S`. -/
theorem isSeparated_relativePicardFunctor_of_isProper_of_flat_of_geometricallyIntegral
    [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] :
    Presieve.IsSeparated (Scheme.fppfTopology.over S)
      (relativePicardFunctor p ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) := by
  intro T R hR x t₁ t₂ h₁ h₂
  have hsheaf : Presieve.IsSheaf (Scheme.fppfTopology.over S)
      ((fppfPicardSheaf p).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((sheafCompose (Scheme.fppfTopology.over S)
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj (fppfPicardSheaf p)).property
  let φ := Functor.whiskerRight (toFppfPicardSheaf p) (CategoryTheory.forget AddCommGrpCat.{u + 1})
  have h := (hsheaf R hR).isSeparatedFor (x.map φ) _ _ (h₁.map φ) (h₂.map φ)
  exact toFppfPicardSheaf_app_injective_of_isProper_of_flat_of_geometricallyIntegral p (op T) h

variable (o : S ⟶ X) (ho : o ≫ p = 𝟙 S)

/-- **Separatedness of the rigidified functor.** Under the hypotheses of
`isSeparated_relativePicardFunctor_of_isProper_of_flat_of_geometricallyIntegral`, through
Lemma 2.9 (`rigidifiedRelativeIso`). -/
theorem isSeparated_rigidifiedPicardFunctor_of_isProper_of_flat_of_geometricallyIntegral
    [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p] :
    Presieve.IsSeparated (Scheme.fppfTopology.over S) (rigidifiedPicardFunctor p o ho) := by
  intro T R hR x t₁ t₂ h₁ h₂
  let φ := (rigidifiedRelativeIso p o ho).hom
  have h := isSeparated_relativePicardFunctor_of_isProper_of_flat_of_geometricallyIntegral p R hR
    (x.map φ) _ _ (h₁.map φ) (h₂.map φ)
  exact ((rigidifiedRelativeIso p o ho).app (op T)).toEquiv.injective h

/-- **The gluing statement of Stacks 0B9N.** Every compatible family of isomorphism classes of
rigidified pairs along an fppf covering sieve of `T` in `Over S` has an amalgamation. Proved in
[Isomorphism](Isomorphism.lean) (`rigidifiedGluing_of_isIso_c`). -/
def RigidifiedGluing : Prop :=
  ∀ ⦃T : Over S⦄ (R : Sieve T), R ∈ (Scheme.fppfTopology.over S) T →
    ∀ x : Presieve.FamilyOfElements (rigidifiedPicardFunctor p o ho) R.arrows, x.Compatible →
      ∃ t, x.IsAmalgamation t

end AlgebraicGeometry.Scheme.RelativePicard
