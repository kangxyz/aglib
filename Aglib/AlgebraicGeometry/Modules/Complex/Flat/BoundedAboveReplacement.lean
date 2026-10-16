/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Generators
public import Aglib.AlgebraicGeometry.Modules.Flat.ProjectivePresheaves
public import Aglib.Algebra.Homology.CochainComplex.BoundedAbove.ProjectiveReplacement
public import Aglib.AlgebraicGeometry.Modules.Complex.Sheafification


/-!
# Actual flat replacements of bounded-above sheaf complexes

For any scheme, a bounded-above complex of arbitrary module sheaves has a
bounded-above stalkwise-flat quasi-isomorphic replacement with exactly the same
upper bound. We resolve the actual underlying module-presheaf complex by
projectives, apply exact sheafification, and use its actual counit isomorphism.
No quasicoherence, affineness, flat morphism, or replacement existence hypothesis
is used. No functorial choice or derived-localization descent is asserted here.
-/
/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Sheaf/BoundedFlatReplacement.lean`.
SHA-256: `89f8b7540cf9edfc643c2cf03ce76ad70df2b026f31822b17721c6958f85f897`.
Selected source lines: 1–101.
Actual source objects, maps, hypotheses and independent universes are preserved.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite HomologicalComplex
namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] Abelian.hasFiniteBiproducts

/-- Every genuinely bounded-above complex of arbitrary module sheaves admits an
actual bounded-above stalkwise-flat replacement, with the same upper bound. -/
theorem exists_boundedAbove_flat_complex_replacement (X : Scheme.{u})
    (K : CochainComplex X.Modules ℤ) (b : ℤ) [K.IsStrictlyLE b] :
    ∃ (P : CochainComplex X.Modules ℤ) (p : P ⟶ K), QuasiIso p ∧
      (∀ n, stalkwiseFlat X (P.X n)) ∧ P.IsStrictlyLE b := by
  let R := SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)
  let A := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let : A.Additive := SheafOfModulesOfCommRing.associatedSheaf_additive X.sheaf
  let K₀ : CochainComplex (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) ℤ :=
    (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have : K₀.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact R.map_isZero (K.isZero_of_isStrictlyLE b n hn)
  obtain ⟨P₀, p₀, hp₀, hP₀, hb⟩ :=
    CochainComplex.exists_boundedAbove_projective_replacement K₀ b
  let P := (A.mapHomologicalComplex (ComplexShape.up ℤ)).obj P₀
  let p : P ⟶ K := (A.mapHomologicalComplex (ComplexShape.up ℤ)).map p₀ ≫
    (sheafificationComplexCounitIso X K).hom
  refine ⟨P, p, ?_, ?_, ?_⟩
  · let : QuasiIso p₀ := hp₀
    have : A.PreservesHomology := by dsimp [A]; infer_instance
    have : QuasiIso ((A.mapHomologicalComplex (ComplexShape.up ℤ)).map p₀) := by
      infer_instance
    dsimp [p]
    infer_instance
  · intro n
    exact stalkwiseFlat_sheafify_projective X (P₀.X n)
  · rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact A.map_isZero (P₀.isZero_of_isStrictlyLE b n hn)

end AlgebraicGeometry.Scheme.Modules
