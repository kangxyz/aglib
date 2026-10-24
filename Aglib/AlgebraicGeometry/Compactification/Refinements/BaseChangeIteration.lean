/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.BaseChangeIterationAmbient
public import Aglib.AlgebraicGeometry.Compactification.Refinements.SourceIso
public import Aglib.AlgebraicGeometry.Compactification.Refinements.ClosedAmbient

/-!
# Iterated normalized base change

Compare the two dense closed ambients inside the original single raw pullback,
after transport along the native source-pullback associator. The comparison
is an actual natural isomorphism, normalized by its original inclusion map.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom.DenseCompactification

variable {X S T U : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (b : T ⟶ S) (c : U ⟶ T)

/-- Identify the single-pullback source with the literal iterated-pullback source. -/
def iteratedSourceTransport : DenseCompactification (pullback.fst (c ≫ b) f) ⥤
    DenseCompactification (pullback.fst c (pullback.fst b f)) :=
  sourceIso _ (iteratedSourceIso (f := f) b c) (iteratedSourceIso_hom_fst b c)

variable (C : DenseCompactification f)

/-- Both closed ambient embeddings agree on the original source after native transport. -/
lemma iteratedNormalization_sourceTransport :
    ((baseChange b ⋙ baseChange c).obj C).j ≫ iteratedNormalization b c C =
      ((baseChange (c ≫ b) ⋙ iteratedSourceTransport b c).obj C).j ≫
        baseChangeNormalization (c ≫ b) C := by
  change ((baseChange b ⋙ baseChange c).obj C).j ≫ iteratedNormalization b c C =
    ((iteratedSourceIso (f := f) b c).hom ≫ ((baseChange (c ≫ b)).obj C).j) ≫
      baseChangeNormalization (c ≫ b) C
  exact (iteratedNormalization_open b c C).trans
    ((congrArg (fun k : pullback (c ≫ b) f ⟶ pullback (c ≫ b) C.p =>
        (iteratedSourceIso (f := f) b c).hom ≫ k)
      (baseChange_j_normalization (c ≫ b) C).symm).trans
        (Category.assoc (iteratedSourceIso (f := f) b c).hom
          ((baseChange (c ≫ b)).obj C).j (baseChangeNormalization (c ≫ b) C)).symm)

/-- The actual comparison of iterated and single normalized compactifications. -/
def baseChangeIterationIso :
    (baseChange b ⋙ baseChange c).obj C ≅
      (baseChange (c ≫ b) ⋙ iteratedSourceTransport b c).obj C :=
  @closedAmbientIso _ _ (pullback (c ≫ b) C.p) _ _ _ (pullback.fst (c ≫ b) C.p)
    (iteratedNormalization b c C) (baseChangeNormalization (c ≫ b) C)
    (baseChangeNormalization_isClosedImmersion (c ≫ b) C)
    (iteratedNormalization_sourceTransport b c C) (iteratedNormalization_fst b c C)
    (baseChangeNormalization_fst (c ≫ b) C) (iteratedNormalization_isClosedImmersion b c C)

/-- The comparison retains the original single-ambient inclusion equation. -/
@[simp, reassoc]
lemma baseChangeIterationIso_hom_normalization :
    (baseChangeIterationIso b c C).hom.hom ≫ baseChangeNormalization (c ≫ b) C =
      iteratedNormalization b c C :=
  @closedAmbientIso_hom_comp (pullback c (pullback.fst b f)) U
    (pullback (c ≫ b) C.p) (pullback.fst c (pullback.fst b f))
    ((baseChange b ⋙ baseChange c).obj C)
    ((baseChange (c ≫ b) ⋙ iteratedSourceTransport b c).obj C)
    (pullback.fst (c ≫ b) C.p) (iteratedNormalization b c C)
    (baseChangeNormalization (c ≫ b) C)
    (baseChangeNormalization_isClosedImmersion (c ≫ b) C)
    (iteratedNormalization_sourceTransport b c C) (iteratedNormalization_fst b c C)
    (baseChangeNormalization_fst (c ≫ b) C) (iteratedNormalization_isClosedImmersion b c C)

/-- Iterated normalized base change is natural in actual compactification refinements. -/
def baseChangeIteration : baseChange b ⋙ baseChange c ≅
    baseChange (c ≫ b) ⋙ iteratedSourceTransport (f := f) b c :=
  NatIso.ofComponents (baseChangeIterationIso b c) (fun _ => Subsingleton.elim _ _)

end AlgebraicGeometry.Scheme.Hom.DenseCompactification
