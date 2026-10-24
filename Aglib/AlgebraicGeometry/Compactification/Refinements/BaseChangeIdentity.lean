/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Refinements.BaseChange
public import Aglib.AlgebraicGeometry.Compactification.Refinements.SourceIso
public import Aglib.AlgebraicGeometry.Compactification.Refinements.ClosedAmbient
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Identity normalized base change

The source identification is the native isomorphism given by the second
projection of the pullback along the identity. The ambient comparison retains
the original normalization followed by the original second projection.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom.DenseCompactification

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The actual identity-base-change source isomorphism. -/
def identitySourceIso : pullback (𝟙 S) f ≅ X := asIso (pullback.snd (𝟙 S) f)

@[reassoc (attr := simp)]
lemma identitySourceIso_hom_f :
    (identitySourceIso f).hom ≫ f = pullback.fst (𝟙 S) f := by
  change pullback.snd (𝟙 S) f ≫ f = pullback.fst (𝟙 S) f
  exact pullback.condition.symm.trans (Category.comp_id _)

variable [QuasiCompact f]

/-- The original dense compactification, on the literal identity-pullback source. -/
def identitySourceTransport :
    DenseCompactification f ⥤ DenseCompactification (pullback.fst (𝟙 S) f) :=
  sourceIso _ (identitySourceIso f) (identitySourceIso_hom_f f)

/-- The actual identity normalization map into the original ambient. -/
def identityNormalization (C : DenseCompactification f) :
    ((baseChange (𝟙 S)).obj C).Xbar ⟶ C.Xbar :=
  baseChangeNormalization (𝟙 S) C ≫ pullback.snd (𝟙 S) C.p

instance identityNormalization_isClosedImmersion (C : DenseCompactification f) :
    IsClosedImmersion (identityNormalization f C) :=
  inferInstanceAs (IsClosedImmersion
    (baseChangeNormalization (𝟙 S) C ≫ pullback.snd (𝟙 S) C.p))

lemma identityNormalization_open (C : DenseCompactification f) :
    ((baseChange (𝟙 S)).obj C).j ≫ identityNormalization f C =
      ((identitySourceTransport f).obj C).j ≫ 𝟙 C.Xbar :=
  (baseChange_j_normalization_snd (𝟙 S) C).trans (Category.comp_id _).symm

lemma identityNormalization_p (C : DenseCompactification f) :
    identityNormalization f C ≫ C.p = ((baseChange (𝟙 S)).obj C).p := by
  calc
    _ = baseChangeNormalization (𝟙 S) C ≫ (pullback.snd (𝟙 S) C.p ≫ C.p) :=
      Category.assoc _ _ _
    _ = baseChangeNormalization (𝟙 S) C ≫ pullback.fst (𝟙 S) C.p :=
      congrArg (fun k => baseChangeNormalization (𝟙 S) C ≫ k)
        (pullback.condition.symm.trans (Category.comp_id _))
    _ = _ := baseChangeNormalization_fst (𝟙 S) C

/-- The identity comparison is an actual isomorphism of dense compactifications. -/
def baseChangeIdentityIso (C : DenseCompactification f) :
    (baseChange (𝟙 S)).obj C ≅ (identitySourceTransport f).obj C :=
  @closedAmbientIso _ _ C.Xbar _ _ _ C.p (identityNormalization f C) (𝟙 C.Xbar)
    (inferInstanceAs (IsClosedImmersion (𝟙 C.Xbar)))
    (identityNormalization_open f C) (identityNormalization_p f C) (Category.id_comp _)
    (identityNormalization_isClosedImmersion f C)

/-- Identity normalized base change is naturally identified with original source transport. -/
def baseChangeIdentity : baseChange (𝟙 S) ≅ identitySourceTransport f :=
  NatIso.ofComponents (baseChangeIdentityIso f) (fun _ => Subsingleton.elim _ _)

/-- The identity comparison retains the original ambient projection exactly. -/
lemma baseChangeIdentityIso_hom (C : DenseCompactification f) :
    (baseChangeIdentityIso f C).hom.hom =
      baseChangeNormalization (𝟙 S) C ≫ pullback.snd (𝟙 S) C.p := by
  have h : (baseChangeIdentityIso f C).hom.hom ≫ (𝟙 C.Xbar) =
      identityNormalization f C :=
    @closedAmbientIso_hom_comp (pullback (𝟙 S) f) S C.Xbar (pullback.fst (𝟙 S) f)
      ((baseChange (𝟙 S)).obj C) ((identitySourceTransport f).obj C) C.p
      (identityNormalization f C) (𝟙 C.Xbar)
      (inferInstanceAs (IsClosedImmersion (𝟙 C.Xbar)))
      (identityNormalization_open f C) (identityNormalization_p f C) (Category.id_comp C.p)
      (identityNormalization_isClosedImmersion f C)
  exact (Category.comp_id _).symm.trans h

end AlgebraicGeometry.Scheme.Hom.DenseCompactification
