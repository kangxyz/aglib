/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.InjectiveStep.QuasiIso
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.KillSmallMaps.Functor

/-!
# The actual combined replacement successor

First take the genuine injective-factor step, then the genuine all-maps
attachment. The original composite unit has both required properties. This is
only a successor; no final-stage injectivity or K-injectivity is asserted.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {ι : Type w} (A : ι → CochainComplex C ℤ)

/-- The actual injective-factor step followed by the all-maps attachment. -/
abbrev replacementStepFunctor : CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  injectiveStepFunctor C ⋙ killAllMapsFunctor A

set_option backward.isDefEq.respectTransparency false in
/-- The original composite natural unit. -/
def replacementStepUnit : 𝟭 (CochainComplex C ℤ) ⟶ replacementStepFunctor A where
  app K := (injectiveStepUnit (C := C)).app K ≫
    (killAllMapsUnit A).app ((injectiveStepFunctor C).obj K)
  naturality K L f := by
    have h₁ : f ≫ (injectiveStepUnit (C := C)).app L =
        (injectiveStepUnit (C := C)).app K ≫ (injectiveStepFunctor C).map f :=
      (injectiveStepUnit (C := C)).naturality f
    have h₂ : (injectiveStepFunctor C).map f ≫
        (killAllMapsUnit A).app ((injectiveStepFunctor C).obj L) =
        (killAllMapsUnit A).app ((injectiveStepFunctor C).obj K) ≫
          (killAllMapsFunctor A).map ((injectiveStepFunctor C).map f) :=
      (killAllMapsUnit A).naturality ((injectiveStepFunctor C).map f)
    change f ≫ ((injectiveStepUnit (C := C)).app L ≫ _) =
      ((injectiveStepUnit (C := C)).app K ≫ _) ≫
        (killAllMapsFunctor A).map ((injectiveStepFunctor C).map f)
    rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]

instance replacementStepUnit_mono (K : CochainComplex C ℤ) :
    Mono ((replacementStepUnit A).app K) := by
  change Mono ((injectiveStepUnit (C := C)).app K ≫
    (killAllMapsUnit A).app ((injectiveStepFunctor C).obj K))
  infer_instance

/-- The original composite unit is a quasi-isomorphism for acyclic tests. -/
lemma replacementStepUnit_quasiIso (hA : ∀ i, (A i).Acyclic) (K : CochainComplex C ℤ) :
    QuasiIso ((replacementStepUnit A).app K) := by
  have := killAllMapsUnit_quasiIso A hA ((injectiveStepFunctor C).obj K)
  change QuasiIso ((injectiveStepUnit (C := C)).app K ≫
    (killAllMapsUnit A).app ((injectiveStepFunctor C).obj K))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Every original test map becomes nullhomotopic after the original unit. -/
def replacementStepHomotopy (K : CochainComplex C ℤ) (i : ι) (f : A i ⟶ K) :
    Homotopy (f ≫ (replacementStepUnit A).app K) 0 := by
  change Homotopy
    (f ≫ ((injectiveStepUnit (C := C)).app K ≫
      killAllMapsι A ((injectiveStepFunctor C).obj K))) 0
  rw [← Category.assoc]
  exact killAllMapsHomotopy A ((injectiveStepFunctor C).obj K) i
      (f ≫ (injectiveStepUnit (C := C)).app K)

/-- Each original component still factors through an actual injective subobject
of the combined successor. -/
lemma replacementStepUnit_injectiveFactor (K : CochainComplex C ℤ) (n : ℤ) :
    ∃ (I : C) (_ : Injective I) (a : K.X n ⟶ I)
      (b : I ⟶ ((replacementStepFunctor A).obj K).X n), Mono b ∧
        ((replacementStepUnit A).app K).f n = a ≫ b := by
  obtain ⟨I, hI, a, b, hb, he⟩ := injectiveStepUnit_injectiveFactor K n
  have : Mono b := hb
  refine ⟨I, hI, a,
    b ≫ ((killAllMapsUnit A).app ((injectiveStepFunctor C).obj K)).f n,
    inferInstance, ?_⟩
  change ((injectiveStepUnit (C := C)).app K).f n ≫ _ = _
  rw [he, Category.assoc]

end CochainComplex
