/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Existence.InjectiveStep.Quotient
public import Aglib.Algebra.Homology.MappingCocone.Map
public import Aglib.Algebra.Homology.MappingCone.ShortExact

/-!
# Functoriality of the original quotient-cocone injective step

The target functor is the native mapping-cone functor of the original quotient
projection, followed by the native shift. Its unit is the original cocone lift.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.IsGrothendieckAbelian

namespace CochainComplex

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- The actual quotient projections form a natural transformation. -/
def injectiveStepQuotientProjection :
    injectiveStepContractible C ⟶ injectiveStepQuotient C where
  app K := injectiveStepQuotientπ K
  naturality {_K _L} f := (coker.π (CochainComplex C ℤ)).naturality ((injectiveStepArrow C).map f)

/-- The original quotient-cocone construction, as a genuine functor. -/
def injectiveStepFunctor : CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  mappingConeNatTransFunctor (injectiveStepQuotientProjection C) ⋙
    CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)

variable {C}

@[reassoc]
lemma injectiveStepCoconeι_naturality {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    f ≫ injectiveStepCoconeι L =
      injectiveStepCoconeι K ≫ (injectiveStepFunctor C).map f :=
  mappingCocone.lift_zero_naturality
    (injectiveStepQuotientπ K) (injectiveStepQuotientπ L)
    (injectiveStepContractibleι K) (injectiveStepContractibleι L)
    (injectiveStepQuotient_condition K) (injectiveStepQuotient_condition L)
    f ((injectiveStepContractible C).map f) ((injectiveStepQuotient C).map f)
    ((injectiveStepQuotientProjection C).naturality f).symm
    (injectiveStepContractibleι_naturality f)

/-- The original natural monomorphism for the injective-factor successor step. -/
def injectiveStepUnit : 𝟭 (CochainComplex C ℤ) ⟶ injectiveStepFunctor C where
  app := injectiveStepCoconeι
  naturality {_K _L} f := injectiveStepCoconeι_naturality f

instance injectiveStepUnit_mono (K : CochainComplex C ℤ) :
    Mono ((injectiveStepUnit (C := C)).app K) :=
  inferInstanceAs (Mono (injectiveStepCoconeι K))

end CochainComplex
