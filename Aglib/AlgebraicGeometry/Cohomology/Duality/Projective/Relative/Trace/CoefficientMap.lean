/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.AffineTrace

/-!
# The original coefficient adjunct with a supplied open immersion proof

The coefficient map chooses its open immersion proof internally. Transport
the complete adjunct equation by proof irrelevance before specializing it.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u
namespace AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace

/-- Normalize both object heads before substituting a concrete coefficient functor. -/
def coefficientRawComponent
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (W : E ⥤ C) (U : E ⥤ F) (V : F ⥤ D) (L : C ⥤ D)
    (η : W ⋙ L ⟶ U ⋙ V) (N : E) :
    L.obj (W.obj N) ⟶ V.obj (U.obj N) :=
  η.app N

/-- The same original adjunct, with the iterated object head fixed generically. -/
def coefficientRawAdjunct
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (W : E ⥤ C) (U : E ⥤ F) (V : F ⥤ D) (T : D ⥤ C)
    (N : E) (b : W.obj N ⟶ T.obj ((U ⋙ V).obj N)) :
    W.obj N ⟶ T.obj (V.obj (U.obj N)) :=
  b

/-- The entire coefficient-adjunction equation over opaque functors. -/
def coefficientAdjunctionEquation
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (W : E ⥤ C) (U : E ⥤ F) (V : F ⥤ D) (L : C ⥤ D) (T : D ⥤ C)
    (adj : L ⊣ T) (η : W ⋙ L ⟶ U ⋙ V) (N : E)
    (b : W.obj N ⟶ T.obj ((U ⋙ V).obj N)) : Prop :=
  b = adj.homEquiv (W.obj N) ((U ⋙ V).obj N) (η.app N)

/-- The original native component equation implies the same normalized equation. -/
theorem coefficientAdjunctionEquation_of_native
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (W : E ⥤ C) (U : E ⥤ F) (V : F ⥤ D) (L : C ⥤ D) (T : D ⥤ C)
    (adj : L ⊣ T) (η : W ⋙ L ⟶ U ⋙ V) (N : E)
    (b : W.obj N ⟶ T.obj ((U ⋙ V).obj N))
    (h : b = adj.homEquiv (W.obj N) ((U ⋙ V).obj N) (η.app N)) :
    coefficientAdjunctionEquation W U V L T adj η N b :=
  h

/-- Normalize the entire equation while all coefficient functors are opaque. -/
theorem coefficientAdjunctionEquation_raw
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (W : E ⥤ C) (U : E ⥤ F) (V : F ⥤ D) (L : C ⥤ D) (T : D ⥤ C)
    (adj : L ⊣ T) (η : W ⋙ L ⟶ U ⋙ V) (N : E)
    (b : W.obj N ⟶ T.obj ((U ⋙ V).obj N))
    (h : coefficientAdjunctionEquation W U V L T adj η N b) :
    coefficientRawAdjunct W U V T N b =
      adj.homEquiv (W.obj N) (V.obj (U.obj N))
        (coefficientRawComponent W U V L η N) :=
  h

/-- The native coefficient adjunct equation, with the open immersion proof
as an explicit proof argument. -/
def coefficientOpenMapAdjunctEquation
    {R A : Type u} [CommRing R] [CommRing A] (σ : R →+* A) (ι : Type u)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom σ))]
    (gOpen : IsOpenImmersion (ProjectiveSpace.map σ ι))
    (n : ℕ) (N : (Spec (.of R)).Modules) : Prop :=
    letI := gOpen
    coefficientAdjunctionEquation
      (relativeTopDifferentialCoefficientsFunctor (ProjectiveSpace.toSpec R ι) n)
      (Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ)))
      (relativeTopDifferentialCoefficientsFunctor (ProjectiveSpace.toSpec A ι) n)
      (Modules.restrictFunctor (ProjectiveSpace.map σ ι))
      (Scheme.Modules.pushforward (ProjectiveSpace.map σ ι))
      (restrictAdjunction (ProjectiveSpace.map σ ι))
      (relativeTopDifferentialCoefficientsRestrictionIso
          (ProjectiveSpace.toSpec R ι) (ProjectiveSpace.map σ ι)
          (ProjectiveSpace.toSpec A ι) (Spec.map (CommRingCat.ofHom σ))
          (ProjectiveSpace.map_toSpec σ ι) n).hom N
      (projectiveAffineDifferentialCoefficientsOpenMap σ ι n N)

private theorem coefficientOpenMap_eq_homEquiv_derived
    {R A : Type u} [CommRing R] [CommRing A] (σ : R →+* A) (ι : Type u)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom σ))]
    (n : ℕ) (N : (Spec (.of R)).Modules) :
    coefficientOpenMapAdjunctEquation σ ι
      (MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map σ ι).flip inferInstance)
      n N :=
  projectiveAffineDifferentialCoefficientsOpenMap_eq_homEquiv σ ι n N

/-- The original coefficient map is the same native adjunct for any proof
that the projective open map is an open immersion. -/
theorem coefficientOpenMap_eq_homEquiv
    {R A : Type u} [CommRing R] [CommRing A] (σ : R →+* A) (ι : Type u)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom σ))]
    (gOpen : IsOpenImmersion (ProjectiveSpace.map σ ι))
    (n : ℕ) (N : (Spec (.of R)).Modules) :
    coefficientOpenMapAdjunctEquation σ ι gOpen n N := by
  let h : IsOpenImmersion (ProjectiveSpace.map σ ι) :=
    MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map σ ι).flip inferInstance
  exact Eq.mp (congrArg (fun h => coefficientOpenMapAdjunctEquation σ ι h n N)
    (Subsingleton.elim h gOpen)) (coefficientOpenMap_eq_homEquiv_derived σ ι n N)

end AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace
