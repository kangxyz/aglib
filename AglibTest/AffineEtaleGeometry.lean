/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AlgebraicSimplex.Zero
public import Aglib.AlgebraicGeometry.AlgebraicSimplex.Units
public import Aglib.AlgebraicGeometry.AlgebraicSimplex.Endpoints
public import Aglib.AlgebraicGeometry.AlgebraicSimplex.FieldBaseChange
public import Aglib.AlgebraicGeometry.AffineScheme.StructureMap
public import Aglib.AlgebraicGeometry.AffineScheme.TensorPullback
public import Aglib.AlgebraicGeometry.AffineScheme.BaseChangeCoordinates
public import Aglib.AlgebraicGeometry.AffineScheme.IsomorphismCoordinates
public import Aglib.AlgebraicGeometry.AffineScheme.FieldSections
public import Aglib.AlgebraicGeometry.Stalk.Scalar
public import Aglib.AlgebraicGeometry.Morphisms.Flat.AffineStalk
public import Aglib.AlgebraicGeometry.Morphisms.Flat.DVRBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.Flat.GenericFiberCriteria
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GenericFieldBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.RationalPointCompletion
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.Dimension
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.Stalks
public import Aglib.AlgebraicGeometry.Morphisms.Etale.Locus

/-!
# Clients of the affine, simplex and finite-etale coordinate interfaces

These examples retain general commutative-ring simplex coordinates, actual
scalar maps, and the separate hypotheses of normalization and adic fullness.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.FiniteEtale

universe u

namespace AglibTest.AffineEtaleGeometry

example (R : Type u) [CommRing R] (n : ℕ) :
    ∑ i, AlgebraicSimplex.coordinate R n i = 1 := AlgebraicSimplex.sum_coordinate R n

example (R : Type u) [CommRing R] (a : R) :
    AlgebraicSimplex.zeroEquiv R (algebraMap R (AlgebraicSimplex.CoordinateRing R 0) a) = a :=
  AlgebraicSimplex.zeroEquiv_algebraMap R a

example {K L : Type u} [Field K] [Field L] (f : K →+* L) (n : ℕ) :
    (AlgebraicSimplex.coefficientMap f n).Flat := AlgebraicSimplex.coefficientMap_flat f n

example {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.algebraMap R A = Spec.algebraMap R B :=
  Spec.map_algHom_algebraMap f

example {R : Type u} [CommRing R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) [Flat p] (x : X) : (p.stalkScalar x).Flat :=
  p.stalkScalar_flat x

/-- The affine section equivalence has no finite-algebra assumption. -/
example (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] (A : CommAlgCat.{u} K) :
    (Over.mk (Spec.algebraMap K Ω) ⟶ (algebraSpecOver K).obj (op A)) ≃ (A →ₐ[K] Ω) :=
  Spec.affineFieldSectionEquiv K Ω A

example (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R] :
    (baseChange (Spec.algebraMap R (R ⧸ I))).Full := inferInstance

/-- Generic recovery permits arbitrary integral bases and split or empty covers. -/
example (X : Scheme.{u}) [IsIntegral X] (C : Scheme.FiniteEtale (Spec X.functionField)) :
    IsIso (GenericNormalization.comparison X C) := inferInstance

/-- Generic full faithfulness does not require local Noetherianity. -/
example (X : Scheme.{u}) [IsIntegral X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] :
    (baseChange (X.fromSpecStalk (genericPoint X))).Full := inferInstance

/-- The actual target-stalk criterion keeps local finite presentation explicit. -/
example {Z X : Scheme.{u}} (f : Z ⟶ X) [LocallyOfFinitePresentation f] (z : Z)
    (h : Etale (pullback.snd f (X.fromSpecStalk (f z)))) :
    ∃ W : Z.Opens, z ∈ W ∧ Etale (W.ι ≫ f) :=
  Scheme.LocalRing.Etale.exists_etale_neighborhood_of_etale_stalkBaseChange f z h

end AglibTest.AffineEtaleGeometry
