/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.GroupCohomology.H1.SplitInflation
public import Aglib.GroupCohomology.Kummer.Basic
public import Aglib.RingTheory.RootsOfUnity.CoordinateLevels
public import Aglib.RingTheory.RootsOfUnity.CyclotomicCoordinates
public import Aglib.RingTheory.RootsOfUnity.FieldPullbackIndependence
public import Aglib.RingTheory.RootsOfUnity.FieldEmbedding
public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.RootActions
public import Aglib.AlgebraicGeometry.Group.RootCover
public import Aglib.AlgebraicGeometry.Group.PrimitiveRootCover
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GenericRestriction

/-!
# Root, Kummer, and multiplicative-group interface checks

These examples exercise the common actual root carrier and action, Kummer at
level one in arbitrary characteristic, and finite-etale root constructions with
their original invertible-level conditions. They also check the lower generic
connectedness supplier independently of a coefficient-normalization assembly.
-/

@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory
open Field.absoluteGaloisGroup.RootsOfUnity
open AlgebraicGeometry.Scheme.Group
open scoped TensorProduct

universe u

-- The incoming additive coefficient is the existing root module, on the same carrier.
example (K : Type u) [Field K] [CharZero K] (n : ℕ) [NeZero n] :
    Mu K n = Scheme.FiniteEtale.Cyclotomic.RootCoordinates.RootModule n K := rfl

-- Its actual action is the same literal field-automorphism action as the native one.
example (K : Type u) [Field K] [CharZero K] (n : ℕ) [NeZero n]
    (g : Field.absoluteGaloisGroup K) (a : Mu K n) :
    rootAction K n g a =
      Scheme.FiniteEtale.Cyclotomic.TensorActions.rootGaloisLinear K n g a := rfl

example (K : Type u) [Field K] (f : Kˣ) :
    GroupCohomology.Kummer.kummer K 1 (by decide) f = 0 :=
  GroupCohomology.Kummer.kummer_level_one K f

example (R : Type u) [CommRing R] (n : ℕ) [NeZero n] :
    Module.Finite R (RootsHopfAlgebra.H R n) := inferInstance

example (R : Type u) [CommRing R] (n : ℕ) [NeZero n] (hunit : IsUnit (n : R)) :
    Algebra.Etale R (PrimitiveRootCover.Cover R n) :=
  PrimitiveRootCover.etale R n hunit

example (X : Scheme.{u}) (n : ℕ) (hn : 0 < n)
    (hunit : IsUnit (n : Γ(X, ⊤))) :
    Etale (MultiplicativeGroup.rootsScheme X n).hom :=
  RootsFiniteEtale.rootsScheme_etale X n hn hunit

example (R K B : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing B] [Algebra R B] [Algebra.Smooth R B]
    [ConnectedSpace (PrimeSpectrum B)] :
    ConnectedSpace (PrimeSpectrum (B ⊗[R] K)) :=
  Algebra.Smooth.generic_primeSpectrum_connected R K B
