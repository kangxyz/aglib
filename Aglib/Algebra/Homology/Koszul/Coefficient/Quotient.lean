/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors
-/
module

public import Aglib.Algebra.Homology.Koszul.Coefficient
public import Aglib.Algebra.Homology.Koszul.ScalarQuotientFunctor
public import Aglib.Algebra.Homology.Koszul.Single.Tensor.Functor
public import Mathlib.Algebra.Homology.Additive

/-!
# Quotient coefficients commute with finite Koszul complexes

The explicit one-element tensor comparison extends recursively to arbitrary
finite lists. In particular, the literal degreewise quotient by a scalar is
isomorphic to the actual finite Koszul complex with quotient coefficients.
This is the quotient comparison needed for regular-sequence induction.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R]

/-- An additive scalar-preserving functor commutes with finite coefficient Koszul complexes. -/
noncomputable def coefficientMapIso (F : ModuleCat R ⥤ ModuleCat R) [F.Additive]
    (hF : ∀ (a : R) (X : ModuleCat R), F.map (ModuleCat.ofHom (LinearMap.lsmul R X a)) =
      ModuleCat.ofHom (LinearMap.lsmul R (F.obj X) a)) (M : ModuleCat R) :
    (s : List R) → mappedComplex F (coefficientComplex M s) ≅ coefficientComplex (F.obj M) s
  | [] => (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.down ℕ) 0).app M
  | a :: s => singleTensorMapIso F a (coefficientComplex M s) (hF a) ≪≫
      whiskerLeftIso (singleComplex R a) (coefficientMapIso F hF M s)

/-- Quotienting all terms is the same as quotienting the coefficient module. -/
noncomputable def coefficientQuotientIso (a : R) (M : ModuleCat R) (s : List R) :
    quotientComplex a (coefficientComplex M s) ≅
      coefficientComplex ((scalarQuotientFunctor a).obj M) s :=
  coefficientMapIso (scalarQuotientFunctor a)
    (fun b X => scalarQuotientFunctor_map_lsmul a X b) M s

/-- In particular, quotienting the ring Koszul complex gives quotient coefficients. -/
noncomputable def chainComplexQuotientIso (a : R) (s : List R) :
    quotientComplex a (chainComplex s) ≅
      coefficientComplex (ModuleCat.of R (SingleQuotient R a)) s :=
  eqToIso (congrArg (quotientComplex a) (coefficientComplex_ring s).symm) ≪≫
    coefficientQuotientIso a (ModuleCat.of R R) s

end ChainComplex.Koszul
