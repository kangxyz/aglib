/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ModuleCat.HomComplex.FiniteProjectiveDimension
public import Aglib.Algebra.Category.ModuleCat.Ext.TopDegree
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Intrinsic self-injective dimension and the original canonical module

For a finite algebra over a regular local ring, assume the original ambient
Ext is concentrated in one degree. Over a Noetherian local target, intrinsic
finite self-injective dimension gives an actual frame of that same installed
coinduced homology.

The proof combines its proved finite projective dimension, positive self-Ext
vanishing, and original scalar homothety. Native local freeness and the rank
of the endomorphism module force rank one. No canonical frame, homothety,
projectivity, or desired duality is supplied as a hypothesis.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex.HomComplex
universe u a b w

namespace RingHom

variable {R S : Type u} [CommRing R] [CommRing S] [IsRegularLocalRing R]
  [IsNoetherianRing S] [IsLocalRing S] (q : R →+* S)
  [Module.Finite R ((ModuleCat.restrictScalars q).obj (ModuleCat.of S S))]
  (dR : ℕ) (hdR : ringKrullDim R = (dR : ℕ))
  [HasExt.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{a} (ModuleCat.{u} R)]
  [HasDerivedCategory.{b} (ModuleCat.{u} S)]
  (n : ℕ) (h : ∀ j : ℕ, j ≠ n → Subsingleton
    (Ext.{w} ((ModuleCat.restrictScalars q).obj (ModuleCat.of S S)) (ModuleCat.of R R) j))

include hdR h in
/-- Intrinsic finite self-injective dimension trivializes the same selected
canonical homology over the local target. This chooses a frame, not a canonical
normalization; no frame or desired homothety is assumed. -/
def coinducedHomologyLinearEquivOfSelfInjectiveDimension
    (dS : ℕ) [HasInjectiveDimensionLE (ModuleCat.of S S) dS] :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).obj
      ((ModuleCat.coextendScalars q).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj
          (ModuleCat.of R R))) ≃ₗ[S] S := by
  let K := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).obj
    ((ModuleCat.coextendScalars q).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))
  let : Module.Finite S K :=
    ModuleCat.derivedCoextendScalarsPlusHomology_finite q (ModuleCat.of R R) n
  let : HasProjectiveDimensionLE K (dS + n) :=
    coinducedHomology_hasProjectiveDimensionLE q dR hdR n h dS
  let : Projective K := ModuleCat.projective_of_self_ext_subsingleton K (dS + n)
    (fun i hi => coinducedHomology_self_ext_subsingleton.{u, a, b, w, u}
      q dR hdR n h i hi)
  let : Module.Free S K := Module.free_of_flat_of_isLocalRing
  let E : S ≃ₗ[S] (K →ₗ[S] K) :=
    (coinducedHomologyHomothetyLinearEquiv q dR hdR n h).trans ModuleCat.homLinearEquiv
  have hRank : Module.finrank S K * Module.finrank S K = 1 := by
    have hE := E.finrank_eq
    rw [Module.finrank_self, Module.finrank_linearMap] at hE
    exact hE.symm
  exact (Module.nonempty_linearEquiv_of_finrank_eq_one
    (Nat.eq_one_of_mul_eq_one_left hRank)).some.symm

include hdR h in
/-- An actual ambient coefficient-line frame transports through the original
derived-coinduction homology map before the proved target frame is applied. -/
def coinducedHomologyLinearEquivOfSelfInjectiveDimensionOfIso
    (N : ModuleCat.{u} R) (e : N ≅ ModuleCat.of R R)
    (dS : ℕ) [HasInjectiveDimensionLE (ModuleCat.of S S) dS] :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).obj
      ((ModuleCat.coextendScalars q).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).obj N)) ≃ₗ[S] S := by
  let E := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).mapIso
    ((ModuleCat.coextendScalars q).rightDerivedFunctorPlus.mapIso
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} R) 0).mapIso e))
  exact E.toLinearEquiv.trans
    (q.coinducedHomologyLinearEquivOfSelfInjectiveDimension dR hdR n h dS)

end RingHom
