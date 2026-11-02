/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Gorenstein.CanonicalModule
public import Aglib.RingTheory.Gorenstein.NormalQuotient

/-!
# Intrinsic Gorensteinness and canonical triviality for normal quotients

For the original surjective local map from a regular local ring to a normal
Noetherian local domain of dimension at most two, finite self-injective
dimension is equivalent to triviality of the same installed canonical
homology. Concentration and both implications are proved by the existing
actual algebra suppliers, not supplied as conclusions under a new predicate.

The construction also retains the original derived-coinduction map for an
actual ambient coefficient-line frame. No completeness or finiteness over
an earlier unrelated base is asserted.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Abelian
universe u w a b

namespace RingHom
variable {P S : Type u} [CommRing P] [CommRing S] [IsRegularLocalRing P]
  [IsLocalRing S] [IsNoetherianRing S] [IsDomain S] [IsIntegrallyClosed S]
  [HasExt.{w} (ModuleCat.{u} P)]
  [HasDerivedCategory.{a} (ModuleCat.{u} P)]
  [HasDerivedCategory.{b} (ModuleCat.{u} S)]
  (q : P →+* S) [IsLocalHom q] (hq : Function.Surjective q)
  (n r : ℕ) (hP : ringKrullDim P = ((n + r : ℕ) : ℕ))
  (hS : ringKrullDim S = (r : ℕ)) (hr : r ≤ 2)

include hq hP hS hr in
/-- Intrinsic finite self-injective dimension constructs an actual frame of
original canonical homology for the specified normal quotient. -/
def coinducedHomologyLinearEquivOfNormalQuotient
    (d : ℕ) [HasInjectiveDimensionLE (ModuleCat.of S S) d] :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).obj
      ((ModuleCat.coextendScalars q).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} P) 0).obj
          (ModuleCat.of P P))) ≃ₗ[S] S := by
  let f : P →ₗ[P] ((ModuleCat.restrictScalars q).obj (ModuleCat.of S S)) :=
    { toFun := q
      map_add' := q.map_add
      map_smul' := q.map_mul }
  let : Module.Finite P ((ModuleCat.restrictScalars q).obj (ModuleCat.of S S)) :=
    Module.Finite.of_surjective f hq
  exact q.coinducedHomologyLinearEquivOfSelfInjectiveDimension (n + r) hP n
    (q.subsingleton_ext_of_normal_quotient_codimension hq n r hP hS hr) d

include hq hP hS hr in
/-- The same construction for an actual ambient coefficient-line frame,
transported through the original derived-coinduction homology isomorphism. -/
def coinducedHomologyLinearEquivOfNormalQuotientOfIso
    (N : ModuleCat.{u} P) (e : N ≅ ModuleCat.of P P)
    (d : ℕ) [HasInjectiveDimensionLE (ModuleCat.of S S) d] :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).obj
      ((ModuleCat.coextendScalars q).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} P) 0).obj N)) ≃ₗ[S] S := by
  let E := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).mapIso
    ((ModuleCat.coextendScalars q).rightDerivedFunctorPlus.mapIso
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} P) 0).mapIso e))
  exact E.toLinearEquiv.trans
    (q.coinducedHomologyLinearEquivOfNormalQuotient hq n r hP hS hr d)

include hq hP hS hr in
/-- The intrinsic finite self-injective-dimension condition is equivalent to
triviality of the same actual canonical homology, under the full normal
quotient hypotheses. No conclusion-shaped Gorenstein predicate is introduced. -/
theorem exists_self_hasInjectiveDimensionLE_iff_nonempty_coinducedHomologyLinearEquiv :
    (∃ d : ℕ, HasInjectiveDimensionLE (ModuleCat.of S S) d) ↔
      Nonempty ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).obj
        ((ModuleCat.coextendScalars q).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} P) 0).obj
            (ModuleCat.of P P))) ≃ₗ[S] S) := by
  constructor
  · rintro ⟨d, hd⟩
    let : HasInjectiveDimensionLE (ModuleCat.of S S) d := hd
    exact ⟨q.coinducedHomologyLinearEquivOfNormalQuotient hq n r hP hS hr d⟩
  · rintro ⟨e⟩
    exact ⟨r, q.self_hasInjectiveDimensionLE_of_coinducedHomology_linearEquiv
      hq n r hP hS hr e⟩

end RingHom
