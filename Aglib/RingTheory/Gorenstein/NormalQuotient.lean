/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction.ConcentratedExt
public import Aglib.RingTheory.RegularLocalRing.NormalQuotientExt
public import Aglib.RingTheory.RegularLocalRing.FiniteProjectiveDimension
public import Mathlib.Algebra.Category.ModuleCat.Ext.Baer
public import Mathlib.Algebra.Category.ModuleCat.InjectiveDimension

/-!
# Finite injective dimension of the canonical module of a normal quotient

For a surjective local map from a regular local ring to a normal Noetherian
local domain of dimension at most two, the actual coinduced homology in the
codimension has injective dimension at most the target dimension. The proof
uses concentration, the finite-module projective dimension theorem, and native
quotient Baer. An actual target-linear trivialization gives finite self-injective
dimension. No converse canonical-module uniqueness theorem is asserted.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Abelian
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

omit [HasDerivedCategory.{a} (ModuleCat.{u} P)]
  [HasDerivedCategory.{b} (ModuleCat.{u} S)] in
include hq hP hS hr in
/-- The original ambient Ext for the specified surjective local map is concentrated
in its codimension; no regular-sequence hypothesis on its kernel is used. -/
theorem subsingleton_ext_of_normal_quotient_codimension (j : ℕ) (hj : j ≠ n) :
    Subsingleton (Ext.{w}
      ((ModuleCat.restrictScalars q).obj (ModuleCat.of S S)) (ModuleCat.of P P) j) := by
  let := q.toAlgebra
  exact q.subsingleton_ext_of_surjective_normal_dimension_le_two_chgUniv hq
    (n + r) r hP hS hr j (by omega)

include hq hP hS hr in
/-- The actual target-ring canonical homology module has finite injective dimension. -/
theorem coinducedHomology_hasInjectiveDimensionLE :
    HasInjectiveDimensionLE
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).obj
        ((ModuleCat.coextendScalars q).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P P))))
      r := by
  let K := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).obj
    ((ModuleCat.coextendScalars q).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} P) 0).obj (ModuleCat.of P P)))
  apply ModuleCat.hasInjectiveDimensionLE_of_quotients K r
  intro I
  let N := ModuleCat.of S (Shrink.{u} (S ⧸ I))
  let T := (ModuleCat.restrictScalars q).obj N
  let : RingHomSurjective q := ⟨hq⟩
  let e : T →ₛₗ[q] S ⧸ I :=
    { toFun := fun x => Shrink.linearEquiv S (S ⧸ I) x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun x y => (Shrink.linearEquiv S (S ⧸ I)).map_smul (q x) y }
  let : Module.Finite P T :=
    (e.finite_iff_of_bijective (Shrink.linearEquiv S (S ⧸ I)).bijective).mpr inferInstance
  let : HasProjectiveDimensionLE T (n + r) :=
    (projectiveDimension_le_iff T (n + r)).mp
      (IsRegularLocalRing.projectiveDimension_le_dimension (n + r) P hP T)
  let E : Ext N K (r + 1) ≃+ Ext.{w} T (ModuleCat.of P P) (r + 1 + n) :=
    ModuleCat.concentratedCoextendScalarsExtAddEquiv q (ModuleCat.of P P) n
      (q.subsingleton_ext_of_normal_quotient_codimension hq n r hP hS hr) N (r + 1)
  let := HasProjectiveDimensionLT.subsingleton T (n + r + 1) (r + 1 + n)
    (by omega) (ModuleCat.of P P)
  exact ⟨fun x y => E.injective (Subsingleton.elim _ _)⟩

include hq hP hS hr in
/-- An actual ambient coefficient-line frame transports the bound through the
same derived coinduction functor and its original homology map. -/
theorem coinducedHomology_hasInjectiveDimensionLE_of_iso
    (N : ModuleCat.{u} P) (e : N ≅ ModuleCat.of P P) :
    HasInjectiveDimensionLE
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).obj
        ((ModuleCat.coextendScalars q).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} P) 0).obj N))) r := by
  let E := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).mapIso
    ((ModuleCat.coextendScalars q).rightDerivedFunctorPlus.mapIso
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} P) 0).mapIso e))
  exact (ModuleCat.hasInjectiveDimensionLE_iff_of_linearEquiv E.toLinearEquiv r).mpr
    (q.coinducedHomology_hasInjectiveDimensionLE hq n r hP hS hr)

include hq hP hS hr in
/-- An actual target-linear trivialization of that same canonical homology yields
finite self-injective dimension, the intrinsic local Gorenstein condition. -/
theorem self_hasInjectiveDimensionLE_of_coinducedHomology_linearEquiv
    (e : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} S) (n : ℤ)).obj
      ((ModuleCat.coextendScalars q).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} P) 0).obj
          (ModuleCat.of P P))) ≃ₗ[S] S) :
    HasInjectiveDimensionLE (ModuleCat.of S S) r :=
  (ModuleCat.hasInjectiveDimensionLE_iff_of_linearEquiv e r).mp
    (q.coinducedHomology_hasInjectiveDimensionLE hq n r hP hS hr)

end RingHom
