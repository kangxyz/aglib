/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Computation.QuasiIso

/-! # Unbounded computation by complexes of acyclic coefficients

Finite cohomological dimension makes the original unbounded derived unit invertible
on every complex of acyclic coefficients. The proof uses the already constructed
K-injective replacement, its injective terms, and its original augmentation.

The bound is on all objects of the source category. No assertion about torsion
of an ambient replacement is made. Truncation/amplitude statements and geometric
proper base change are separate consumers, not conclusions of this leaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe s u v w u' v' w'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [IsGrothendieckAbelian.{s} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  (N : ℕ) (hbound : ∀ M : C, IsZero ((F.rightDerived (N + 1)).obj M))

include N hbound

/-- Under finite cohomological dimension, the original unbounded derived unit
is invertible on an arbitrary unbounded complex of acyclic coefficients. -/
theorem isIso_unboundedRightDerivedFunctorUnit_app_of_acyclic_terms
    (K : CochainComplex C ℤ)
    (hK : ∀ i : ℤ, ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj (K.X i))) :
    IsIso (F.unboundedRightDerivedFunctorUnit.app K) := by
  let i := (CochainComplex.kInjectiveReplacementUnit (isSeparator_separator C)).app K
  have hi : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map i) :=
    F.quasiIso_map_of_acyclic_terms_of_bound i hK
      (fun j n => F.isZero_rightDerived_obj_injective_succ n _) N hbound
  have : IsIso (F.unboundedRightDerivedFunctorUnit.app K ≫
      (F.unboundedRightDerivedFunctorReplacementIso K).hom) := by
    rw [F.unboundedRightDerivedFunctorUnit_app_comp_replacementIso_hom]
    exact Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso D (.up ℤ))
      ((F.mapHomologicalComplex (.up ℤ)).map i) hi
  exact IsIso.of_isIso_comp_right _ (F.unboundedRightDerivedFunctorReplacementIso K).hom

/-- Computation of the same actual unbounded functor by the original termwise image. -/
def unboundedRightDerivedFunctorIsoOfAcyclicTerms (K : CochainComplex C ℤ)
    (hK : ∀ i : ℤ, ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj (K.X i))) :
    F.unboundedRightDerivedFunctor.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  let := F.isIso_unboundedRightDerivedFunctorUnit_app_of_acyclic_terms N hbound K hK
  exact (asIso (F.unboundedRightDerivedFunctorUnit.app K)).symm

/-- The computation comparison is the inverse of the original universal unit. -/
@[reassoc (attr := simp)]
theorem unboundedRightDerivedFunctorIsoOfAcyclicTerms_unit (K : CochainComplex C ℤ)
    (hK : ∀ i : ℤ, ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj (K.X i))) :
    F.unboundedRightDerivedFunctorUnit.app K ≫
      (F.unboundedRightDerivedFunctorIsoOfAcyclicTerms N hbound K hK).hom = 𝟙 _ := by
  let := F.isIso_unboundedRightDerivedFunctorUnit_app_of_acyclic_terms N hbound K hK
  exact IsIso.hom_inv_id _

/-- Any specified quasi-isomorphism into an acyclic-term complex computes the
same unbounded functor, not a newly chosen resolution-based functor. -/
def unboundedRightDerivedFunctorObjIsoOfAcyclicTerms
    {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f]
    (hL : ∀ i : ℤ, ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj (L.X i))) :
    F.unboundedRightDerivedFunctor.obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj L) :=
  F.unboundedRightDerivedFunctor.mapIso (asIso (DerivedCategory.Q.map f)) ≪≫
    F.unboundedRightDerivedFunctorIsoOfAcyclicTerms N hbound L hL

/-- The supplied-resolution comparison identifies the original unit with the image
of that exact supplied arrow. -/
@[reassoc]
theorem unboundedRightDerivedFunctorObjIsoOfAcyclicTerms_unit
    {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f]
    (hL : ∀ i : ℤ, ∀ n : ℕ, IsZero ((F.rightDerived (n + 1)).obj (L.X i))) :
    F.unboundedRightDerivedFunctorUnit.app K ≫
      (F.unboundedRightDerivedFunctorObjIsoOfAcyclicTerms N hbound f hL).hom =
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  dsimp only [unboundedRightDerivedFunctorObjIsoOfAcyclicTerms, Iso.trans_hom,
    Functor.mapIso_hom, asIso_hom]
  have hn := F.unboundedRightDerivedFunctorUnit.naturality f
  change DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) ≫
      F.unboundedRightDerivedFunctorUnit.app L =
    F.unboundedRightDerivedFunctorUnit.app K ≫
      F.unboundedRightDerivedFunctor.map (DerivedCategory.Q.map f) at hn
  rw [← Category.assoc, ← hn, Category.assoc,
    F.unboundedRightDerivedFunctorIsoOfAcyclicTerms_unit N hbound L hL]
  exact Category.comp_id _

end CategoryTheory.Functor
