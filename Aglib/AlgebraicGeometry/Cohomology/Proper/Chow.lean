/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.Chow.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Products.Finiteness

/-!
# A coefficient-independent Chow modification with proved cohomology inputs

The unconditional graph-product construction supplies one proper surjective
modification, an isomorphism over a dense source open, and an actual finite
map to a finite projective product. These data are chosen before any module
coefficient. The actual closed pair and finite map give bounded coherent
derived images, uniformly for every coherent coefficient and integer single
placement. The original structural cohomology of the modification is finite
in every natural degree. No Chow, proper-finiteness or coherence theorem
family is supplied as a premise. Reducedness and integrality are not assumed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The installed ambient derived categories of actual scheme modules. -/
local instance chowCohomologyStandardDerived (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- One actual Chow modification supplies both proved cohomology inputs,
uniformly for every coherent coefficient. Its bound is the sum of the
dimensions of the internally constructed projective factors. -/
theorem exists_chowModification_cohomology
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∃ (m : ℕ) (σ : Fin m → Type u) (_ : ∀ i, Fintype (σ i))
      (Y : Scheme.{u}) (p : Y ⟶ X) (q : Y ⟶ (Chow.projectiveProductOver R σ).left)
      (V : X.Opens) (comm : p ≫ f = q ≫ (Chow.projectiveProductOver R σ).hom),
      IsProper p ∧ Surjective p ∧ IsFinite q ∧ Dense (V : Set X) ∧
        IsIso (p ∣_ V) ∧ IsClosedImmersion (pullback.lift p q comm) ∧
        ∀ (M : Y.Modules), affineLocallyFiniteType Y M →
          (∀ k : ℤ,
            Scheme.Modules.coherentHomologyObjects X
                ((Scheme.Modules.derivedPushforwardPlus p).obj
                  ((DerivedCategory.Plus.singleFunctor Y.Modules k).obj M)) ∧
              ((Scheme.Modules.derivedPushforwardPlus p).obj
                ((DerivedCategory.Plus.singleFunctor Y.Modules k).obj M)).IsGE k ∧
                ((Scheme.Modules.derivedPushforwardPlus p).obj
                  ((DerivedCategory.Plus.singleFunctor Y.Modules k).obj M)).IsLE
                    (k + ∑ i, Fintype.card (σ i))) ∧
          (∀ k : ℤ,
            Scheme.Modules.coherentHomologyObjects (Spec (.of R))
                ((Scheme.Modules.derivedPushforwardPlus (p ≫ f)).obj
                  ((DerivedCategory.Plus.singleFunctor Y.Modules k).obj M)) ∧
              ((Scheme.Modules.derivedPushforwardPlus (p ≫ f)).obj
                ((DerivedCategory.Plus.singleFunctor Y.Modules k).obj M)).IsGE k ∧
                ((Scheme.Modules.derivedPushforwardPlus (p ≫ f)).obj
                  ((DerivedCategory.Plus.singleFunctor Y.Modules k).obj M)).IsLE
                    (k + ∑ i, Fintype.card (σ i))) ∧
          (∀ j : ℕ,
            let α : R →+* Γ(Y, ⊤) :=
              (p ≫ f).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
            letI := moduleCohomologyModuleOfHom Y α M j
            Module.Finite R (Sheaf.H.{u + 1} (moduleAddSheaf Y M) j)) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨m, σ, hσ, Y, p, q, V, comm, hp, hsurj, hq, hdense, hopen, hpair⟩ :=
    Chow.exists_finite_projective_product_modification R f
  let : ∀ i, Fintype (σ i) := hσ
  let : IsFinite q := hq
  let : IsClosedImmersion (pullback.lift p q comm) := hpair
  let d : Fin m → ℕ := fun i => Fintype.card (σ i)
  let e : ∀ i, Option (σ i) ≃ Fin (d i + 1) :=
    fun i => Fintype.equivFinOfCardEq (by simp [d])
  refine ⟨m, σ, hσ, Y, p, q, V, comm, hp, hsurj, hq, hdense, hopen, hpair, ?_⟩
  intro M hM
  refine ⟨?_, ?_, ?_⟩
  · intro k
    exact finiteOverProjectiveProduct_derivedSingle_bounded_coherent R f
      (fun i => Option (σ i)) d e (pullback.lift p q comm) p (by simp) M hM k
  · intro k
    exact finiteToProjectiveProduct_derivedSingle_bounded_coherent R
      (fun i => Option (σ i)) d e q (p ≫ f) comm.symm M hM k
  · intro j
    exact moduleCohomology_finite_of_finiteToProjectiveProduct R
      (fun i => Option (σ i)) d e q (p ≫ f) comm.symm M hM j

end AlgebraicGeometry.Scheme.Cohomology
