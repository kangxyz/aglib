/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
Source: `Quillen/Algebra/Homology/KInjectiveRepresentatives.lean` at frozen dirty Quillen
`6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
Source SHA-256: `7ddc95f6aa72965d8385e55eff9078f6e3738f044007c12991e290893236545d`.

# Actual derived arrows and equalities with injective targets

K-injective targets give original chain representatives for derived arrows
and actual homotopies for derived equalities. A specified original derived
factorization is retained up to a genuine chain homotopy.

Every additive functor preserves quasi-isomorphisms between K-injective
complexes, hence between lower-bounded termwise-injective complexes, because
these original maps are homotopy equivalences. The two lower bounds may differ.
No exactness of the functor, upper bounds, or quasicoherence is assumed. This
is suitable for actual section and direct-image models of derived morphisms.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v w u' v'
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    {K L : CochainComplex C ℤ} [L.IsKInjective]

/-- A derived arrow into the genuine K-injective target has an original chain representative. -/
lemma exists_chain_representative_of_isKInjective
    (α : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    ∃ f : K ⟶ L, DerivedCategory.Q.map f = α := by
  let e := DerivedCategory.quotientCompQhIso C
  obtain ⟨β, hβ⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient C (.up ℤ)).obj K) L).surjective
      (e.hom.app K ≫ α ≫ e.inv.app L)
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective β
  refine ⟨f, ?_⟩
  rw [← NatIso.naturality_1 e f]
  change e.inv.app K ≫ DerivedCategory.Qh.map
    ((HomotopyCategory.quotient C (.up ℤ)).map f) ≫ e.hom.app L = α
  rw [hβ]
  simp

/-- Equality in the original derived category is witnessed by an actual chain homotopy. -/
def homotopyOfDerivedEqOfIsKInjective (f g : K ⟶ L)
    (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) : Homotopy f g := by
  let e := DerivedCategory.quotientCompQhIso C
  apply HomotopyCategory.homotopyOfEq f g
  apply (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient C (.up ℤ)).obj K) L).injective
  have hf := NatIso.naturality_2 e f
  have hg := NatIso.naturality_2 e g
  exact hf.symm.trans ((congrArg (fun t => e.hom.app K ≫ t ≫ e.inv.app L) h).trans hg)


/-- Preserve a specified original derived triangle as a genuine chain homotopy. -/
lemma exists_chain_factorization_up_to_homotopy_into_isKInjective
    {A B : CochainComplex C ℤ} (u : A ⟶ B) (v : A ⟶ L)
    (α : DerivedCategory.Q.obj B ⟶ DerivedCategory.Q.obj L)
    (h : DerivedCategory.Q.map u ≫ α = DerivedCategory.Q.map v) :
    ∃ f : B ⟶ L, DerivedCategory.Q.map f = α ∧ Nonempty (Homotopy (u ≫ f) v) := by
  obtain ⟨f, hf⟩ := exists_chain_representative_of_isKInjective α
  refine ⟨f, hf, ⟨homotopyOfDerivedEqOfIsKInjective (u ≫ f) v ?_⟩⟩
  rw [Functor.map_comp, hf]
  exact h

end CochainComplex
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Actual weak maps between K-injective complexes remain weak under every additive functor. -/
lemma quasiIso_map_of_isKInjective (F : C ⥤ D) [F.Additive]
    {K L : CochainComplex C ℤ} [K.IsKInjective] [L.IsKInjective]
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  have hf := (CochainComplex.IsKInjective.quasiIso_iff f).mp inferInstance
  exact homotopyEquivalences_le_quasiIso _ _ _
    (F.homotopyEquivalences_mapHomologicalComplex_map f hf)

/-- Lower-bounded injective models give actual weak-map preservation with independent bounds. -/
lemma quasiIso_map_of_lowerBounded_injective (F : C ⥤ D) [F.Additive]
    {K L : CochainComplex C ℤ} (a b : ℤ)
    (hK : ∀ n, n < a → IsZero (K.X n)) (hL : ∀ n, n < b → IsZero (L.X n))
    (iK : ∀ n, Injective (K.X n)) (iL : ∀ n, Injective (L.X n))
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  have : K.IsStrictlyGE a := (CochainComplex.isStrictlyGE_iff _ _).mpr hK
  have : L.IsStrictlyGE b := (CochainComplex.isStrictlyGE_iff _ _).mpr hL
  have := CochainComplex.isKInjective_of_injective K a
  have := CochainComplex.isKInjective_of_injective L b
  exact quasiIso_map_of_isKInjective F f
end CochainComplex
