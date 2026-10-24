/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Derived
public import Aglib.Algebra.Homology.DerivedCategory.TStructure.HomToSingle
public import Mathlib.RingTheory.LocalRing.Length

/-!
# Residue morphisms and the original derived evaluation

A nonzero finite-length top homology gives an actual morphism to the
same-degree residue single. Naturality of the original A-derived signed
evaluation detects this morphism after dualizing. The actual residue-dual
isomorphism and evaluation at the original object then produce a morphism
in the opposite direction.

This is the algebraic obstruction used by surface vanishing. The actual
coinduced residue comparison, finite-projective models, geometric residue
vanishing and canonical-module comparison remain separate suppliers.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u v w

namespace IsLocalRing

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- A nonzero finite-length module has a surjection to the actual residue
field, using a genuine simple quotient and the unique maximal ideal. -/
theorem finiteLength_residue_surjection
    (M : Type u) [AddCommGroup M] [Module A M] (hM : IsFiniteLength A M) :
    Nontrivial M → ∃ q : M →ₗ[A] ResidueField A, Function.Surjective q := by
  induction hM with
  | @of_subsingleton M _ _ _ =>
    intro h
    let : Nontrivial M := h
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    exact (hx (Subsingleton.elim _ _)).elim
  | @of_simple_quotient M _ _ N hsimple _ _ =>
    intro _
    let : IsSimpleModule A (M ⧸ N) := hsimple
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
      (inferInstance : IsSimpleModule A (M ⧸ N))
    have hm' : m = maximalIdeal A := IsLocalRing.eq_maximalIdeal hm
    subst m
    exact ⟨e.toLinearMap.comp N.mkQ, e.surjective.comp N.mkQ_surjective⟩

end IsLocalRing

namespace DerivedCategory

variable {A : Type u} [CommRing A] [IsLocalRing A]
  [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- The native top-homology projection gives a nonzero morphism to the
actual residue single when its original finite-length top homology is nonzero. -/
theorem exists_nonzero_top_residue_morphism (K : DerivedCategory (ModuleCat.{u} A))
    (n : ℤ) [K.IsLE n]
    (hN : IsFiniteLength A ((homologyFunctor (ModuleCat.{u} A) n).obj K))
    [Nontrivial ((homologyFunctor (ModuleCat.{u} A) n).obj K)] :
    ∃ α : K ⟶ (singleFunctor (ModuleCat.{u} A) n).obj (ModuleCat.of A (ResidueField A)),
      α ≠ 0 := by
  let N := (homologyFunctor (ModuleCat.{u} A) n).obj K
  obtain ⟨q, hq⟩ := IsLocalRing.finiteLength_residue_surjection A N hN inferInstance
  let q' : N ⟶ ModuleCat.of A (ResidueField A) := ModuleCat.ofHom q
  have hq' : q' ≠ 0 := by
    intro hz
    obtain ⟨x, hx⟩ := hq 1
    have h := ConcreteCategory.congr_hom hz x
    change q x = 0 at h
    exact one_ne_zero (hx.symm.trans h)
  let E := homToSingleAddEquiv K n (ModuleCat.of A (ResidueField A))
  refine ⟨E.symm q', ?_⟩
  intro hz
  have h := congrArg E hz
  simp only [AddEquiv.apply_symm_apply, map_zero] at h
  exact hq' h

end DerivedCategory

namespace CochainComplex.HomComplex

section Detection

variable {A : Type u} [CommRing A]
  [HasDerivedCategory.{w} (ModuleCat.{v} A)]
  (J : CochainComplex (ModuleCat.{v} A) ℤ) [J.IsKInjective]

/-- Naturality detects a morphism after dualizing whenever the original
evaluation at its target is invertible. Evaluation at its dual is not required. -/
theorem derivedDual_map_eq_zero_iff
    {K L : DerivedCategory (ModuleCat.{v} A)}
    [IsIso ((derivedEvaluation J).app L)] (α : K ⟶ L) :
    (derivedDual J).map α.op = 0 ↔ α = 0 := by
  let D := derivedDual J
  constructor
  · intro hα
    have hdouble : D.map (D.map α.op).op = 0 := by
      rw [hα]
      change D.map (0 : op (D.obj (op K)) ⟶ op (D.obj (op L))) = 0
      exact D.map_zero _ _
    have hnat := (derivedEvaluation J).naturality α
    change α ≫ (derivedEvaluation J).app L =
      (derivedEvaluation J).app K ≫ D.map (D.map α.op).op at hnat
    rw [hdouble, comp_zero] at hnat
    apply (cancel_mono ((derivedEvaluation J).app L)).mp
    simpa only [zero_comp] using hnat
  · rintro rfl
    change D.map (0 : op L ⟶ op K) = 0
    exact D.map_zero _ _

/-- The same residue-dual isomorphism and original evaluation turn a
nonzero dual morphism into an actual nonzero morphism to the original object. -/
theorem exists_nonzero_morphism_of_dual
    (K E : DerivedCategory (ModuleCat.{v} A))
    (ρ : (derivedDual J).obj (op E) ≅ E)
    [IsIso ((derivedEvaluation J).app K)]
    [IsIso ((derivedEvaluation J).app E)]
    (α : (derivedDual J).obj (op K) ⟶ E) (hα : α ≠ 0) :
    ∃ β : E ⟶ K, β ≠ 0 := by
  let ε := (derivedEvaluation J).app K
  let β : E ⟶ K := ρ.inv ≫ (derivedDual J).map α.op ≫ inv ε
  refine ⟨β, ?_⟩
  intro hβ
  have h₁ : (derivedDual J).map α.op ≫ inv ε = 0 := by
    apply (cancel_epi ρ.inv).mp
    simpa only [comp_zero] using hβ
  have h₂ : (derivedDual J).map α.op = 0 := by
    apply (cancel_mono (inv ε)).mp
    simpa only [zero_comp] using h₁
  exact hα ((derivedDual_map_eq_zero_iff J α).mp h₂)

end Detection

section ResidueObstruction

variable {A : Type u} [CommRing A] [IsLocalRing A]
  [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  (J : CochainComplex (ModuleCat.{u} A) ℤ) [J.IsKInjective]

/-- Vanishing of the actual residue-single morphisms kills the original
finite-length top homology of the dual, after its genuine residue comparison
and original evaluations have been supplied. This is an algebraic obstruction;
it does not assume or assert a geometric surface duality theorem. -/
theorem isZero_dual_topHomology_of_residue_vanishing
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    [((derivedDual J).obj (op K)).IsLE n]
    (hN : IsFiniteLength A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        ((derivedDual J).obj (op K))))
    (ρ : (derivedDual J).obj
        (op ((DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj
          (ModuleCat.of A (ResidueField A)))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj
        (ModuleCat.of A (ResidueField A)))
    [IsIso ((derivedEvaluation J).app K)]
    [IsIso ((derivedEvaluation J).app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj
        (ModuleCat.of A (ResidueField A))))]
    (hvan : ∀ f : (DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj
      (ModuleCat.of A (ResidueField A)) ⟶ K, f = 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      ((derivedDual J).obj (op K))) := by
  classical
  apply ModuleCat.isZero_iff_subsingleton.mpr
  by_contra hn
  let : Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      ((derivedDual J).obj (op K))) := not_subsingleton_iff_nontrivial.mp hn
  obtain ⟨α, hα⟩ := DerivedCategory.exists_nonzero_top_residue_morphism
    ((derivedDual J).obj (op K)) n hN
  obtain ⟨β, hβ⟩ := exists_nonzero_morphism_of_dual J K _ ρ α hα
  exact hβ (hvan β)

end ResidueObstruction

end CochainComplex.HomComplex
