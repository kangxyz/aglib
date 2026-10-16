/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Finite-free single-complex covers of actual homology

Finite generation of one original homology module supplies a finite-free
module whose single complex maps to the original complex and surjects on
that homology. The generators lift through the original cycle-to-homology
epimorphism by projectivity. No flatness, term bound or Noetherian hypothesis
is needed for this first step of finite-projective replacement.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {R : Type u} [CommRing R] {ι : Type w} [DecidableEq ι]
  {c : ComplexShape ι}

/-- A finite original homology module has a finite-free single-complex
cover whose literal native homology map is an epimorphism. -/
theorem exists_finiteFree_single_homology_epi
    (K : HomologicalComplex (ModuleCat.{max u v} R) c) (i : ι)
    [Module.Finite R (K.homology i)] :
    ∃ P : ModuleCat.{max u v} R, Module.Finite R P ∧ Module.Free R P ∧
      ∃ φ : (single (ModuleCat.{max u v} R) c i).obj P ⟶ K,
        Epi (homologyMap φ i) := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := R) (M := K.homology i))
  let P : ModuleCat.{max u v} R := ModuleCat.of R (s →₀ R)
  let q : P ⟶ K.homology i :=
    ModuleCat.ofHom (Finsupp.linearCombination R (fun x : s => (x : K.homology i)))
  have hq : Epi q := by
    apply (ModuleCat.epi_iff_surjective q).mpr
    apply LinearMap.range_eq_top.mp
    change (Finsupp.linearCombination R (fun x : s => (x : K.homology i))).range = ⊤
    rw [Finsupp.range_linearCombination, Subtype.range_coe_subtype]
    exact hs
  let z : P ⟶ K.cycles i := Projective.factorThru q (K.homologyπ i)
  let φ : (single (ModuleCat.{max u v} R) c i).obj P ⟶ K :=
    mkHomFromSingle (z ≫ K.iCycles i) (fun j _ => by simp)
  have hz : z ≫ K.homologyπ i = q := Projective.factorThru_comp q (K.homologyπ i)
  have hc : (singleObjCyclesSelfIso c i P).inv ≫ cyclesMap φ i = z := by
    apply (cancel_mono (K.iCycles i)).mp
    simp [φ]
  have hh : (singleObjHomologySelfIso c i P).inv ≫ homologyMap φ i = q := by
    rw [← singleObjCyclesSelfIso_inv_homologyπ, Category.assoc,
      homologyπ_naturality, ← Category.assoc, hc, hz]
  have : Epi ((singleObjHomologySelfIso c i P).inv ≫ homologyMap φ i) := by
    rw [hh]
    exact hq
  exact ⟨P, inferInstance, inferInstance, φ,
    epi_of_epi ((singleObjHomologySelfIso c i P).inv) (homologyMap φ i)⟩

end HomologicalComplex
