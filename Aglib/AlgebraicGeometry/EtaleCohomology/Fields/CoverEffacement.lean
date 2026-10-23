/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteGaloisCover
public import Aglib.CategoryTheory.Sites.Hypercohomology.Terminal
public import Aglib.CategoryTheory.Sites.SheafCohomology.BasisAcyclicity.CoverEffacement
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.Basic

/-! # Finite Galois effacement of original field cohomology classes

An individual positive original `Sheaf.H` class vanishes after restriction of
its free-representable source to an actual finite Galois cover. The displayed
map is the original free-representable restriction followed by the canonical
terminal/integer source comparison. No Galois cohomology comparison or
positive cohomology vanishing is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.Sheaf.Hypercohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u w

open Scheme.FiniteEtale Scheme.FiniteEtale.FieldGalois.Arbitrary

variable (K : Type u) [Field K]

attribute [local instance] hasSheafifyLarge

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} (Spec (.of K)))]

/-- Individual positive original cohomology classes are killed by an actual
finite Galois field cover, with the source restriction map retained explicitly. -/
theorem exists_finiteGalois_ext_eq_zero
    (A : AbelianSheaf.{u, u + 1} (Spec (.of K))) [HasInjectiveResolution A]
    (n : ℕ) (α : Sheaf.H.{w} A (n + 1)) :
    ∃ L : FiniteGaloisIntermediateField K (SeparableClosure K),
      (Ext.mk₀ (((freeAbelianSheafFunctor.{u + 1} (Scheme.smallEtaleTopology
        (Spec (.of K)))).map ((StrictlyLocal.terminalIsTerminal K).from
          ((toEtale _).obj (finiteFieldCover K L)))) ≫
        (constantIntegerFreeTerminalIso (Scheme.smallEtaleTopology (Spec (.of K)))
          (StrictlyLocal.terminalIsTerminal K)).inv)).comp α (Nat.zero_add _) = 0 := by
  let J := Scheme.smallEtaleTopology (Spec (.of K))
  let e := constantIntegerFreeTerminalIso.{u + 1, u, u + 1} J
    (StrictlyLocal.terminalIsTerminal K)
  let β : Ext (freeAbelianSheaf.{u + 1} J (StrictlyLocal.terminalObject K)) A (n + 1) :=
    (Ext.mk₀ e.inv).comp α (Nat.zero_add _)
  obtain ⟨S, hS, hkill⟩ := Sheaf.BasisAcyclicity.exists_covering_sieve_ext_eq_zero J n β
  obtain ⟨L, hL⟩ := exists_finiteGalois_mem_covering_sieve K S hS
  refine ⟨L, ?_⟩
  have h := hkill ((StrictlyLocal.terminalIsTerminal K).from
    ((toEtale _).obj (finiteFieldCover K L))) hL
  simpa only [β, Ext.mk₀_comp_mk₀_assoc] using h

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
