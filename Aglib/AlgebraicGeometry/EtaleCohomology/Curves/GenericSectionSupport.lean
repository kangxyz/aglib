/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.NoetherianCurveSupport
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finite support of sections trivial at all generic stalks

These are actual structure-sheaf germs, not residue-field evaluations. Thus
nilpotents are retained. The result applies on Noetherian curve tests; it is
not a finite-support assertion for arbitrary non-quasi-compact etale objects.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

variable (X : Scheme.{u})

/-- The zero-germ locus of an actual global section is open. -/
theorem isOpen_globalSection_zeroGerms (f : Γ(X, ⊤)) :
    IsOpen {x : X | X.presheaf.germ ⊤ x trivial f = 0} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨V, i, hxV, hres⟩ :=
    X.toRingedSpace.exists_res_eq_zero_of_germ_eq_zero ⊤ f ⟨x, trivial⟩ hx
  apply Filter.mem_of_superset (V.isOpen.mem_nhds hxV)
  intro y hy
  change X.presheaf.germ ⊤ y trivial f = 0
  rw [← X.presheaf.germ_res_apply i y hy f, hres, map_zero]

/-- A global section vanishing in every actual generic stalk has finite stalk support. -/
theorem finite_globalSection_support_of_generic_germs_zero [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) (f : Γ(X, ⊤))
    (hf : ∀ η : genericPoints X, X.presheaf.germ ⊤ η.val trivial f = 0) :
    {x : X | X.presheaf.germ ⊤ x trivial f ≠ 0}.Finite := by
  exact TopologicalSpace.finite_compl_open_of_contains_genericPoints hdim
    (isOpen_globalSection_zeroGerms X f) (fun x hx => hf ⟨x, hx⟩)

/-- A global unit trivial at all actual generic stalks has finite nontrivial support. -/
theorem finite_globalUnit_support_of_generic_germs_one [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1) (a : Γ(X, ⊤)ˣ)
    (ha : ∀ η : genericPoints X, X.presheaf.germ ⊤ η.val trivial (a : Γ(X, ⊤)) = 1) :
    {x : X | X.presheaf.germ ⊤ x trivial (a : Γ(X, ⊤)) ≠ 1}.Finite := by
  have h := finite_globalSection_support_of_generic_germs_zero X hdim
    ((a : Γ(X, ⊤)) - 1) (fun η => by rw [map_sub, map_one, ha η, sub_self])
  simpa only [map_sub, map_one, sub_ne_zero] using h

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
