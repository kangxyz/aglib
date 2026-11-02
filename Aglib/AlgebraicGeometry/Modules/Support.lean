/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Stalk
public import Aglib.AlgebraicGeometry.Modules.Exact
public import Mathlib.Topology.Sheaves.Abelian
/-!
# Actual stalk support of scheme module sheaves

The ambient Serre class of sheaves vanishing under open restriction is exactly
the class whose ordinary stalk support misses that open. No coherence or
closedness of the support is assumed in this module.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- The underlying abelian-group stalk functor on actual `𝒪_X`-modules. -/
abbrev stalkFunctor (X : Scheme.{u}) (x : X) : X.Modules ⥤ AddCommGrpCat.{u} :=
  SheafOfModulesOfCommRing.stalkFunctor X.sheaf x

/-- A module sheaf is zero exactly when all its stalks are zero. -/
theorem isZero_iff_stalks {X : Scheme.{u}} (M : X.Modules) :
    IsZero M ↔ ∀ x : X, IsZero ((stalkFunctor X x).obj M) :=
  SheafOfModulesOfCommRing.isZero_iff_stalks (R := X.sheaf) M

/-- The ordinary stalk support of an `𝒪_X`-module, without any finiteness
assumption or implicit assertion that this set is closed. -/
def support {X : Scheme.{u}} (M : X.Modules) : Set X :=
  {x | ¬ IsZero ((stalkFunctor X x).obj M)}

@[simp]
theorem mem_support {X : Scheme.{u}} (M : X.Modules) (x : X) :
    x ∈ support M ↔ ¬ IsZero ((stalkFunctor X x).obj M) := Iff.rfl

/-- Vanishing on an open immersion can be tested at every stalk in its image. -/
theorem supportedAway_iff_stalks {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (M : X.Modules) :
    supportedAway j M ↔ ∀ u : U, IsZero ((stalkFunctor X (j u)).obj M) := by
  rw [supportedAway_iff, isZero_iff_stalks]
  constructor
  · intro h u
    exact (h u).of_iso ((Scheme.Modules.restrictStalkNatIso j u).app M).symm
  · intro h u
    exact (h u).of_iso ((Scheme.Modules.restrictStalkNatIso j u).app M)

/-- Support of an open restriction is precisely the inverse image of support. -/
theorem support_restrict {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (M : X.Modules) :
    support ((Scheme.Modules.restrictFunctor j).obj M) = j ⁻¹' support M := by
  ext u
  change (¬ IsZero ((stalkFunctor U u).obj ((Scheme.Modules.restrictFunctor j).obj M))) ↔
    ¬ IsZero ((stalkFunctor X (j u)).obj M)
  exact not_congr ⟨fun h => h.of_iso ((Scheme.Modules.restrictStalkNatIso j u).app M).symm,
    fun h => h.of_iso ((Scheme.Modules.restrictStalkNatIso j u).app M)⟩

/-- The vanishing Serre class is precisely the class with support disjoint
from the image of the open immersion. -/
theorem supportedAway_iff_support_disjoint {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (M : X.Modules) :
    supportedAway j M ↔ Disjoint (support M) (Set.range j) := by
  rw [supportedAway_iff_stalks, Set.disjoint_left]
  constructor
  · rintro h x hx ⟨u, rfl⟩
    exact hx (h u)
  · intro h u
    by_contra hu
    exact h hu ⟨u, rfl⟩

/-- Zero module sheaves have empty support. -/
theorem support_eq_empty_iff {X : Scheme.{u}} (M : X.Modules) :
    support M = ∅ ↔ IsZero M := by
  classical
  rw [isZero_iff_stalks]
  simp only [support, Set.eq_empty_iff_forall_notMem, Set.mem_ofPred_eq, not_not]

/-- Support does not depend on the representative of a module sheaf. -/
theorem support_eq_of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) :
    support M = support N := by
  ext x
  simp only [mem_support]
  exact not_congr ⟨fun h => h.of_iso ((stalkFunctor X x).mapIso e).symm,
    fun h => h.of_iso ((stalkFunctor X x).mapIso e)⟩

end AlgebraicGeometry.Scheme.Modules
