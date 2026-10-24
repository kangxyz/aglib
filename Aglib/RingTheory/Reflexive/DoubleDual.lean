/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Reflexive.Dual
public import Aglib.RingTheory.Reflexive.ProjectiveDimension
public import Aglib.RingTheory.RegularLocalRing.Normal
public import Aglib.RingTheory.IntegralClosure.HeightOneIntersection
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Actual surface biduals and extension inside the original generic fibre

The first section derives freeness of an actual finite-module double dual,
including dimensions zero and one.
The second section extends a specified raw map by the normal height-one
intersection theorem. Its generic equation uses doubleDualToFraction itself.
No canonical module, chosen generic basis, or desired blowup comparison is
an input to these lemmas.
-/

@[expose] public noncomputable section

universe u

namespace Module

/-- The actual double dual of a finite module on a regular local surface is free. -/
theorem free_doubleDual_of_dimension_le_two (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (hd : ringKrullDim R ≤ 2)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.Free R (Dual R (Dual R M)) := by
  let : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
  let : IsNoetherian R (Dual R M) := isNoetherian_linearMap R R M
  let : Module.Finite R (Dual R M) := Module.IsNoetherian.finite R _
  let : IsNoetherian R (Dual R (Dual R M)) :=
    isNoetherian_linearMap R R (Dual R M)
  let : Module.Finite R (Dual R (Dual R M)) := Module.IsNoetherian.finite R _
  let : Module.IsReflexive R (Dual R (Dual R M)) := IsReflexive.dual_of_finite
  exact free_of_isReflexive_of_dimension_le_two R hd (Dual R (Dual R M))

/-- Rank one is measured by the original generic localization, not by an
independently supplied line-bundle structure on the double dual. -/
theorem finrank_doubleDual_eq_one_of_generic
    {R K M V : Type u} [CommRing R] [IsNoetherianRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (f : M →ₗ[R] V) [IsLocalizedModule (nonZeroDivisors R) f]
    (hV : Module.finrank K V = 1) :
    Module.finrank R (Dual R (Dual R M)) = 1 := by
  let : FinitePresentation R M := finitePresentation_of_finite R M
  let : IsNoetherian R (Dual R M) := isNoetherian_linearMap R R M
  let : Module.Finite R (Dual R M) := Module.IsNoetherian.finite R _
  let : FinitePresentation R (Dual R M) := finitePresentation_of_finite R _
  let d : Dual R M →ₗ[R] Dual K V :=
    IsLocalizedModule.mapExtendScalars (nonZeroDivisors R) f (Algebra.linearMap R K) K
  let : IsLocalizedModule (nonZeroDivisors R) d :=
    FinitePresentation.isLocalizedModule_mapExtendScalars _ _ _ _
  let dd : Dual R (Dual R M) →ₗ[R] Dual K (Dual K V) :=
    IsLocalizedModule.mapExtendScalars (nonZeroDivisors R) d (Algebra.linearMap R K) K
  let : IsLocalizedModule (nonZeroDivisors R) dd :=
    FinitePresentation.isLocalizedModule_mapExtendScalars _ _ _ _
  calc
    Module.finrank R (Dual R (Dual R M)) =
        Module.finrank R (Dual K (Dual K V)) :=
      (IsLocalizedModule.finrank_eq (nonZeroDivisors R) dd le_rfl).symm
    _ = Module.finrank K (Dual K (Dual K V)) :=
      (IsLocalization.finrank_eq K (nonZeroDivisors R) le_rfl).symm
    _ = Module.finrank K V := by
      rw [Subspace.dual_finrank_eq, Subspace.dual_finrank_eq]
    _ = 1 := hV

/-- The actual rank-one double dual is trivial over the regular local ring.
This is the local algebra for invertibility, not an assumed canonical line. -/
theorem nonempty_doubleDual_equiv_self_of_generic_rank_one
    {R K M V : Type u} [CommRing R] [IsRegularLocalRing R]
    (hd : ringKrullDim R ≤ 2) [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (f : M →ₗ[R] V) [IsLocalizedModule (nonZeroDivisors R) f]
    (hV : Module.finrank K V = 1) :
    Nonempty (R ≃ₗ[R] Dual R (Dual R M)) := by
  let : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
  let : Module.Free R (Dual R (Dual R M)) :=
    free_doubleDual_of_dimension_le_two R hd M
  exact Module.nonempty_linearEquiv_of_finrank_eq_one
    (finrank_doubleDual_eq_one_of_generic f hV)

end Module

namespace Module.Dual

variable {R K N V : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup N] [Module R N] [FinitePresentation R N]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
  [IsReflexive K V]
  (f : N →ₗ[R] V) [IsLocalizedModule (nonZeroDivisors R) f]

/-- Actual height-one membership puts a vector in the embedded double dual.
The original module need not be reflexive or torsion-free. -/
theorem mem_range_doubleDualToFraction_of_height_one (v : V)
    (hv : ∀ p : Ideal R, p.IsPrime → p.height = 1 →
      ∃ s ∉ p, s • v ∈ Set.range f) :
    v ∈ Set.range (doubleDualToFraction (K := K) f) := by
  apply (mem_range_doubleDualToFraction_iff (K := K) f v).mpr
  intro l
  apply IsIntegrallyClosed.mem_range_of_forall_height_one
  intro p hp hh
  obtain ⟨s, hs, n, hn⟩ := hv p hp hh
  refine ⟨s, hs, l n, ?_⟩
  let d := IsLocalizedModule.mapExtendScalars (nonZeroDivisors R) f
    (Algebra.linearMap R K) K
  change algebraMap R K (l n) = d l v * algebraMap R K s
  calc
    algebraMap R K (l n) = d l (f n) :=
      (IsLocalizedModule.map_apply (nonZeroDivisors R) f
        (Algebra.linearMap R K) l n).symm
    _ = d l (s • v) := congrArg (d l) hn
    _ = d l v * algebraMap R K s := by
      simp only [LinearMap.map_smul_of_tower, Algebra.smul_def, mul_comm]

variable {P : Type*} [AddCommGroup P] [Module R P]
  (g : P →ₗ[R] V)
  (hg : ∀ m : P, ∀ p : Ideal R, p.IsPrime → p.height = 1 →
    ∃ s ∉ p, s • g m ∈ Set.range f)

/-- The specified generic raw map is lifted through the actual bidual embedding. -/
def liftLinearMapToDoubleDualOfHeightOne : P →ₗ[R] Dual R (Dual R N) :=
  g.codRestrictOfInjective (doubleDualToFraction (K := K) f)
    (doubleDualToFraction_injective (K := K) f)
    (fun m => mem_range_doubleDualToFraction_of_height_one (K := K) f (g m) (hg m))

/-- The lift retains exactly the supplied original generic map. -/
theorem liftLinearMapToDoubleDualOfHeightOne_generic (m : P) :
    doubleDualToFraction (K := K) f
      (liftLinearMapToDoubleDualOfHeightOne (K := K) f g hg m) = g m :=
  LinearMap.codRestrictOfInjective_comp_apply _ _ _ _ m

/-- Generic equality determines the extension uniquely. -/
theorem liftLinearMapToDoubleDualOfHeightOne_unique
    (h : P →ₗ[R] Dual R (Dual R N))
    (hh : ∀ m, doubleDualToFraction (K := K) f (h m) = g m) :
    h = liftLinearMapToDoubleDualOfHeightOne (K := K) f g hg := by
  apply LinearMap.ext
  intro m
  apply doubleDualToFraction_injective (K := K) f
  exact (hh m).trans
    (liftLinearMapToDoubleDualOfHeightOne_generic (K := K) f g hg m).symm

/-- If the map already lands in the original module, the lift is its original
evaluation map. This fixes the normalization on every isomorphism open. -/
theorem liftLinearMapToDoubleDualOfHeightOne_eval
    (h : P →ₗ[R] N) (hh : ∀ m, f (h m) = g m) (m : P) :
    liftLinearMapToDoubleDualOfHeightOne (K := K) f g hg m = eval R N (h m) := by
  apply doubleDualToFraction_injective (K := K) f
  rw [liftLinearMapToDoubleDualOfHeightOne_generic (K := K),
    doubleDualToFraction_eval (K := K)]
  exact (hh m).symm

end Module.Dual
