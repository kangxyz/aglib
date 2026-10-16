/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Support
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pullback
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Direct coherent descent to a closed thickening

On a Noetherian scheme an actual coherent module supported in the native
support of an ideal datum is annihilated by a positive power of that ideal.
It therefore descends directly to that actual closed thickening. The
coefficient there is the ordinary native pullback, and the comparison is
the inverse of the original adjunction unit. No filtration, reducedness or
full-support hypothesis on the coefficient is used.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

open QuasiCoherent QuasiCoherent.AffineOpenSections

variable {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData) (M : X.Modules)

/-- Native coherent support on a Noetherian scheme supplies one actual
positive ideal power annihilating the original module sheaf. -/
theorem exists_pos_pow_killedByIdealSheaf_of_coherent_support
    (hM : affineLocallyFiniteType X M) (hs : support M ⊆ I.support) :
    ∃ n : ℕ, 0 < n ∧ killedByIdealSheaf (I ^ n) M := by
  let : M.IsFinitePresentation := affineLocallyFiniteType_finitePresentation hM
  apply exists_pos_pow_killedByIdealSheaf_of_support_subset I M hs
  · intro U
    let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    exact (I.ideal U).fg_of_isNoetherianRing
  · intro U
    let hU : IsAffineOpen U.1 := U.2
    have hf := (hM Γ(X, U.1) hU.fromSpec).2
    let : Module.Finite Γ(X, U.1) Γ(M.restrict hU.fromSpec, ⊤) := hf
    exact Module.Finite.equiv (toSpecTopSectionsLinearEquiv M hU).symm

/-- A supported coherent module descends to an actual positive closed
thickening with unchanged topological support. Its descended coefficient
is the actual ordinary pullback, and its comparison uses the original unit. -/
theorem exists_coherent_thickening_descent (hM : affineLocallyFiniteType X M)
    (hs : support M ⊆ I.support) :
    ∃ n : ℕ, 0 < n ∧ killedByIdealSheaf (I ^ n) M ∧
      affineLocallyFiniteType (I ^ n).subscheme
        ((pullback (I ^ n).subschemeι).obj M) ∧
      Nonempty ((pushforward (I ^ n).subschemeι).obj
        ((pullback (I ^ n).subschemeι).obj M) ≅ M) ∧
      Set.range (I ^ n).subschemeι = (I.support : Set X) := by
  obtain ⟨n, hn, hkill⟩ := exists_pos_pow_killedByIdealSheaf_of_coherent_support I M hM hs
  have hker : killedByIdealSheaf (I ^ n).subschemeι.ker M := by
    rwa [(I ^ n).ker_subschemeι]
  refine ⟨n, hn, hkill, affineLocallyFiniteType_pullback (I ^ n).subschemeι hM,
    ⟨closedImmersionDescentIso (I ^ n).subschemeι M hker⟩, ?_⟩
  rw [Scheme.IdealSheafData.range_subschemeι, I.support_pow n (Nat.ne_zero_of_lt hn)]

end AlgebraicGeometry.Scheme.Modules
