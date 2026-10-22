/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.CoherentSupport
public import Aglib.AlgebraicGeometry.Modules.Coherent.Basic

/-!
# Uniform annihilation of coherent defects on an isomorphism locus

A map of coherent sheaves which is an isomorphism off a closed ideal locus
has its actual kernel and cokernel killed by one positive power of that
ideal sheaf. No flatness or dimension bound is involved.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsNoetherian X]

/-- One positive ideal-sheaf power kills both coherent modules supported
on the same closed locus. -/
theorem exists_pos_pow_killedByIdealSheaf_pair (I : X.IdealSheafData)
    (M N : X.Modules) (hM : QuasiCoherent.affineLocallyFiniteType X M)
    (hN : QuasiCoherent.affineLocallyFiniteType X N)
    (hsM : support M ⊆ I.support) (hsN : support N ⊆ I.support) :
    ∃ n : ℕ, 0 < n ∧ killedByIdealSheaf (I ^ n) M ∧
      killedByIdealSheaf (I ^ n) N := by
  obtain ⟨m, hm, hmk⟩ :=
    exists_pos_pow_killedByIdealSheaf_of_coherent_support I M hM hsM
  obtain ⟨n, hn, hnk⟩ :=
    exists_pos_pow_killedByIdealSheaf_of_coherent_support I N hN hsN
  refine ⟨m + n, lt_of_lt_of_le hm (Nat.le_add_right m n), ?_, ?_⟩
  · apply killedByIdealSheaf_of_le (M := M) _ hmk
    intro U
    exact Ideal.pow_le_pow_right (Nat.le_add_right m n)
  · apply killedByIdealSheaf_of_le (M := N) _ hnk
    intro U
    exact Ideal.pow_le_pow_right (Nat.le_add_left n m)

/-- A coherent map invertible on an open has a uniformly bounded defect
on any ideal-sheaf locus containing the complementary closed set. -/
theorem exists_pos_pow_killedByIdealSheaf_kernel_cokernel
    (I : X.IdealSheafData) (U : X.Opens) (hU : (U : Set X)ᶜ ⊆ I.support)
    {M N : X.Modules} (f : M ⟶ N)
    (hM : QuasiCoherent.affineLocallyFiniteType X M)
    (hN : QuasiCoherent.affineLocallyFiniteType X N)
    [IsIso ((restrictFunctor U.ι).map f)] :
    ∃ n : ℕ, 0 < n ∧ killedByIdealSheaf (I ^ n) (kernel f) ∧
      killedByIdealSheaf (I ^ n) (cokernel f) := by
  have h := (supportedAway_isoModSerre_iff U.ι f).mpr inferInstance
  rw [ObjectProperty.isoModSerre_iff] at h
  have hs (P : X.Modules) (hP : supportedAway U.ι P) : support P ⊆ I.support := by
    have hd := (supportedAway_iff_support_disjoint U.ι P).mp hP
    intro x hx
    apply hU
    intro hxU
    exact Set.disjoint_left.mp hd hx ⟨⟨x, hxU⟩, rfl⟩
  exact exists_pos_pow_killedByIdealSheaf_pair I (kernel f) (cokernel f)
    ((QuasiCoherent.affineLocallyFiniteType X).prop_kernel f hM hN)
    ((QuasiCoherent.affineLocallyFiniteType X).prop_cokernel f hM hN)
    (hs _ h.1) (hs _ h.2)

end AlgebraicGeometry.Scheme.Modules
