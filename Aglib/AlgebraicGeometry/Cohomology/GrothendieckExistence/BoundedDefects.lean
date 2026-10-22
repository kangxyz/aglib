/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Completion
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.Support
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits

/-!
# Uniform bounds on ordinary formal defects

A bound here kills the ordinary kernels and cokernels at every original
finite stage. It does not make those kernels into an adic system. Compactness
patches bounds that are uniform in the stage on each affine chart; no
completion/localization interchange or faithful completion is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u v

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Chartwise bounds on any family of quasicoherent modules admit one global
positive bound on a quasicompact scheme. The family need not be finite. -/
theorem exists_pos_pow_killedByIdealSheaf_family [CompactSpace X]
    (J : X.IdealSheafData) {ι : Type v} (M : ι → X.Modules)
    [∀ i, (M i).IsQuasicoherent]
    (hlocal : ∀ U : X.affineOpens, ∃ t : ℕ, ∀ i,
      (J.ideal U) ^ t ≤ Module.annihilator Γ(X, U.1) Γ(M i, U.1)) :
    ∃ t : ℕ, 0 < t ∧ ∀ i, killedByIdealSheaf (J ^ t) (M i) := by
  classical
  choose n hn using hlocal
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => (U.1 : Set X)) (fun U => U.1.isOpen) (by
      intro x hx
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hx isOpen_univ
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩)
  refine ⟨s.sup n + 1, Nat.succ_pos _, fun i => ?_⟩
  apply killedByIdealSheaf_of_affineCover (J ^ (s.sup n + 1)) (M i)
    (fun U : {U : X.affineOpens // U ∈ s} => U.val)
  · intro x
    obtain ⟨U, hUs, hxU⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact ⟨⟨U, hUs⟩, hxU⟩
  · intro U
    change (J.ideal U.val) ^ (s.sup n + 1) ≤ _
    exact (Ideal.pow_le_pow_right
      ((Finset.le_sup U.property).trans (Nat.le_succ (s.sup n)))).trans (hn U.val i)

namespace Coherent.AdicSystem

variable [IsLocallyNoetherian X] {K : X.IdealSheafData}
  {F G : AdicSystem X K}

/-- A specified power kills the two ordinary defects at every finite stage.
The bounding ideal may differ from the ideal defining the formal system. -/
def DefectsKilled (J : X.IdealSheafData) (t : ℕ) (φ : F ⟶ G) : Prop :=
  ∀ n : ℕ, killedByIdealSheaf (J ^ t) (kernel (φ.hom.app (op n))) ∧
    killedByIdealSheaf (J ^ t) (cokernel (φ.hom.app (op n)))

/-- One positive exponent, independent of the stage, kills both defects. -/
def HasBoundedDefects (J : X.IdealSheafData) (φ : F ⟶ G) : Prop :=
  ∃ t : ℕ, 0 < t ∧ DefectsKilled J t φ

/-- Increasing a uniform exponent preserves the bound. -/
theorem DefectsKilled.mono {J : X.IdealSheafData} {t s : ℕ} {φ : F ⟶ G}
    (h : DefectsKilled J t φ) (hts : t ≤ s) : DefectsKilled J s φ := by
  intro n
  exact ⟨killedByIdealSheaf_of_le (idealSheaf_pow_le X J hts) (h n).1,
    killedByIdealSheaf_of_le (idealSheaf_pow_le X J hts) (h n).2⟩

/-- A bound without a positivity convention gives the required positive bound. -/
theorem DefectsKilled.hasBoundedDefects {J : X.IdealSheafData} {t : ℕ}
    {φ : F ⟶ G} (h : DefectsKilled J t φ) : HasBoundedDefects J φ :=
  ⟨t + 1, Nat.succ_pos _, h.mono (Nat.le_succ t)⟩

/-- Uniform bounds on the original affine sections of both ordinary defects
are equivalent to a global uniform bound. The local exponent may depend on
the affine chart, but not on the stage. -/
theorem hasBoundedDefects_iff_affine [CompactSpace X]
    (J : X.IdealSheafData) (φ : F ⟶ G) :
    HasBoundedDefects J φ ↔ ∀ U : X.affineOpens, ∃ t : ℕ, ∀ n : ℕ,
      (J.ideal U) ^ t ≤
        Module.annihilator Γ(X, U.1) Γ(kernel (φ.hom.app (op n)), U.1) ∧
      (J.ideal U) ^ t ≤
        Module.annihilator Γ(X, U.1) Γ(cokernel (φ.hom.app (op n)), U.1) := by
  constructor
  · rintro ⟨t, _, h⟩ U
    refine ⟨t, fun n => ?_⟩
    exact ⟨(killedByIdealSheaf_iff_le_annihilator _ _).mp (h n).1 U,
      (killedByIdealSheaf_iff_le_annihilator _ _).mp (h n).2 U⟩
  · intro h
    let M : Bool × ℕ → X.Modules := fun i =>
      if i.1 then kernel (φ.hom.app (op i.2)) else cokernel (φ.hom.app (op i.2))
    have hc (i : Bool × ℕ) : affineLocallyFiniteType X (M i) := by
      dsimp only [M]
      split
      · exact (affineLocallyFiniteType X).prop_kernel _
          (F.property.coherent i.2) (G.property.coherent i.2)
      · exact (affineLocallyFiniteType X).prop_cokernel _
          (F.property.coherent i.2) (G.property.coherent i.2)
    let : ∀ i, (M i).IsQuasicoherent := fun i =>
      quasicoherent_of_affineCharts _ (fun R j _ => (hc i R j).1)
    obtain ⟨t, ht, hM⟩ := exists_pos_pow_killedByIdealSheaf_family J M (by
      intro U
      obtain ⟨t, ht⟩ := h U
      refine ⟨t, fun i => ?_⟩
      rcases i with ⟨b, n⟩
      cases b
      · simpa [M] using (ht n).2
      · simpa [M] using (ht n).1)
    exact ⟨t, ht, fun n => ⟨by simpa [M] using hM (true, n),
      by simpa [M] using hM (false, n)⟩⟩

end Coherent.AdicSystem

end AlgebraicGeometry.Scheme.Modules
