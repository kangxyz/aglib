/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Finiteness near a whole proper fibre

Finiteness of the original map over an entire residue-field fibre spreads to
an open of the original base. The non-quasi-finite locus and its proper image
are constructed here. No separate point-fibre or bad-image certificate is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Set

namespace AlgebraicGeometry.Scheme

universe u

/-- If a proper map between schemes proper over the base is finite over a
whole residue-field fibre, it is finite over an actual neighbourhood in that
base. In particular this applies to the generic point of an integral base. -/
theorem exists_open_isFinite_of_finite_fibreBaseChange
    {C X S : Scheme.{u}} (p : X ⟶ S) [IsProper p]
    (ν : C ⟶ X) [IsProper ν] (s : S)
    [IsFinite (pullback.snd ν (p.fiberι s))] :
    ∃ U : S.Opens, s ∈ U ∧ IsFinite (ν ∣_ (p ⁻¹ᵁ U)) := by
  have hfibre (x : X) (hx : p x = s) : (ν ⁻¹' {x}).Finite := by
    let z : Spec (S.residueField s) := Nonempty.some inferInstance
    have hxz : p x = (S.fromSpecResidueField s) z := by
      simpa only [Scheme.fromSpecResidueField_apply] using hx
    obtain ⟨xₛ, hxₛ, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := p) (g := S.fromSpecResidueField s) x z hxz
    apply (((pullback.snd ν (p.fiberι s)).finite_preimage_singleton xₛ).image
      (pullback.fst ν (p.fiberι s))).subset
    intro c hc
    change ν c = x at hc
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := ν) (g := p.fiberι s) c xₛ (hc.trans hxₛ.symm)
    exact ⟨w, hw₂, hw₁⟩
  have hgood (c : C) (hc : (ν ≫ p) c = s) : ν.QuasiFiniteAt c := by
    have hfinite := hfibre (ν c) hc
    let : Finite (ν.fiber (ν c)) := (ν.fiberHomeo (ν c)).finite_iff.mpr hfinite
    exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr
      (isOpen_discrete _)
  let U : S.Opens :=
    ⟨((ν ≫ p) '' (ν.quasiFiniteLocus : Set C)ᶜ)ᶜ,
      ((ν ≫ p).isClosedMap _ ν.quasiFiniteLocus.isOpen.isClosed_compl).isOpen_compl⟩
  have hsU : s ∈ U := by
    rintro ⟨c, hc, hcs⟩
    exact hc (hgood c hcs)
  refine ⟨U, hsU, ?_⟩
  suffices LocallyQuasiFinite (ν ∣_ (p ⁻¹ᵁ U)) from
    IsFinite.of_isProper_of_locallyQuasiFinite _
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  ext c
  have hc : ν.QuasiFiniteAt ((ν ⁻¹ᵁ (p ⁻¹ᵁ U)).ι c) := by
    by_contra hbad
    exact c.2 ⟨_, hbad, rfl⟩
  rw [← Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion,
    ← morphismRestrict_ι, Scheme.Hom.quasiFiniteAt_comp_iff] at hc
  simpa using hc

end AlgebraicGeometry.Scheme
