/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Koszul.Ext.Top
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction.RegularList

/-!
# The original Koszul top class and its quotient line

For every finite weakly regular list, the actual ring quotient computes native
top Ext with the ring coefficient. Its forward map sends each representative
to the original cocycle on the original finite Koszul resolution. It is linear
for the original quotient-source action, and the class kernel is exactly the
list ideal.

The previous recursive coinduction calculation is used only to prove that the
surjective original class map to this rank-one Ext module is injective. The
actual forward map is multiplication by the original Koszul unit class; it is
not the previously chosen recursive equivalence. The public interface needs
no supplied resolution or derived-category size. No Noetherian, flatness,
finiteness, proper-ideal or nontrivial-ring premise is used. Empty lists, zero
rings and unit equations are included. Determinant changes of generators,
localization and geometric sheaf purity remain separate comparisons.
-/

open CategoryTheory CategoryTheory.Abelian
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w

namespace ChainComplex.Koszul
variable {R : Type u} [CommRing R] [HasExt.{w} (ModuleCat.{u} R)]

private theorem topExtRingSpan_apply_mk (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (r : R) :
    letI := Ext.quotientSourceModule.{u,w} (Ideal.ofList s) (ModuleCat.of R R) s.length
    (LinearMap.toSpanSingleton (R ⧸ Ideal.ofList s)
      (Ext.{w} (ModuleCat.of R (R ⧸ Ideal.ofList s)) (ModuleCat.of R R) s.length)
        (topExtClass s hs (ModuleCat.of R R) 1))
      (Ideal.Quotient.mk (Ideal.ofList s) r) =
        topExtClass s hs (ModuleCat.of R R) r := by
  let := Ext.quotientSourceModule.{u,w} (Ideal.ofList s) (ModuleCat.of R R) s.length
  change Ideal.Quotient.mk (Ideal.ofList s) r • topExtClass s hs (ModuleCat.of R R) 1 = _
  rw [Ext.quotientSourceModule_mk_smul]
  simpa only [smul_eq_mul, mul_one] using
    ((topExtClass s hs (ModuleCat.of R R)).map_smul r (1 : R)).symm

private theorem topExtRingSpan_bijective (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) :
    letI := Ext.quotientSourceModule.{u,w} (Ideal.ofList s) (ModuleCat.of R R) s.length
    Function.Bijective (LinearMap.toSpanSingleton (R ⧸ Ideal.ofList s)
      (Ext.{w} (ModuleCat.of R (R ⧸ Ideal.ofList s)) (ModuleCat.of R R) s.length)
        (topExtClass s hs (ModuleCat.of R R) 1)) := by
  let := Ext.quotientSourceModule.{u,w} (Ideal.ofList s) (ModuleCat.of R R) s.length
  let f := LinearMap.toSpanSingleton (R ⧸ Ideal.ofList s)
    (Ext.{w} (ModuleCat.of R (R ⧸ Ideal.ofList s)) (ModuleCat.of R R) s.length)
      (topExtClass s hs (ModuleCat.of R R) 1)
  have hf : Function.Surjective f := by
    intro e
    obtain ⟨r, hr⟩ := topExtClass_surjective s hs (ModuleCat.of R R) e
    exact ⟨Ideal.Quotient.mk (Ideal.ofList s) r, (topExtRingSpan_apply_mk s hs r).trans hr⟩
  let E := ModuleCat.regularListQuotientExtLinearEquiv.{u,w} s hs
    (injectiveResolution (ModuleCat.of R R))
  let g := E.symm.toLinearMap.comp f
  have hg : Function.Surjective g := E.symm.surjective.comp hf
  obtain ⟨a, ha⟩ := hg 1
  have hmul (x : R ⧸ Ideal.ofList s) : g x = x * g 1 := by
    simpa only [smul_eq_mul, mul_one] using g.map_smul x (1 : R ⧸ Ideal.ofList s)
  have hunit : a * g 1 = 1 := (hmul a).symm.trans ha
  have hleft (x : R ⧸ Ideal.ofList s) : a * g x = x := by
    rw [hmul, mul_left_comm a x, hunit, mul_one]
  refine ⟨?_, hf⟩
  intro x y hxy
  have h : g x = g y := congrArg E.symm hxy
  have h' := congrArg (fun z => a * z) h
  rwa [hleft, hleft] at h'

public section

/-- The original Koszul top class identifies the ring quotient with its native top Ext line. -/
def topExtRingQuotientLinearEquiv (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s) :
    letI := Ext.quotientSourceModule.{u,w} (Ideal.ofList s) (ModuleCat.of R R) s.length
    (R ⧸ Ideal.ofList s) ≃ₗ[R ⧸ Ideal.ofList s]
      Ext.{w} (ModuleCat.of R (R ⧸ Ideal.ofList s)) (ModuleCat.of R R) s.length := by
  letI := Ext.quotientSourceModule.{u,w} (Ideal.ofList s) (ModuleCat.of R R) s.length
  exact LinearEquiv.ofBijective (LinearMap.toSpanSingleton (R ⧸ Ideal.ofList s)
    (Ext.{w} (ModuleCat.of R (R ⧸ Ideal.ofList s)) (ModuleCat.of R R) s.length)
      (topExtClass s hs (ModuleCat.of R R) 1)) (topExtRingSpan_bijective s hs)

end

@[expose] public section

/-- A literal quotient representative is sent to its original top Koszul cocycle class. -/
@[simp]
theorem topExtRingQuotientLinearEquiv_apply_mk (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (r : R) :
    topExtRingQuotientLinearEquiv.{u,w} s hs (Ideal.Quotient.mk (Ideal.ofList s) r) =
      topExtClass s hs (ModuleCat.of R R) r := topExtRingSpan_apply_mk s hs r

/-- For the ring coefficient, the original top class has exactly the
regular-list ideal as kernel. -/
theorem topExtClass_ring_ker (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s) :
    LinearMap.ker (topExtClass s hs (ModuleCat.of R R)) = Ideal.ofList s := by
  let := Ext.quotientSourceModule.{u,w} (Ideal.ofList s) (ModuleCat.of R R) s.length
  ext r
  change topExtClass s hs (ModuleCat.of R R) r = 0 ↔ r ∈ Ideal.ofList s
  constructor
  · intro hr
    have hq : Ideal.Quotient.mk (Ideal.ofList s) r = 0 := by
      apply (topExtRingQuotientLinearEquiv.{u,w} s hs).injective
      simpa only [topExtRingQuotientLinearEquiv_apply_mk, map_zero] using hr
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq
  · intro hr
    rw [← topExtRingQuotientLinearEquiv_apply_mk s hs r, Ideal.Quotient.eq_zero_iff_mem.mpr hr,
      map_zero]

end

end ChainComplex.Koszul
