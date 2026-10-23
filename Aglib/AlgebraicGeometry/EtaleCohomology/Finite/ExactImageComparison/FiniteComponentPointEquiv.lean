/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.FiniteComponentPoint

/-! # Finite components indexed by points in one common algebraically closed field -/

@[expose] public noncomputable section

open IsLocalRing

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u v w

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (ResidueField R)]
  (A : Type v) [CommRing A] [Algebra R A] [Module.Finite R A]
  (Ω : Type w) [Field Ω] [IsAlgClosed Ω] [Algebra (ResidueField R) Ω]

/-- Reconstruct an actual geometric point from the maximal component it selects. -/
theorem finiteComponentPoint_geometricPointComponent (a : A →+* Ω)
    (ha : a.comp (algebraMap R A) =
      (algebraMap (ResidueField R) Ω).comp (residue R)) :
    finiteComponentPoint R A Ω (geometricPointComponent R A Ω a ha) = a := by
  let m := geometricPointComponent R A Ω a ha
  let C := Localization.AtPrime m.asIdeal
  let : Module.Finite R C := HenselianLocalRing.finite_localizationAtPrime R A m.asIdeal
  let : IsLocalHom (algebraMap R C) := by
    apply ((local_hom_TFAE (algebraMap R C)).out 5 1).mp
    exact eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (maximalIdeal C))
  have hu : ∀ y : m.asIdeal.primeCompl, IsUnit (a y) := by
    intro y
    apply isUnit_iff_ne_zero.mpr
    intro hy
    exact y.property (show (y : A) ∈ m.asIdeal from hy)
  let b : C →+* Ω := IsLocalization.lift (S := C) hu
  have hb : b.comp (algebraMap A C) = a := IsLocalization.lift_comp hu
  have hbR : b.comp (algebraMap R C) =
      (algebraMap (ResidueField R) Ω).comp (residue R) := by
    rw [IsScalarTower.algebraMap_eq R A C, ← RingHom.comp_assoc, hb]
    exact ha
  let : IsLocalHom b := geometricPoint_isLocalHom R C Ω b hbR
  have hbu := finiteLocalGeometricPoint_unique R C Ω b hbR
  change (finiteLocalGeometricPoint R C Ω).comp (algebraMap A C) = a
  rw [← hbu]
  exact hb

/-- Maximal components and actual geometric points over the fixed closed base
point are in bijection. All geometric points use the same field `Ω`. -/
def finiteComponentPointEquiv : MaximalSpectrum A ≃
    {a : A →+* Ω // a.comp (algebraMap R A) =
      (algebraMap (ResidueField R) Ω).comp (residue R)} where
  toFun m := ⟨finiteComponentPoint R A Ω m, finiteComponentPoint_comp_algebraMap R A Ω m⟩
  invFun a := geometricPointComponent R A Ω a.val a.property
  left_inv m := by
    apply MaximalSpectrum.ext
    exact finiteComponentPoint_ker R A Ω m
  right_inv a := by
    apply Subtype.ext
    exact finiteComponentPoint_geometricPointComponent R A Ω a.val a.property

end AlgebraicGeometry.Scheme.EtaleCohomology
