/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.RootTransversePoint
public import Aglib.AlgebraicGeometry.Spec.TransverseEtaleStalk

/-! # A transverse section cancels an actual pointed etale root presentation

The actual root presentation is pulled back along the original whole DVR
section. Its original point supplies the actual local stalk, and the native
unramified DVR theorem preserves the uniformizer. The whole stalk point forces
exponent one; no auxiliary field or algebra map from the chart ring to the
original DVR is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Algebra.Kummer

namespace AlgebraicGeometry.Scheme.Kummer

universe u

variable (R A D : Type u) [CommRing R] [CommRing A] [CommRing D]
  [Algebra R A] [Algebra R D] [Algebra.Etale R A]
  [IsDomain D] [IsDiscreteValuationRing D]

/-- The original pointed etale root presentation becomes unramified along a
transverse whole DVR section, without an additional field or lift premise. -/
theorem exponent_eq_one_of_pointedEtalePresentation
    (n : ℕ) (f : R) (hf : Irreducible (algebraMap R D f))
    {Z : Scheme.{u}}
    (π : Spec (.of (RootAlgebra n (algebraMap R A f))) ⟶ Z) [Etale π]
    (p : Z ⟶ Spec (.of R))
    (hc : π ≫ p = Spec.algebraMap A (RootAlgebra n (algebraMap R A f)) ≫
      Spec.algebraMap R A)
    (s : Spec (.of D) ⟶ Z) (hs : s ≫ p = Spec.algebraMap R D)
    (y : Spec (.of (RootAlgebra n (algebraMap R A f))))
    (hy : π y = s (IsLocalRing.closedPoint D)) :
    n = 1 ∧ Etale (π ≫ p) := by
  let c := Spec.algebraMap A (RootAlgebra n (algebraMap R A f))
  have hstalk := exists_transverseEtaleStalk R A D π c p hc s hs y hy hf
  obtain ⟨z, _, _, hdom, hdvr, hirr, a, ha, hbase, _, _⟩ := hstalk
  let T := (pullback π s).presheaf.stalk z
  let : Algebra A T := a.toAlgebra
  let η := (pullback π s).fromSpecStalk z ≫ pullback.fst π s
  have hparameter : algebraMap A T (algebraMap R A f) =
      (pullback.snd π s).stalkScalar z (algebraMap R D f) :=
    RingHom.congr_fun hbase f
  have hfT : Irreducible (algebraMap A T (algebraMap R A f)) := by
    rw [hparameter]
    exact hirr
  have hη : η ≫ c = Spec.algebraMap A T := ha.symm
  have h := exponent_eq_one_and_etale_of_transversePoint A T n (algebraMap R A f)
    hfT c (Iso.refl _) (Category.id_comp _) η hη
  let : Etale c := h.2
  let : Etale (Spec.algebraMap R A) := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  refine ⟨h.1, ?_⟩
  rw [hc]
  exact inferInstanceAs (Etale (c ≫ Spec.algebraMap R A))

end AlgebraicGeometry.Scheme.Kummer
