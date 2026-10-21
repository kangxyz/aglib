/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Aglib.RingTheory.Localization.Away.Torsion

/-! # Affine Néron modifications

The actual divisibility quotient followed by removal of uniformizer-power torsion.
The construction is independent of desingularization and approximation theorems.
-/

@[expose] public section

noncomputable section

namespace Algebra
namespace NeronModification

variable {B C : Type*} [CommRing B] [CommRing C] {ι : Type*}

/-- The actual equations `p * Zᵢ = gᵢ` before removing torsion. -/
def relations (p : B) (g : ι → B) : Ideal (MvPolynomial ι B) :=
  Ideal.span (Set.range fun i => MvPolynomial.C p * MvPolynomial.X i -
    MvPolynomial.C (g i))

/-- The polynomial quotient imposing the divisibility equations. -/
abbrev Raw (p : B) (g : ι → B) := MvPolynomial ι B ⧸ relations p g

/-- The original coefficient map into the divisibility quotient. -/
def rawMap (p : B) (g : ι → B) : B →+* Raw p g :=
  (Ideal.Quotient.mk (relations p g)).comp MvPolynomial.C

/-- A new variable in the divisibility quotient. -/
def rawVariable (p : B) (g : ι → B) (i : ι) : Raw p g :=
  Ideal.Quotient.mk (relations p g) (MvPolynomial.X i)

/-- Each new variable satisfies its defining divisibility equation. -/
theorem rawMap_mul_rawVariable (p : B) (g : ι → B) (i : ι) :
    rawMap p g p * rawVariable p g i = rawMap p g (g i) := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk (relations p g) (MvPolynomial.C p) *
      Ideal.Quotient.mk (relations p g) (MvPolynomial.X i) -
      Ideal.Quotient.mk (relations p g) (MvPolynomial.C (g i)) = 0
  rw [← map_mul, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- Specified divisibility witnesses annihilate the defining relation ideal. -/
theorem relations_le_ker (p : B) (g : ι → B) (f : B →+* C) (z : ι → C)
    (hz : ∀ i, f p * z i = f (g i)) :
    relations p g ≤ RingHom.ker (MvPolynomial.eval₂Hom f z) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change MvPolynomial.eval₂Hom f z
    (MvPolynomial.C p * MvPolynomial.X i - MvPolynomial.C (g i)) = 0
  simp only [map_sub, map_mul, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X', hz, sub_self]

/-- Evaluate the divisibility quotient at the specified divisible point. -/
def rawLift (p : B) (g : ι → B) (f : B →+* C) (z : ι → C)
    (hz : ∀ i, f p * z i = f (g i)) : Raw p g →+* C :=
  Ideal.Quotient.lift (relations p g) (MvPolynomial.eval₂Hom f z)
    (fun _q hq => relations_le_ker p g f z hz hq)

/-- Evaluation of the divisibility quotient preserves the original point. -/
@[simp] theorem rawLift_rawMap (p : B) (g : ι → B) (f : B →+* C)
    (z : ι → C) (hz : ∀ i, f p * z i = f (g i)) (b : B) :
    rawLift p g f z hz (rawMap p g b) = f b := by
  change MvPolynomial.eval₂Hom f z (MvPolynomial.C b) = f b
  exact MvPolynomial.eval₂Hom_C f z b

/-- Evaluation sends each new variable to its specified divisibility witness. -/
@[simp] theorem rawLift_rawVariable (p : B) (g : ι → B) (f : B →+* C)
    (z : ι → C) (hz : ∀ i, f p * z i = f (g i)) (i : ι) :
    rawLift p g f z hz (rawVariable p g i) = z i := by
  change MvPolynomial.eval₂Hom f z (MvPolynomial.X i) = z i
  exact MvPolynomial.eval₂Hom_X' f z i

/-- The affine Néron modification: first impose the divisibility equations,
then remove precisely the uniformizer-power torsion. -/
abbrev Modification (p : B) (g : ι → B) :=
  Raw p g ⧸ RingHom.ker (algebraMap (Raw p g) (Localization.Away (rawMap p g p)))

/-- The quotient map removing precisely the localization kernel. -/
def quotientMap (p : B) (g : ι → B) : Raw p g →+* Modification p g :=
  Ideal.Quotient.mk (RingHom.ker (algebraMap (Raw p g) (Localization.Away (rawMap p g p))))

/-- The original ring map into the modification. -/
def of (p : B) (g : ι → B) : B →+* Modification p g :=
  (quotientMap p g).comp (rawMap p g)

/-- A new variable after removal of uniformizer-power torsion. -/
def coordinate (p : B) (g : ι → B) (i : ι) : Modification p g :=
  quotientMap p g (rawVariable p g i)

/-- Removing the actual localization kernel makes the distinguished element
regular; this is the torsion-removal assertion, not an input hypothesis. -/
theorem isRegular_of (p : B) (g : ι → B) : IsRegular (of p g p) :=
  RingHom.isRegular_mk_ker_localizationAway (rawMap p g p)

/-- The defining divisibility equations remain true after torsion removal. -/
theorem of_mul_coordinate (p : B) (g : ι → B) (i : ι) :
    of p g p * coordinate p g i = of p g (g i) := by
  exact (map_mul (quotientMap p g) _ _).symm.trans
    (congrArg (quotientMap p g) (rawMap_mul_rawVariable p g i))

/-- A specified divisible point has a genuine lift to the actual modification.
Regularity is used only to kill the torsion ideal, not to invert `p`. -/
def lift (p : B) (g : ι → B) (f : B →+* C) (z : ι → C)
    (hz : ∀ i, f p * z i = f (g i)) (hp : IsRegular (f p)) :
    Modification p g →+* C :=
  RingHom.liftAwayTorsion (rawLift p g f z hz) (rawMap p g p)
    (by simpa using hp)

/-- The lifted point agrees with the original point on original coefficients. -/
@[simp] theorem lift_of (p : B) (g : ι → B) (f : B →+* C)
    (z : ι → C) (hz : ∀ i, f p * z i = f (g i)) (hp : IsRegular (f p))
    (b : B) : lift p g f z hz hp (of p g b) = f b := by
  simp [lift, of, quotientMap]

/-- The lifted point has the specified values on the new coordinates. -/
@[simp] theorem lift_coordinate (p : B) (g : ι → B) (f : B →+* C)
    (z : ι → C) (hz : ∀ i, f p * z i = f (g i)) (hp : IsRegular (f p))
    (i : ι) : lift p g f z hz hp (coordinate p g i) = z i := by
  simp [lift, coordinate, quotientMap]

/-- The lifted point factors the original ring map through the modification. -/
@[simp] theorem lift_comp_of (p : B) (g : ι → B) (f : B →+* C)
    (z : ι → C) (hz : ∀ i, f p * z i = f (g i)) (hp : IsRegular (f p)) :
    (lift p g f z hz hp).comp (of p g) = f := by
  ext b
  exact lift_of p g f z hz hp b

/-- The base map determines a point of the modification uniquely when the
image of the distinguished element is regular. -/
theorem lift_unique (p : B) (g : ι → B) (f : B →+* C)
    (z : ι → C) (hz : ∀ i, f p * z i = f (g i)) (hp : IsRegular (f p))
    (ψ : Modification p g →+* C) (hψ : ψ.comp (of p g) = f) :
    ψ = lift p g f z hz hp := by
  have hbase : ∀ b, ψ (of p g b) = f b := fun b => DFunLike.congr_fun hψ b
  have hcoord : ∀ i, ψ (coordinate p g i) = z i := by
    intro i
    apply hp.left
    calc
      f p * ψ (coordinate p g i) = ψ (of p g p * coordinate p g i) := by
        rw [map_mul, hbase]
      _ = ψ (of p g (g i)) := congrArg ψ (of_mul_coordinate p g i)
      _ = f (g i) := hbase _
      _ = f p * z i := (hz i).symm
  have hpoly :
      (ψ.comp (quotientMap p g)).comp (Ideal.Quotient.mk (relations p g)) =
      ((lift p g f z hz hp).comp (quotientMap p g)).comp
        (Ideal.Quotient.mk (relations p g)) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      change ψ (of p g b) = lift p g f z hz hp (of p g b)
      rw [hbase, lift_of]
    · intro i
      change ψ (coordinate p g i) = lift p g f z hz hp (coordinate p g i)
      rw [hcoord, lift_coordinate]
  apply RingHom.ext
  intro x
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact DFunLike.congr_fun hpoly P

end NeronModification
end Algebra
