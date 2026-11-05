/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Smooth.SeparableResiduePointEtaleNeighborhood
public import Mathlib.FieldTheory.Perfect

/-! # Etale sections through the original finite-field-valued point

The kernel of the original base map supplies its actual residue field. That
residue field embeds into the given finite field and is therefore finite and
perfect. The existing separable-residue-point construction then extends the
same smooth-algebra point over a genuine finitely presented etale algebra.
-/

@[expose] public noncomputable section

namespace Algebra.Smooth

universe u

/-- A finite-field-valued point of a smooth algebra extends to a section over
one genuine etale base algebra, retaining the original value map exactly.
The original base need not be Noetherian or arithmetic. -/
theorem exists_etale_lift_of_finite_field
    (R B L : Type u) [CommRing R] [CommRing B] [Field L] [Finite L]
    [Algebra R B] [Algebra R L] [Algebra.Smooth R B] (ψ : B →ₐ[R] L) :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra R E),
      Algebra.Etale R E ∧ ∃ (ε : B →ₐ[R] E) (l : E →ₐ[R] L), l.comp ε = ψ := by
  let p : Ideal R := RingHom.ker (algebraMap R L)
  let : p.IsPrime := RingHom.ker_isPrime _
  have hpunit : p.primeCompl ≤ (IsUnit.submonoid L).comap (algebraMap R L) := by
    intro r hr
    exact isUnit_iff_ne_zero.mpr hr
  let η : p.ResidueField →+* L :=
    Ideal.ResidueField.lift p (algebraMap R L) le_rfl hpunit
  let : Algebra p.ResidueField L := η.toAlgebra
  let : IsScalarTower R p.ResidueField L := IsScalarTower.of_algebraMap_eq fun r =>
    (Ideal.ResidueField.lift_algebraMap p (algebraMap R L) le_rfl hpunit r).symm
  let : Finite p.ResidueField := Finite.of_injective η η.injective
  let : FiniteDimensional p.ResidueField L := Module.Finite.of_finite
  let : Algebra.IsSeparable p.ResidueField L := inferInstance
  obtain ⟨E, hE, hRE, het, ε, l, hε, _⟩ :=
    SeparableResiduePoint.exists_etale_lift R p L B ψ
  exact ⟨E, hE, hRE, het, ε, l, hε⟩

end Algebra.Smooth
