/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.DivisorInverse

/-!
# Effective divisor classes and nonzero sections

For the existing divisor and line-bundle realizations on an integral
Noetherian curve with closed DVR stalks, a line-bundle class has an effective
divisor representative exactly when the actual line bundle has a nonzero
global section. No degree, genus, field, or Riemann--Roch inequality enters
this equivalence. The theta effective-locus argument consumes both directions.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open Scheme Scheme.Modules.Invertible
open Scheme.OverField.Curve.Divisors

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Picard

open DivisorClass DivisorInverse

variable (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
  [∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
  (hdim : topologicalKrullDim X ≤ 1)

-- Evaluation retains the native module-sheaf and presheaf presentations.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A nonzero section supplies an effective representative of the original
line-bundle class, in arbitrary degree. -/
theorem exists_effective_divisor_class_of_nonzero_section (L : LineBundle X)
    (s : L.val.val.obj (op ⊤)) (hs : s ≠ 0) :
    ∃ D : Divisor X, (∀ x, 0 ≤ D x) ∧ divisorToPicard X hdim D = classOf X L := by
  obtain ⟨D, ⟨e⟩⟩ := exists_divisor_iso X L.val L.property hdim
  let q : L.val.val.obj (op ⊤) ≃ₗ[Γ(X, ⊤)]
      (divisorSheaf X D).val.obj (op ⊤) :=
    ((PresheafOfModules.evaluation X.ringCatSheaf.obj (op ⊤)).mapIso
      ((SheafOfModules.forget _).mapIso e)).toLinearEquiv
  have hqs : q s ≠ 0 := fun hz => hs (q.injective (hz.trans q.map_zero.symm))
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  let z : fractionalSections X D ⊤ := (divisorSheafSectionsEquiv X D ⊤) (q s)
  have hz : (z : X.functionField) ≠ 0 := by
    intro hz
    apply hqs
    apply (divisorSheafSectionsEquiv X D ⊤).injective
    exact (Subtype.ext hz).trans (divisorSheafSectionsEquiv X D ⊤).map_zero.symm
  let f : X.functionFieldˣ := Units.mk0 (z : X.functionField) hz
  refine ⟨principal X (Additive.ofMul f) + D, ?_, ?_⟩
  · intro x
    exact z.property.resolve_left hz x trivial
  · rw [map_add, divisorToPicard_principal, zero_add]
    exact Quotient.sound ⟨e.symm⟩

-- Match the actual fractional-section module with its sheaf-section presentation.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An effective divisor has the nonzero rational section one in its
original fractional-ideal sheaf. -/
theorem divisorSheaf_exists_nonzero_section_of_effective
    (D : Divisor X) (hD : ∀ x, 0 ≤ D x) :
    ∃ s : (divisorSheaf X D).val.obj (op ⊤), s ≠ 0 := by
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  let z : fractionalSections X D ⊤ := ⟨1, Or.inr fun x _ => by
    have h : X.ord (1 : X.functionField) x.val = 0 := (localOrder X x).map_zero
    simpa only [h, zero_add] using hD x⟩
  refine ⟨(divisorSheafSectionsEquiv X D ⊤).symm z, ?_⟩
  intro hs
  have hz : z = 0 := by
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using
      congrArg (divisorSheafSectionsEquiv X D ⊤) hs
  exact one_ne_zero (congrArg Subtype.val hz)

-- The class equality supplies the actual module isomorphism used at evaluation.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Effectivity of the original line-bundle class is equivalent to existence
of a nonzero section of that actual bundle. -/
theorem exists_nonzero_section_iff_effective_class (L : LineBundle X) :
    (∃ s : L.val.val.obj (op ⊤), s ≠ 0) ↔
      ∃ D : Divisor X, (∀ x, 0 ≤ D x) ∧ divisorToPicard X hdim D = classOf X L := by
  constructor
  · rintro ⟨s, hs⟩
    exact exists_effective_divisor_class_of_nonzero_section X hdim L s hs
  · rintro ⟨D, hD, hclass⟩
    obtain ⟨e⟩ := (class_eq_iff X (divisorLineBundle X hdim D) L).mp hclass
    let q : (divisorSheaf X D).val.obj (op ⊤) ≃ₗ[Γ(X, ⊤)] L.val.val.obj (op ⊤) :=
      ((PresheafOfModules.evaluation X.ringCatSheaf.obj (op ⊤)).mapIso
        ((SheafOfModules.forget _).mapIso e)).toLinearEquiv
    obtain ⟨s, hs⟩ := divisorSheaf_exists_nonzero_section_of_effective X D hD
    exact ⟨q s, fun hz => hs (q.injective (hz.trans q.map_zero.symm))⟩

end AlgebraicGeometry.Scheme.OverField.Curve.Picard
