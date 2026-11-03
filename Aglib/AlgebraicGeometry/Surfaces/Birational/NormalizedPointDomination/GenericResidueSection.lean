/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.CurveResidue

/-!
# Transporting the selected section through the original generic residue field

Pullback of an affine section along the original dominant field point is
injective. Its scalar equation is obtained from the original scheme triangle
on actual section maps. This produces a residue-transcendental element in
the original ambient stalk, not in an unrelated chosen function field.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination

universe u

private theorem appLE_top_eq_appTop {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens)) : f.appLE ⊤ ⊤ h = f.appTop :=
  f.appLE_eq_app

private theorem exists_transcendental_of_dominant_fieldPoint
    {K L : Type u} [Field K] [Field L] {D : Scheme.{u}} [IsIntegral D]
    (j : Spec (.of L) ⟶ D) [IsDominant j]
    (q : D ⟶ Spec (.of K)) (φ : K →+* L)
    (w : j ≫ q = Spec.map (CommRingCat.ofHom φ))
    (U : D.Opens) [Nonempty U] (a : Γ(D, U))
    (ha : letI : Algebra K Γ(D, U) := (constantSection (Over.mk q) U).toAlgebra
      Transcendental K a) :
    letI := φ.toAlgebra
    ∃ b : L, Transcendental K b := by
  let : Algebra K Γ(D, U) := (constantSection (Over.mk q) U).toAlgebra
  let : Algebra K L := φ.toAlgebra
  let : Nonempty (⊤ : (Spec (.of L)).Opens) := ⟨⟨genericPoint _, trivial⟩⟩
  have hη : genericPoint D ∈ U :=
    ((genericPoint_spec D).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hpre : (⊤ : (Spec (.of L)).Opens) ≤ j ⁻¹ᵁ U := by
    intro z _
    change j z ∈ U
    have hz : z = genericPoint (Spec (.of L)) := Subsingleton.elim _ _
    rw [hz, map_genericPoint_of_isDominant (Spec (.of L)) j]
    exact hη
  let ψ : Γ(D, U) →+* L :=
    (Scheme.ΓSpecIso (.of L)).hom.hom.comp (j.appLE U ⊤ hpre).hom
  let : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isDominant j
  have hψ : Function.Injective ψ :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of L)).hom).1.comp
      ((map_injective_of_isIntegral (Spec (.of L)) (homOfLE hpre)).comp (j.app_injective U))
  have hscalar : ψ.comp (constantSection (Over.mk q) U) = φ := by
    suffices he : CommRingCat.ofHom (ψ.comp (constantSection (Over.mk q) U)) =
        CommRingCat.ofHom φ from congrArg CommRingCat.Hom.hom he
    change (Scheme.ΓSpecIso (.of K)).inv ≫ q.appLE ⊤ U le_top ≫
      j.appLE U ⊤ hpre ≫ (Scheme.ΓSpecIso (.of L)).hom = CommRingCat.ofHom φ
    rw [Hom.appLE_comp_appLE_assoc, w]
    rw [appLE_top_eq_appTop, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  refine ⟨ψ a, ha.ringHom_of_comp_eq (RingHom.id K) ψ Function.surjective_id hψ ?_⟩
  change φ.comp (RingHom.id K) = ψ.comp (constantSection (Over.mk q) U)
  rw [RingHom.comp_id]
  exact hscalar.symm

/-- The original generic stalk of an actual contracted curve contains an
element whose original residue is transcendental for the original morphism's
residue-field map. The selected element is obtained by lifting through the
actual residue quotient. -/
theorem exists_transcendental_curve_residue
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p]
    (C : IrreducibleCloseds X) (hC : C ∈ contractedCurves p) :
    ∃ u : X.presheaf.stalk C.isIrreducible.genericPoint,
      letI := (p.residueFieldMap C.isIrreducible.genericPoint).hom.toAlgebra
      Transcendental (Y.residueField (p C.isIrreducible.genericPoint))
        (X.residue C.isIrreducible.genericPoint u) := by
  obtain ⟨U, hU, a, ha, _⟩ := CurveResidue.exists_affine_transcendental_unit p C hC
  let : Nonempty U.1 := hU
  obtain ⟨b, hb⟩ := exists_transcendental_of_dominant_fieldPoint
    (CurveResidue.fromGeneric C) (CurveResidue.toPoint p C hC)
    (p.residueFieldMap C.isIrreducible.genericPoint).hom
    (CurveResidue.fromGeneric_toPoint p C hC) U.1 a ha
  obtain ⟨u, hu⟩ := IsLocalRing.residue_surjective
    (R := X.presheaf.stalk C.isIrreducible.genericPoint) b
  refine ⟨u, ?_⟩
  have hu' : X.residue C.isIrreducible.genericPoint u = b := hu
  rw [hu']
  exact hb

end AlgebraicGeometry.Scheme.NormalizedPointDomination
