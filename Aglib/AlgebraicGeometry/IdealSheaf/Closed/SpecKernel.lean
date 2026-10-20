/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Affine kernel ideal on global sections

Source: `R5Lab.Aglib.AlgebraicGeometry.IdealSheaf.SpecKernel`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `3ef09436fe668207b58f8d12d2b810d5846d028805ebc04607cd4523fad01dae`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

open Scheme.IdealSheafData

/-- On an actual spectrum, the native kernel ideal is the original ring kernel
transported by the canonical global-sections isomorphism. -/
theorem specMap_kernel_top {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) :
    (Spec.map (CommRingCat.ofHom f)).ker.ideal ⟨⊤, isAffineOpen_top _⟩ =
      (RingHom.ker f).comap (Scheme.ΓSpecIso (.of A)).hom.hom := by
  rw [Scheme.ker_of_isAffine]
  simp only [ofIdealTop_ideal, homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
    CommRingCat.hom_id, Ideal.map_id]
  ext x
  change (Spec.map (CommRingCat.ofHom f)).appTop x = 0 ↔
    f ((Scheme.ΓSpecIso (.of A)).hom x) = 0
  have he := congrArg (fun g : Γ(Spec (.of A), ⊤) ⟶ CommRingCat.of B => g x)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
  change (Scheme.ΓSpecIso (.of B)).hom ((Spec.map (CommRingCat.ofHom f)).appTop x) =
    f ((Scheme.ΓSpecIso (.of A)).hom x) at he
  rw [← he]
  exact (map_eq_zero_iff _ (Scheme.ΓSpecIso (.of B)).commRingCatIsoToRingEquiv.injective).symm

end AlgebraicGeometry.Scheme.IdealSheafData
