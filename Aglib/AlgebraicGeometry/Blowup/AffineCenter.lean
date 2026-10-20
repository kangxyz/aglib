/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.UniversalProperty

/-!
Source: `R5Lab.Aglib.AlgebraicGeometry.Blowup.AffineCenter`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `10c3448464ece32ba1542723d348eb5f247f3bc4c0ee716210e7b98ce73cc8fa`.
Actual maps and mathematical hypotheses are retained. Conditional family
definitions do not supply blowup existence, properness, base change or an atlas.
-/

@[expose] public section

/-!
# Affine centres of surjective ring maps

Extracted from R5 baseline `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Original declaration names, mathematical hypotheses, and source boundaries are retained.
-/

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Blowup
open AlgebraicGeometry.Scheme.Blowup

/-- The quotient ideal sheaf of the exact kernel of a surjective ring map is
the scheme-theoretic kernel of its actual affine closed immersion. -/
lemma affineCenter_kernel {A K : Type u} [CommRing A] [CommRing K]
    (f : A →+* K) (hf : Function.Surjective f) :
    affineCenter A (RingHom.ker f) = (Spec.map (CommRingCat.ofHom f)).ker := by
  let e := f.quotientKerEquivOfSurjective hf
  let : IsIso (Spec.map (CommRingCat.ofHom e.symm.toRingHom)) := by
    change IsIso (Scheme.Spec.mapIso e.symm.toCommRingCatIso.op).hom
    infer_instance
  have h : Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom f) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker f))) := by
    rw [← Spec.map_comp]
    exact congrArg (fun g => Spec.map (CommRingCat.ofHom g))
      (RingHom.quotientKerEquivOfSurjective_symm_comp hf)
  change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker f)))).ker = _
  rw [← h]
  exact Scheme.Hom.ker_comp_of_isIso _ _

end AlgebraicGeometry.Scheme.Blowup
