/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.UnitLocus

/-!
Source: `R5Lab.Aglib.AlgebraicGeometry.Blowup.BasicOpenIsomorphism`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `ad0754a269e502cf8c249f740bdb1ed74eeba86c2f9337534f8f3ef3f68c73da`.
Actual maps and mathematical hypotheses are retained. Conditional family
definitions do not supply blowup existence, properness, base change or an atlas.
-/

@[expose] public section

/-!
# Blowup isomorphism over basic opens

Relocated from R5 baseline `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Existing mathematical declarations and explicit source boundaries are retained.
-/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Blowup

open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.Blowup.Coordinates

lemma blowup_restrict_isIso {A : Type u} [CommRing A] {I : Ideal A}
    {B : BlowupDatum (affineCenter A I)} (H : AffineAtlas A I B) (a : I) :
    IsIso (B.map ∣_ PrimeSpectrum.basicOpen (a : A)) := by
  let e := AlgebraicGeometry.Scheme.Blowup.UnitLocus.unitLocusIso H a
  have he : e.hom ≫ (B.map ∣_ PrimeSpectrum.basicOpen (a : A)) =
      (basicOpenIsoSpecAway (R := .of A) (a : A)).inv := by
    apply (cancel_mono (show (Spec (.of A)).Opens from PrimeSpectrum.basicOpen (a : A)).ι).mp
    rw [Category.assoc, morphismRestrict_ι]
    exact (AlgebraicGeometry.Scheme.Blowup.UnitLocus.unitLocusIso_base_triangle H a).trans
      (IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _).symm
  have hh : IsIso (e.hom ≫ (B.map ∣_ PrimeSpectrum.basicOpen (a : A))) := by
    rw [he]; infer_instance
  exact IsIso.of_isIso_comp_left e.hom _

end AlgebraicGeometry.Scheme.Blowup
