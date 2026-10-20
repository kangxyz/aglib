/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AffineAtlas
public import Aglib.AlgebraicGeometry.Blowup.FlatBaseChange
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Properness of every universal blowup over a locally Noetherian scheme

On spectra, the original Rees Proj map is proper and the unique comparison
transfers this to every given universal representative. Properness is local on
the target; the proved flat-base-change datum supplies the actual pullbacks over
an affine open cover. No global existence theorem is assumed.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Blowup

/-- Every given universal blowup of an actual ideal sheaf on a Noetherian spectrum is
proper, by comparison with the original proper Rees Proj map. -/
theorem BlowupDatum.isProper_of_spectrum {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : (Spec (.of A)).IdealSheafData} (B : BlowupDatum I) : IsProper B.map := by
  have : IsProper (spectrumDatum I).map := inferInstanceAs
    (IsProper (affineProjMap (spectrumIdeal I)))
  exact BlowupDatum.proper_of_comparison (spectrumDatum I) B

/-- Every given universal blowup over a locally Noetherian scheme is proper. Its affine
pullbacks are the literal base changes and have the original inverse-image centres. -/
theorem BlowupDatum.isProper_of_isLocallyNoetherian {X : Scheme.{u}}
    [IsLocallyNoetherian X] {I : X.IdealSheafData} (B : BlowupDatum I) : IsProper B.map := by
  let C := Scheme.OpenCover.affineRefinement X.affineCover
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsProper) C.openCover
  intro i
  have : IsLocallyNoetherian (Spec (C.X i)) := isLocallyNoetherian_of_isOpenImmersion (C.f i)
  have hN : IsNoetherianRing (C.X i) := isLocallyNoetherian_Spec.mp inferInstance
  exact @BlowupDatum.isProper_of_spectrum (C.X i) inferInstance hN _
    (flatPullbackDatum B (C.f i))

/-- The exact original locally Noetherian blowup-properness family is supplied by affine
properness, actual flat base change and Zariski locality on the target. -/
theorem noetherianBlowupProper : NoetherianBlowupProper.{u} := by
  intro X _ I B
  exact B.isProper_of_isLocallyNoetherian

end AlgebraicGeometry.Scheme.Blowup
