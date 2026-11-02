/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.AffineBase
public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedBlowupCover

/-!
# An original nonzero ideal on an actual normalized-point chain

The existing native ordinary ideal blowup is dominated by the existing
normalized-point construction. Its original Cartier image pulls back
through the actual dominant comparison, without flatness. The original
structural and ideal-comap triangles identify the terminal image ideal.
No regularity of the base or terminal, or resolution theorem, is used.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Blowup

universe u

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination

/-- An actual normalized-point chain makes the SAME nonzero ideal's original
image locally rank one over a normal Nagata domain of dimension at most two.
The terminal remains merely normal; both original comparison triangles and
function-field isomorphisms are retained. -/
theorem exists_ideal_image_isLocallyRankOne_of_nagata_base
    (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (hA : IsNagataRing.{u, 0} A) (hdA : ringKrullDim A ≤ 2)
    (J : Ideal A) (hJ : J ≠ ⊥) :
    ∃ (T : Scheme.{u}) (beta : T ⟶ Spec (.of A))
      (a : T ⟶ Birational.NormalizedBlowupCover.Base.source A J hJ) (hT : IsIntegral T),
      letI := hT
      ∃ (hbeta : IsDominant beta) (ha : IsDominant a),
        letI := hbeta
        letI := ha
        ∃ (_ : NormalizedPointBlowupChain beta),
          a ≫ Birational.NormalizedBlowupCover.Base.map A J hJ = beta ∧
            NormalStalks T ∧ IsNoetherian T ∧ topologicalKrullDim T ≤ 2 ∧
            IsProper beta ∧ IsProper a ∧
            IsIso (CommRingCat.ofHom (functionFieldMap beta)) ∧
            IsIso (CommRingCat.ofHom (functionFieldMap a)) ∧
            (Birational.NormalizedBlowupCover.Base.ordinaryIdeal A J hJ).comap a =
              (affineCenter A J).comap beta ∧
            Modules.Invertible.IsLocallyRankOne T
              (Hom.idealModule ((affineCenter A J).comap beta).subschemeι) := by
  let : IsNoetherianRing A := hA.isNoetherianRing
  obtain ⟨T, beta, a, hT, hbeta, ha, c, htriangle, hTN, hTNoeth, hdT, hbetaP, haP,
    hbetaff, haff⟩ := exists_domination_of_nagata_base A hA hdA
      (Birational.NormalizedBlowupCover.Base.map A J hJ)
      (Birational.NormalizedBlowupCover.Base.map_fieldMap_isIso A J hJ)
  let : IsIntegral T := hT
  let : IsDominant beta := hbeta
  let : IsDominant a := ha
  have himage : (Birational.NormalizedBlowupCover.Base.ordinaryIdeal A J hJ).comap a =
      (affineCenter A J).comap beta := by
    change ((affineCenter A J).comap
      (Birational.NormalizedBlowupCover.Base.map A J hJ)).comap a = _
    rw [← IdealSheafData.comap_comp, htriangle]
  have hline := Birational.NormalizedBlowupCover.imageIdeal_isLocallyRankOne
    (Birational.NormalizedBlowupCover.Base.ordinaryIdeal A J hJ) a
    (Birational.NormalizedBlowupCover.Base.ordinaryIdeal_generic_avoidance A J hJ)
    (Birational.NormalizedBlowupCover.Base.datum A J).cartier
  rw [himage] at hline
  exact ⟨T, beta, a, hT, hbeta, ha, c, htriangle, hTN, hTNoeth, hdT,
    hbetaP, haP, hbetaff, haff, himage, hline⟩

end AlgebraicGeometry.Scheme.NormalizedPointDomination
