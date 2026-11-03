/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Integral
public import Aglib.AlgebraicGeometry.Cohomology.Blowup.RegularPoint.OnePoleDerived
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.ProperTransposeCoefficient
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.ExteriorCoefficient
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.FiniteType
public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.Affine
public import Aglib.AlgebraicGeometry.Modules.Invertible.Bidual.Affine
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Locality
public import Aglib.AlgebraicGeometry.Stalk.GenericPoint


/-!
# Original canonical coefficients across a regular point blowup

The original one-pole derived map supplies the coefficient equation required
by proper Serre transposition. Global local finite type supplies coherence of
the actual raw exterior sheaf and upstairs bidual. The resulting ordinary
canonical trace square is a conclusion, not an additional input.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Blowup AlgebraicGeometry.Scheme.Blowup.RegularPoint
open AlgebraicGeometry.Scheme.Cohomology

universe u vK


open AlgebraicGeometry.Scheme.Modules.Differentials

namespace AlgebraicGeometry.Scheme.Blowup.RegularPoint

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  {Λ A : CommRingCat.{u}} [IsDomain A] [IsRegularLocalRing A]
  (ρ : Λ ⟶ A) (β : X ⟶ Spec A) [IsDominant β]
  [LocallyOfFiniteType (β ≫ Spec.map ρ)]
  (K : Type vK) [Field K] [Algebra A K] [IsFractionRing A K]
  (hβ : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap β)))
  (hX : RegularStalks X) (p : X) (hp : IsClosed ({p} : Set X))
  (hd : ringKrullDim (X.presheaf.stalk p) = 2)
  (n : ℕ) (L : LineBundle X)
  (φ : moduleExteriorPower X (relativeDifferentialSheaf (β ≫ Spec.map ρ)) n ⟶ L.val)

local notation "a" => β ≫ Spec.map ρ
local notation "Y" => pointBlowup X p
local notation "b" => pointBlowdown X p
local notation "MX" => moduleExteriorPower X (relativeDifferentialSheaf a) n
local notation "MY" => moduleExteriorPower Y (relativeDifferentialSheaf (b ≫ a)) n
local notation "DY" => dualSheaf Y (dualSheaf Y MY)

local instance pointCanonicalProper : IsProper b :=
  (pointBlowupDatum X p).isProper_of_isLocallyNoetherian

local instance pointCanonicalLocallyNoetherian : IsLocallyNoetherian Y :=
  LocallyOfFiniteType.isLocallyNoetherian b

omit [IsIntegral X] [IsLocallyNoetherian X] [IsDomain A] [IsRegularLocalRing A]
    [IsDominant β] in
private theorem pointCanonicalRaw_coherent : affineLocallyFiniteType X MX :=
  moduleExteriorPower_affineLocallyFiniteType _
    (relativeDifferentialSheaf_affineLocallyFiniteType a) n

omit [IsIntegral X] [IsDomain A] [IsRegularLocalRing A] [IsDominant β] in
theorem pointCanonicalBidual_coherent : affineLocallyFiniteType Y DY := by
  have hMY : affineLocallyFiniteType Y MY :=
    moduleExteriorPower_affineLocallyFiniteType _
      (relativeDifferentialSheaf_affineLocallyFiniteType (b ≫ a)) n
  exact affineLocallyFiniteType_bidualSheaf MY hMY

local instance pointCanonicalRawQuasicoherent : (MX).IsQuasicoherent :=
  quasicoherent_of_affineLocallyFiniteType (pointCanonicalRaw_coherent ρ β n)

local instance pointCanonicalBidualQuasicoherent : (DY).IsQuasicoherent :=
  quasicoherent_of_affineLocallyFiniteType (pointCanonicalBidual_coherent ρ β p n)

variable (ιX ιY : Type u)
  (iX : X ⟶ ProjectiveSpace A ιX) [IsClosedImmersion iX]
  [IsDominant (iX ≫ toSpec A ιX)]
  (iY : pointBlowup X p ⟶ ProjectiveSpace A ιY) [IsClosedImmersion iY]
  [IsDominant (iY ≫ toSpec A ιY)]
  (hb : iY ≫ toSpec A ιY = pointBlowdown X p ≫ (iX ≫ toSpec A ιX))
  (hNX : NormalStalks X) (hXdim : topologicalKrullDim X ≤ 2)
  (hNY : NormalStalks (pointBlowup X p)) (hYdim : topologicalKrullDim (pointBlowup X p) ≤ 2)
  (nX nY : ℕ) (eX : ιX ≃ Fin (nX + 1)) (eY : ιY ≃ Fin (nY + 1))
  (hfinX : (genericImageBaseMap A ιX iX).Finite)
  (hfinY : letI : IsIntegral (pointBlowup X p) :=
      pointBlowup_isIntegral X p hp (ne_genericPoint_of_stalk_dimension_two p hd)
    (genericImageBaseMap A ιY iY).Finite)
  (ΦX : L.val ⟶ normalSurfaceCanonicalModule A ιX iX nX)

/-- The existing proper Serre transpose of the original one-pole derived map.
The upstairs source is the original bidual, not an independently selected line. -/
def modelPointOnePoleCanonicalCoefficient :
    letI : IsIntegral Y :=
      pointBlowup_isIntegral X p hp (ne_genericPoint_of_stalk_dimension_two p hd)
    DY ⟶ normalSurfaceCanonicalModule A ιY iY nY := by
  letI : IsIntegral Y :=
    pointBlowup_isIntegral X p hp (ne_genericPoint_of_stalk_dimension_two p hd)
  exact normalSurfaceProperSerreTranspose A ιX ιY b iX iY hb
    hNX hXdim hNY hYdim nX nY eX eY hfinX hfinY L.val DY
    (pointCanonicalBidual_coherent ρ β p n)
    (modelPointOnePoleDerivedMap ρ β K hβ hX p hp hd n L φ) ΦX

/-- The actual raw coefficient square for a point step. Its derived premise is
proved by the original one-pole map and coefficient-tensored exceptional rho. -/
theorem modelPointOnePoleCanonicalCoefficient_trace :
    letI : IsIntegral Y :=
      pointBlowup_isIntegral X p hp (ne_genericPoint_of_stalk_dimension_two p hd)
    bidualFormsCoefficient a b n ≫ (pushforward b).map
      (modelPointOnePoleCanonicalCoefficient ρ β K hβ hX p hp hd n L φ
        ιX ιY iX iY hb hNX hXdim hNY hYdim nX nY eX eY hfinX hfinY ΦX) ≫
      normalSurfaceProperCanonicalTrace A ιX ιY b iX iY hb
        hNX hXdim hNY hYdim nX nY eX eY hfinX hfinY = φ ≫ ΦX := by
  let : IsIntegral Y :=
    pointBlowup_isIntegral X p hp (ne_genericPoint_of_stalk_dimension_two p hd)
  exact normalSurfaceProperSerreTranspose_coefficient A ιX ιY b iX iY hb
    hNX hXdim hNY hYdim nX nY eX eY hfinX hfinY MX L.val DY
    (pointCanonicalRaw_coherent ρ β n) (pointCanonicalBidual_coherent ρ β p n)
    (bidualFormsCoefficient a b n) φ
    (modelPointOnePoleDerivedMap ρ β K hβ hX p hp hd n L φ)
    (modelPointOnePoleDerivedMap_coefficient ρ β K hβ hX p hp hd n L φ) ΦX

end AlgebraicGeometry.Scheme.Blowup.RegularPoint
