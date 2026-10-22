/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.OpenExtension
public import Aglib.AlgebraicGeometry.Blowup.Admissible
public import Aglib.AlgebraicGeometry.Blowup.Construction
public import Aglib.AlgebraicGeometry.Blowup.FlatBaseChange
public import Aglib.AlgebraicGeometry.Blowup.Properness

/-!
# Extension of admissible blowup centres

Extend a centre from a quasi-compact open by its native schematic-image ideal.
This retains the original ideal on that open and the unit ideal on the protected
open. The ordinary blowup construction then supplies the proper modification;
there is no assumed ideal-extension or modification provider.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Blowup

variable {X : Scheme.{u}}

/-- Every original local blowup is the actual Cartesian restriction of the
canonical blowup of the extended centre. The upper map is the existing canonical
base-change map; the left map is the original local structural morphism. -/
theorem extendedCentre_isPullback (V : X.Opens) [QuasiCompact V.ι]
    (J : V.toScheme.IdealSheafData) (B : BlowupDatum J) :
    IsPullback
      (BaseChange.map V.ι (J.comap_map_of_isOpenImmersion V.ι)
        (blowupDatum (J.map V.ι)) B)
      B.map (blowupDatum (J.map V.ι)).map V.ι :=
  BaseChange.isPullback_of_flat V.ι inferInstance
    (J.comap_map_of_isOpenImmersion V.ι) (blowupDatum (J.map V.ι)) B

/-- The canonical blowup of the extended centre is unchanged over the protected
open. The centre is the native schematic-image ideal, with no auxiliary choice. -/
theorem extendedCentre_restrict_isIso (U V : X.Opens) [QuasiCompact V.ι]
    (J : V.toScheme.IdealSheafData) (hJ : J.comap (V.ι ⁻¹ᵁ U).ι = ⊤) :
    IsIso ((blowupDatum (J.map V.ι)).map ∣_ U) :=
  (blowupDatum (J.map V.ι)).restrict_isIso_of_comap_eq_top U
    (J.map_comap_eq_top_of_comap_eq_top V.ι U hJ)

/-- Extension of an admissible centre, with literal ideal restrictions and a
proper native blowup unchanged over the protected open. Quasi-compactness is
needed only for the open immersion from which the centre is extended. -/
theorem exists_admissible_extension [IsLocallyNoetherian X]
    (U V : X.Opens) [QuasiCompact V.ι]
    (J : V.toScheme.IdealSheafData) (hJ : J.comap (V.ι ⁻¹ᵁ U).ι = ⊤) :
    ∃ I : X.IdealSheafData, I.comap V.ι = J ∧ I.comap U.ι = ⊤ ∧
      IsProper (blowupDatum I).map ∧ IsIso ((blowupDatum I).map ∣_ U) := by
  refine ⟨J.map V.ι, J.comap_map_of_isOpenImmersion V.ι,
    J.map_comap_eq_top_of_comap_eq_top V.ι U hJ, ?_,
    extendedCentre_restrict_isIso U V J hJ⟩
  exact (blowupDatum (J.map V.ι)).isProper_of_isLocallyNoetherian

/-- On an arbitrary Noetherian scheme every open centre extends while keeping
a prescribed open unchanged. Nilpotents and reducible schemes are allowed. -/
theorem exists_admissible_extension_of_isNoetherian [IsNoetherian X]
    (U V : X.Opens) (J : V.toScheme.IdealSheafData)
    (hJ : J.comap (V.ι ⁻¹ᵁ U).ι = ⊤) :
    ∃ I : X.IdealSheafData, I.comap V.ι = J ∧ I.comap U.ι = ⊤ ∧
      IsProper (blowupDatum I).map ∧ IsIso ((blowupDatum I).map ∣_ U) :=
  exists_admissible_extension U V J hJ

end AlgebraicGeometry.Scheme.Blowup
