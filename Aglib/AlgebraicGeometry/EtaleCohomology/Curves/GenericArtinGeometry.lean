/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericArtin

/-!
# Finiteness properties of the actual generic Artin locus

Each component has one topological point but retains its entire stalk ring.
For a Noetherian scheme the actual coproduct is a finite, locally Artinian
scheme, and its map to the original scheme is quasi-compact and quasi-separated.
The map is not asserted finite or of finite type.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u
variable (X : Scheme.{u})

/-- The spectrum of an original component-generic stalk has one point topologically. -/
instance genericArtinComponent_subsingleton (η : genericPoints X) :
    Subsingleton (genericArtinComponent X η) := by
  let : Ring.KrullDimLE 0 (X.presheaf.stalk η.val) := genericStalk_krullDimLE_zero X η
  exact Ring.KrullDimLE.subsingleton_primeSpectrum (X.presheaf.stalk η.val)

/-- The actual generic infinitesimal neighborhood is locally Artinian. -/
instance genericArtinComponent_isLocallyArtinian [IsLocallyNoetherian X]
    (η : genericPoints X) : IsLocallyArtinian (genericArtinComponent X η) :=
  Scheme.isLocallyArtinianScheme_Spec.mpr (genericStalk_isArtinian X η)

/-- The actual coproduct is locally Artinian, with no reduction of its stalk rings. -/
instance genericArtinLocus_isLocallyArtinian [IsLocallyNoetherian X] :
    IsLocallyArtinian (genericArtinLocus X) :=
  (isLocallyArtinian_iff_openCover (sigmaOpenCover (genericArtinComponent X))).mpr
    (fun η => by
      change IsLocallyArtinian (genericArtinComponent X η)
      exact genericArtinComponent_isLocallyArtinian X η)

/-- A Noetherian scheme has a topologically finite generic Artin locus. -/
instance genericArtinLocus_finite [IsNoetherian X] : Finite (genericArtinLocus X) :=
  Finite.of_equiv (Σ η : genericPoints X, genericArtinComponent X η)
    (sigmaMk (genericArtinComponent X)).toEquiv

/-- The generic Artin source is Noetherian; the original base need only be Noetherian. -/
instance genericArtinLocus_isNoetherian [IsNoetherian X] :
    IsNoetherian (genericArtinLocus X) := ⟨⟩

/-- The original generic map is quasi-compact, not necessarily finite. -/
instance genericArtinMap_quasiCompact [IsNoetherian X] :
    QuasiCompact (genericArtinMap X) := inferInstance

/-- The original generic map is quasi-separated. -/
instance genericArtinMap_quasiSeparated [IsNoetherian X] :
    QuasiSeparated (genericArtinMap X) := inferInstance

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
