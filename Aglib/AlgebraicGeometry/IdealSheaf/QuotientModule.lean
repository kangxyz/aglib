/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Modules
public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Coefficient
public import Aglib.AlgebraicGeometry.Modules.Coherent.Basic
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.StructureQuotient
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.GeneralPushforward
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Limits

/-!
# The structure module of a closed subscheme

For a closed subscheme `W ⊆ X` (`W : X.IdealSheafData`), `W.quotientModule = 𝒪_X / I_W` is the
cokernel of the actual ideal inclusion `Scheme.Hom.idealInclusion W.subschemeι`, with projection
`W.toQuotientModule : 𝒪_X ⟶ 𝒪_X / I_W`.

* `Scheme.IdealSheafData.shortComplex_shortExact`: `0 → I_W → 𝒪_X → 𝒪_W → 0` is short exact.
* `Scheme.IdealSheafData.quotientModuleIsoPushforward`: `𝒪_X / I_W ≅ i_* 𝒪_W`, since `I_W` is the
  kernel of the epimorphism `𝒪_X ⟶ i_* 𝒪_W` (`Scheme.Hom.structureModuleMap_epi`,
  `Modules/ClosedImmersion/StructureQuotient`); hence `𝒪_X / I_W` is quasi-coherent
  (`quotientModule_isQuasicoherent`).
* `Scheme.Hom.affineLocallyFiniteType_idealModule`, `affineLocallyFiniteType_quotientModule`: on a
  locally Noetherian scheme the actual ideal module of a closed immersion and the structure module
  of a closed subscheme are coherent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The structure module `𝒪_X / I_W` of a closed subscheme `W ⊆ X`, as a module on `X`: the
cokernel of the actual ideal inclusion `Scheme.Hom.idealInclusion W.subschemeι`. -/
def quotientModule (W : X.IdealSheafData) : X.Modules :=
  cokernel (Scheme.Hom.idealInclusion W.subschemeι)

/-- The projection `𝒪_X ⟶ 𝒪_X / I_W`. -/
def toQuotientModule (W : X.IdealSheafData) :
    (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ W.quotientModule :=
  cokernel.π (Scheme.Hom.idealInclusion W.subschemeι)

/-- The sequence `I_W ⟶ 𝒪_X ⟶ 𝒪_W` of a closed subscheme. -/
def shortComplex (W : X.IdealSheafData) : ShortComplex X.Modules :=
  ShortComplex.mk (Scheme.Hom.idealInclusion W.subschemeι) W.toQuotientModule
    (cokernel.condition _)

/-- **`0 → I_W → 𝒪_X → 𝒪_W → 0` is short exact.** -/
theorem shortComplex_shortExact (W : X.IdealSheafData) : W.shortComplex.ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
  mono_f := Scheme.Hom.idealInclusionMono _
  epi_g := coequalizer.π_epi

end Scheme.IdealSheafData

/-- The actual ideal module of a closed immersion into a locally Noetherian scheme is coherent:
it is the kernel of `𝒪_X ⟶ i_* 𝒪_D`, a map of coherent modules. -/
theorem Scheme.Hom.affineLocallyFiniteType_idealModule {X D : Scheme.{u}}
    [IsLocallyNoetherian X] (i : D ⟶ X) [IsClosedImmersion i] :
    Scheme.Modules.QuasiCoherent.affineLocallyFiniteType X (Scheme.Hom.idealModule i) :=
  (Scheme.Modules.QuasiCoherent.affineLocallyFiniteType X).prop_kernel
    (Scheme.Hom.structureModuleMap i)
    (Scheme.Modules.affineLocallyFiniteType_unit X)
    (Scheme.Modules.Coherent.Pushforward.ClosedImmersion.affineLocallyFiniteType_pushforward i
      (Scheme.Modules.affineLocallyFiniteType_unit D))

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- **The structure module of a closed subscheme is the pushforward of its structure sheaf**:
`𝒪_X / I_W ≅ i_* 𝒪_W`, since `I_W` is the kernel of the epimorphism `𝒪_X ⟶ i_* 𝒪_W`. -/
def quotientModuleIsoPushforward (W : X.IdealSheafData) :
    W.quotientModule ≅ (Scheme.Modules.pushforward W.subschemeι).obj
      (SheafOfModules.unit W.subscheme.ringCatSheaf) :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
    (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel (Scheme.Hom.structureModuleMap W.subschemeι)))

/-- The structure module of a closed subscheme is quasi-coherent: it is the pushforward of the
structure sheaf along the closed immersion (`quotientModuleIsoPushforward`). -/
theorem quotientModule_isQuasicoherent (W : X.IdealSheafData) :
    W.quotientModule.IsQuasicoherent := by
  have hP := Scheme.Modules.Coherent.Pushforward.ClosedImmersion.affineLocallyFiniteType_pushforward
    W.subschemeι (Scheme.Modules.affineLocallyFiniteType_unit W.subscheme)
  have : ((Scheme.Modules.pushforward W.subschemeι).obj
      (SheafOfModules.unit W.subscheme.ringCatSheaf)).IsQuasicoherent :=
    Scheme.Modules.QuasiCoherent.quasicoherent_of_affineCharts _ (fun R j _ => (hP R j).1)
  exact (SheafOfModules.isQuasicoherent _).prop_of_iso W.quotientModuleIsoPushforward.symm this

/-- The structure module of a closed subscheme of a locally Noetherian scheme is coherent. -/
theorem affineLocallyFiniteType_quotientModule [IsLocallyNoetherian X] (W : X.IdealSheafData) :
    Scheme.Modules.QuasiCoherent.affineLocallyFiniteType X W.quotientModule :=
  (Scheme.Modules.QuasiCoherent.affineLocallyFiniteType X).prop_cokernel
    (Scheme.Hom.idealInclusion W.subschemeι)
    (Scheme.Hom.affineLocallyFiniteType_idealModule W.subschemeι)
    (Scheme.Modules.affineLocallyFiniteType_unit X)

end Scheme.IdealSheafData

end AlgebraicGeometry
