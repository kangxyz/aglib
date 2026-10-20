/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Coherent
public import Aglib.AlgebraicGeometry.Modules.Coherent.Basic
public import Aglib.AlgebraicGeometry.Modules.Exact
public import Aglib.AlgebraicGeometry.Modules.Support

/-!
# The structural finite-pushforward quotient

For arbitrary schemes this constructs the actual map from the unit
module to its pushforward, its cokernel, and the short exact sequence
under schematic dominance. Finite morphisms preserve the displayed
affine finite-type property over locally Noetherian targets. The quotient
has zero stalks wherever the original morphism restricts to an isomorphism;
no dimension, properness, or birationality hypothesis is added.

Source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.ProperCurveFiniteness`, R5 revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`. Existing declaration
namespaces, hypotheses, universes, objects, maps, and proofs are retained.
-/

/- Component: Basic. All declaration bodies preserved. -/

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Coherent.FinitePushforward.Quotient`
at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`1493490e9f65b8bc3d05b12f60c751296eaaac02e994e8ea6eed3fb122ae4f20`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Support
universe u
variable {Y X : Scheme.{u}}

/-- The structural map from the unit module to the pushforward of the source unit module. -/
abbrev unitMap (f : Y ⟶ X) : SheafOfModules.unit X.ringCatSheaf ⟶
    (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

instance unitMap_mono (f : Y ⟶ X) [IsSchemeTheoreticallyDominant f] [QuasiCompact f] :
    Mono (unitMap f) := by
  apply (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U
  exact f.app_injective U.unop

/-- The cokernel of the structural map to the pushed-forward unit module. -/
abbrev quotient (f : Y ⟶ X) : X.Modules := cokernel (unitMap f)
/-- The cokernel short complex of the structural map to the pushed-forward unit module. -/
abbrev sequence (f : Y ⟶ X) : ShortComplex X.Modules :=
  ShortComplex.mk (unitMap f) (cokernel.π (unitMap f)) (cokernel.condition _)

theorem sequence_shortExact (f : Y ⟶ X) [IsSchemeTheoreticallyDominant f]
    [QuasiCompact f] : (sequence f).ShortExact := by
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel (unitMap f)) (unitMap_mono f)
      (by dsimp [sequence]; infer_instance)

theorem unit_coherent (X : Scheme.{u}) :
    Scheme.Modules.QuasiCoherent.affineLocallyFiniteType X
        (SheafOfModules.unit X.ringCatSheaf) := by
  let e : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} Unit) ≅
      SheafOfModules.unit X.ringCatSheaf := coproductUniqueIso _
  exact (Scheme.Modules.QuasiCoherent.affineLocallyFiniteType
      X).prop_of_iso e
    (Scheme.Modules.coherent_of_finiteLocallyFree _)

theorem quotient_coherent (f : Y ⟶ X) [IsFinite f] [IsLocallyNoetherian X] :
    Scheme.Modules.QuasiCoherent.affineLocallyFiniteType X (quotient
        f) := by
  exact (Scheme.Modules.QuasiCoherent.affineLocallyFiniteType
      X).prop_cokernel (unitMap f)
    (unit_coherent X)
    (Scheme.Modules.QuasiCoherent.FiniteMorphism.affineLocallyFiniteType_pushforward f
        (unit_coherent Y))


theorem unitMap_restrict_isIso (f : Y ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (unitMap f)) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro V
  have h : IsIso ((f ∣_ U).app V) := inferInstance
  rw [morphismRestrict_app] at h
  have h' : IsIso (f.app (U.ι ''ᵁ V)) :=
    (isIso_comp_right_iff _ _).mp h
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ConcreteCategory.bijective_of_isIso (f.app (U.ι ''ᵁ V))

theorem quotient_stalk_zero_on_iso_open (f : Y ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)]
    (x : X) (hx : x ∈ U) :
    IsZero ((Scheme.Modules.stalkFunctor X x).obj (quotient f)) := by
  let F := Scheme.Modules.restrictFunctor U.ι
  have : IsIso (F.map (unitMap f)) := unitMap_restrict_isIso f U
  have hq : IsZero (F.obj (quotient f)) :=
    (isZero_cokernel_of_epi (F.map (unitMap f))).of_iso
      (PreservesCokernel.iso F (unitMap f))
  exact ((Scheme.Modules.supportedAway_iff_stalks U.ι (quotient f)).mp
      hq) ⟨x, hx⟩

end AlgebraicGeometry.Scheme.Modules.Coherent.Support

end
