/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Smooth.Fiber

/-!
# Guarded etale descent along a faithfully flat source extension

The intermediate local algebra remains the supplied original ring. Formal
unramifiedness descends through the native differential comparison, and
flatness descends by faithful tensor injectivity. Over a Noetherian local base,
essential finite type supplies the native finite-presentation localization
needed by the smooth-fiber criterion. No arbitrary formal-etale cancellation
without these guards is asserted.
-/

@[expose] public noncomputable section

open TensorProduct
open scoped TensorProduct

universe u

namespace Module.Flat

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- Flatness descends through a faithfully flat extension of the original target. -/
theorem of_faithfullyFlat_target [Module.Flat R T] [Module.FaithfullyFlat S T] :
    Module.Flat R S := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ f hf
  let g := AlgebraTensorModule.lTensor S S f
  have hg : Function.Injective g := by
    apply (Module.FaithfullyFlat.lTensor_injective_iff_injective S T g).mp
    apply Function.Injective.of_comp (f := AlgebraTensorModule.cancelBaseChange R S S T N')
    change Function.Injective
      ((AlgebraTensorModule.cancelBaseChange R S S T N').toLinearMap.comp
        (AlgebraTensorModule.lTensor S T (AlgebraTensorModule.lTensor S S f)))
    rw [← AlgebraTensorModule.lTensor_comp_cancelBaseChange R S S (M := T) f]
    exact (Module.Flat.lTensor_preserves_injective_linearMap f hf).comp
      (AlgebraTensorModule.cancelBaseChange R S S T N).injective
  exact hg

end Module.Flat

namespace Algebra

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- Formal unramifiedness descends through a faithfully flat formally etale
extension of the original target ring. -/
theorem FormallyUnramified.of_formallyEtale_faithfullyFlat_target
    [Module.FaithfullyFlat S T] [FormallyEtale S T] [FormallyUnramified R T] :
    FormallyUnramified R S := by
  have : Subsingleton (T ⊗[S] Ω[S⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).subsingleton
  have : Subsingleton Ω[S⁄R] := Module.FaithfullyFlat.lTensor_reflects_triviality S T _
  exact ⟨inferInstance⟩

/-- A local essentially finite-type flat unramified map over a Noetherian local
base is formally etale. The native finite-type subalgebra only supplies the
finite-presentation witness; the localized ring is the unchanged original ring. -/
theorem FormallyEtale.of_local_flat_formallyUnramified
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R]
    [IsLocalHom (algebraMap R S)] [EssFiniteType R S]
    [Module.Flat R S] [FormallyUnramified R S] : FormallyEtale R S := by
  let P := EssFiniteType.subalgebra R S
  let : Algebra.FinitePresentation R P :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : FormallyUnramified (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] S) := inferInstance
  have : FormallyEtale (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] S) :=
    FormallyEtale.of_formallyUnramified_of_field _ _
  have : FormallySmooth R S :=
    FormallySmooth.of_formallySmooth_residueField_tensor
      (R := R) (S := S) (P := P) (EssFiniteType.submonoid R S)
  exact FormallyEtale.of_formallyUnramified_and_formallySmooth

/-- Guarded source descent on the original local rings. -/
theorem FormallyEtale.of_faithfullyFlat_source_of_noetherian
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R]
    [IsLocalHom (algebraMap R S)] [EssFiniteType R S]
    [Module.Flat R T] [Module.FaithfullyFlat S T]
    [FormallyEtale S T] [FormallyUnramified R T] : FormallyEtale R S := by
  have : Module.Flat R S := Module.Flat.of_faithfullyFlat_target R S T
  have : FormallyUnramified R S :=
    FormallyUnramified.of_formallyEtale_faithfullyFlat_target R S T
  exact FormallyEtale.of_local_flat_formallyUnramified R S

end Algebra
