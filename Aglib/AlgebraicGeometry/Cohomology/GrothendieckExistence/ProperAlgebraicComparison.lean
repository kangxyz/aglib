/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.BoundedDefect
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Cartesian
public import Aglib.AlgebraicGeometry.Modules.IsomorphismFunctors
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Proper.Coherent

/-!
# Bounded defects of the algebraic proper-modification comparison

For an actual algebraic coefficient, the adjoint of a pullback isomorphism
has uniformly annihilated kernel and cokernel on the modification boundary.
This is the algebraic comparison needed after affine completion in the
formal comparison argument; it is not effectivity of a formal system.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The adjoint of a pullback isomorphism is invertible on every open over
which the original scheme morphism is an isomorphism. -/
theorem pullbackIso_adjoint_restrict_isIso {Y X : Scheme.{u}} (f : Y ⟶ X)
    (U : X.Opens) [IsIso (f ∣_ U)] {G : X.Modules} {F : Y.Modules}
    (e : (pullback f).obj G ≅ F) :
    IsIso ((restrictFunctor U.ι).map
      ((pullbackPushforwardAdjunction f).homEquiv _ _ e.hom)) := by
  let b := f ∣_ U
  let := pullback_isEquivalence_of_isIso b
  let := pushforward_isEquivalence_of_isIso b
  let T := cartesianAdjointTargetIso (f ⁻¹ᵁ U).ι b f U.ι
    (isPullback_morphismRestrict f U).flip e
  have heq := cartesianAdjointTargetIso_homEquiv (f ⁻¹ᵁ U).ι b f U.ι
    (isPullback_morphismRestrict f U).flip e
  have hi : IsIso ((pullbackPushforwardAdjunction b).unit.app
      ((restrictFunctor U.ι).obj G)) := by infer_instance
  have hc : IsIso (((restrictFunctor U.ι).map
      ((pullbackPushforwardAdjunction f).homEquiv _ _ e.hom)) ≫ T.hom) :=
    heq.symm ▸ hi
  exact IsIso.of_isIso_comp_right _ T.hom

/-- Coherent proper pushforward in ordinary degree zero, through the
original degree-zero comparison. -/
theorem properPushforward_coherent {Y X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : Y ⟶ X) [IsProper f] (F : Y.Modules)
    (hF : QuasiCoherent.affineLocallyFiniteType Y F) :
    QuasiCoherent.affineLocallyFiniteType X ((pushforward f).obj F) :=
  (QuasiCoherent.affineLocallyFiniteType X).prop_of_iso
    (((pushforward f).rightDerivedZeroIsoSelf).app F)
    (moduleHigherDirectImage_coherent_of_proper f F hF 0)

/-- The actual algebraic adjoint comparison for a proper modification has
one positive exceptional-ideal power killing both defects. -/
theorem exists_pos_pow_killedByIdealSheaf_pullbackIso_adjoint
    {Y X : Scheme.{u}} [IsNoetherian X] (f : Y ⟶ X) [IsProper f]
    (I : X.IdealSheafData) (U : X.Opens) [IsIso (f ∣_ U)]
    (hU : (U : Set X)ᶜ ⊆ I.support)
    {G : X.Modules} {F : Y.Modules}
    (hG : QuasiCoherent.affineLocallyFiniteType X G)
    (hF : QuasiCoherent.affineLocallyFiniteType Y F)
    (e : (pullback f).obj G ≅ F) :
    ∃ n : ℕ, 0 < n ∧
      killedByIdealSheaf (I ^ n)
        (kernel ((pullbackPushforwardAdjunction f).homEquiv _ _ e.hom)) ∧
      killedByIdealSheaf (I ^ n)
        (cokernel ((pullbackPushforwardAdjunction f).homEquiv _ _ e.hom)) := by
  let := pullbackIso_adjoint_restrict_isIso f U e
  exact exists_pos_pow_killedByIdealSheaf_kernel_cokernel I U hU
    ((pullbackPushforwardAdjunction f).homEquiv _ _ e.hom)
    hG (properPushforward_coherent f F hF)

end AlgebraicGeometry.Scheme.Modules
