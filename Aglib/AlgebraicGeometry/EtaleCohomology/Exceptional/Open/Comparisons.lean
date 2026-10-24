/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.AbelianAdjunction
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackCoherence

/-!
# Original identity and composition comparisons for étale lower shriek

The comparisons are the unique left-adjoint comparisons induced by the original
inverse-image identity and composition isomorphisms. Their hom-equivalence
normalizations retain the specified adjunction maps, rather than choosing
unrelated isomorphisms between the same functors.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology

/-- Lower shriek of the identity, normalized by the original inverse-image identity. -/
def etaleLowerShriekIdIso (X : Scheme.{u}) :
    etaleLowerShriek (𝟙 X) ≅ 𝟭 (AbelianSheaf.{u, u + 1} X) :=
  ((etaleLowerShriekAdjunction (𝟙 X)).ofNatIsoRight (inverseImageId X)).leftAdjointUniq
    Adjunction.id

/-- The identity comparison has the original adjunction normalization. -/
@[reassoc]
theorem etaleLowerShriekIdIso_homEquiv (X : Scheme.{u})
    (F : AbelianSheaf.{u, u + 1} X) :
    (etaleLowerShriekAdjunction (𝟙 X)).homEquiv _ _
        ((etaleLowerShriekIdIso X).hom.app F) ≫ (inverseImageId X).hom.app F = 𝟙 F := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((etaleLowerShriekAdjunction (𝟙 X)).ofNatIsoRight (inverseImageId X))
    (Adjunction.id (C := AbelianSheaf.{u, u + 1} X)) F
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  simpa only [etaleLowerShriekIdIso, Functor.id_obj, Adjunction.id, NatTrans.id_app] using h


variable {V U X : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ U) [Etale j] [Etale k]

/-- Lower shriek composition is the mate of the original inverse-image composition. -/
def etaleLowerShriekCompIso :
    etaleLowerShriek (k ≫ j) ≅ etaleLowerShriek k ⋙ etaleLowerShriek j :=
  ((etaleLowerShriekAdjunction (k ≫ j)).ofNatIsoRight (inverseImageComp j k)).leftAdjointUniq
    ((etaleLowerShriekAdjunction k).comp (etaleLowerShriekAdjunction j))

/-- The composition comparison is normalized by the actual composite adjunction unit. -/
@[reassoc]
theorem etaleLowerShriekCompIso_homEquiv (F : AbelianSheaf.{u, u + 1} V) :
    (etaleLowerShriekAdjunction (k ≫ j)).homEquiv _ _
        ((etaleLowerShriekCompIso j k).hom.app F) ≫
          (inverseImageComp j k).hom.app
            ((etaleLowerShriek j).obj ((etaleLowerShriek k).obj F)) =
      ((etaleLowerShriekAdjunction k).comp (etaleLowerShriekAdjunction j)).unit.app F := by
  simpa only [Adjunction.homEquiv_ofNatIsoRight_apply, etaleLowerShriekCompIso,
    Functor.comp_obj] using
    Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((etaleLowerShriekAdjunction (k ≫ j)).ofNatIsoRight (inverseImageComp j k))
    ((etaleLowerShriekAdjunction k).comp (etaleLowerShriekAdjunction j)) F

/-- The normalized composition comparison retains both original lower-shriek units. -/
@[reassoc]
theorem etaleLowerShriekCompIso_unit (F : AbelianSheaf.{u, u + 1} V) :
    (etaleLowerShriekAdjunction (k ≫ j)).homEquiv _ _
        ((etaleLowerShriekCompIso j k).hom.app F) ≫
          (inverseImageComp j k).hom.app
            ((etaleLowerShriek j).obj ((etaleLowerShriek k).obj F)) =
      (etaleLowerShriekAdjunction k).unit.app F ≫
        (inverseImage k).map
          ((etaleLowerShriekAdjunction j).unit.app ((etaleLowerShriek k).obj F)) := by
  rw [etaleLowerShriekCompIso_homEquiv, Adjunction.comp_unit_app]

end AlgebraicGeometry.Scheme.EtaleCohomology
