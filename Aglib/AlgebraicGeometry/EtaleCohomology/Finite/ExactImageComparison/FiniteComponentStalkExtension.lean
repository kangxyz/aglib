/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.PointStalkExtension
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.FiniteComponentPointScheme
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.TupleStageLift

/-! # Extending the original finite-component stalks to the common geometric field -/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

variable (B A Ω : Type u) [CommRing B] [HenselianLocalRing B]
  [IsSepClosed (ResidueField B)] [CommRing A] [Algebra B A] [Module.Finite B A]
  [Field Ω] [IsAlgClosed Ω] [Algebra (ResidueField B) Ω]
  {X : Scheme.{u}} (q : Spec (.of A) ⟶ X) (m : MaximalSpectrum A)

local instance : Module.Finite B (Localization.AtPrime m.asIdeal) :=
  HenselianLocalRing.finite_localizationAtPrime B A m.asIdeal

local instance : IsLocalHom (algebraMap B (Localization.AtPrime m.asIdeal)) := by
  apply ((local_hom_TFAE (algebraMap B (Localization.AtPrime m.asIdeal))).out 5 1).mp
  exact eq_maximalIdeal
    (Ideal.isMaximal_under_of_isIntegral_of_isMaximal
      (maximalIdeal (Localization.AtPrime m.asIdeal)))

/-- The literal field extension of the original component residue point. -/
def extendedFiniteComponentPoint : Spec (.of Ω) ⟶ X :=
  Spec.map (CommRingCat.ofHom
    (finiteLocalResidueEmbedding B (Localization.AtPrime m.asIdeal) Ω).toRingHom) ≫
    (Finite.finiteSourceResiduePoint A m ≫ q)

/-- This original extended point is precisely the point selected by the common
geometric-field component bijection. -/
theorem extendedFiniteComponentPoint_eq :
    extendedFiniteComponentPoint B A Ω q m =
      Spec.map (CommRingCat.ofHom (finiteComponentPoint B A Ω m)) ≫ q := by
  rw [finiteComponentPoint_spec_eq]
  simp only [extendedFiniteComponentPoint, Finite.finiteSourceResiduePoint,
    Finite.localComponentResidueMap, Category.assoc]

/-- The actual component stalk is unchanged on extending its separably closed
residue field to the chosen common algebraically closed field. -/
def finiteSourceComponentStalkExtension :
    (Finite.finiteSourceComponentPoint A B q m).presheafFiber
        (A := AddCommGrpCat.{u + 1}) ≅
      (pointSmallEtale (extendedFiniteComponentPoint B A Ω q m)).presheafFiber := by
  let : IsSepClosed (ResidueField (Localization.AtPrime m.asIdeal)) :=
    HenselianLocalRing.residueField_isSepClosed_localizationAtPrime B A m.asIdeal
  exact pointExtensionPresheafFiberIso (Finite.finiteSourceResiduePoint A m ≫ q)
    (Spec.map (CommRingCat.ofHom
      (finiteLocalResidueEmbedding B (Localization.AtPrime m.asIdeal) Ω).toRingHom))

/-- Every original germ is transported to the literal extended-point germ. -/
theorem finiteSourceComponentStalkExtension_germ
    (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (U : X.Etale)
    (p : (Finite.finiteSourceComponentPoint A B q m).fiber.obj U) :
    let : IsSepClosed (ResidueField (Localization.AtPrime m.asIdeal)) :=
      HenselianLocalRing.residueField_isSepClosed_localizationAtPrime B A m.asIdeal
    (Finite.finiteSourceComponentPoint A B q m).toPresheafFiber U p P ≫
        (finiteSourceComponentStalkExtension B A Ω q m).hom.app P =
      (pointSmallEtale (extendedFiniteComponentPoint B A Ω q m)).toPresheafFiber U
        (pointFiberExtension (Finite.finiteSourceResiduePoint A m ≫ q)
          (Spec.map (CommRingCat.ofHom
            (finiteLocalResidueEmbedding B (Localization.AtPrime m.asIdeal) Ω).toRingHom))
          U p) P := by
  let : IsSepClosed (ResidueField (Localization.AtPrime m.asIdeal)) :=
    HenselianLocalRing.residueField_isSepClosed_localizationAtPrime B A m.asIdeal
  exact pointExtensionPresheafFiberIso_germ _ _ P U p

end AlgebraicGeometry.Scheme.EtaleCohomology
