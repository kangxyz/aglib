/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalPoint.Unramified
public import Aglib.AlgebraicGeometry.Morphisms.Etale.Locus
public import Aglib.RingTheory.Etale.SmoothDifferential

/-!
# The smooth differential criterion at an actual rational point

Formal unramifiedness between smooth schemes of the same relative dimension
gives formal etaleness of the original stalk map. For a pointed endomorphism,
a surjective original cotangent map supplies formal unramifiedness. Local
finite presentation then gives an actual etale neighborhood.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.OverField.Cotangent

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- Formal unramifiedness of the actual pointed stalk map implies formal
etaleness between smooth schemes of the same relative dimension. -/
theorem localMap_formallyEtale_of_formallyUnramified
    {X Y : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X) (y : 𝟙_ (FScheme k) ⟶ Y)
    (f : X ⟶ Y) (h : x ≫ f = y) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension d Y.hom]
    (hu : (localMap x y f h).FormallyUnramified) :
    (localMap x y f h).FormallyEtale := by
  let qx := pointData x
  let qy := pointData y
  let A := qy.localRing
  let B := qx.localRing
  let := qy.constants.toAlgebra
  let := qx.constants.toAlgebra
  let : SmoothOfRelativeDimension d qx.structureMap := ‹SmoothOfRelativeDimension d X.hom›
  let : SmoothOfRelativeDimension d qy.structureMap := ‹SmoothOfRelativeDimension d Y.hom›
  let : Smooth qx.structureMap := SmoothOfRelativeDimension.smooth d qx.structureMap
  let : Smooth qy.structureMap := SmoothOfRelativeDimension.smooth d qy.structureMap
  let : Algebra.EssFiniteType k A := qy.constants_essFiniteType
  let : Algebra.EssFiniteType k B := qx.constants_essFiniteType
  let : Algebra.FormallySmooth k B := qx.constants_formallySmooth
  obtain ⟨hA, hrA⟩ := qy.localRing_kaehlerDifferential_free_and_rank d
  obtain ⟨hB, hrB⟩ := qx.localRing_kaehlerDifferential_free_and_rank d
  let : Module.Free A Ω[A⁄k] := hA
  let : Module.Free B Ω[B⁄k] := hB
  let : Algebra A B := (localMap x y f h).toAlgebra
  let : IsScalarTower k A B :=
    IsScalarTower.of_algebraMap_eq' (localMap_constants x y f h).symm
  let : Algebra.FormallyUnramified A B := hu
  apply Algebra.formallyEtale_of_formallyUnramified_of_finrank_eq k A B
  exact congrArg Cardinal.toNat (hrA.trans hrB.symm)

/-- A surjective original cotangent pullback makes a pointed endomorphism
of a smooth scheme formally etale at its actual rational point. -/
theorem localMap_formallyEtale_of_surjective {X : FScheme k}
    (x : 𝟙_ (FScheme k) ⟶ X) (f : X ⟶ X) (h : x ≫ f = x) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (hc : Function.Surjective (map x x f h)) : (localMap x x f h).FormallyEtale := by
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth d X.hom
  have : LocallyOfFiniteType (f.left ≫ X.hom) := by rw [f.w]; infer_instance
  let : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left X.hom
  exact localMap_formallyEtale_of_formallyUnramified x x f h d
    (localMap_formallyUnramified_of_surjective x f h hc)

/-- The actual smooth pointed endomorphism is etale on a neighborhood of the
rational point whenever its original cotangent pullback is surjective. -/
theorem exists_etale_neighborhood_of_surjective {X : FScheme k}
    (x : 𝟙_ (FScheme k) ⟶ X) (f : X ⟶ X) (h : x ≫ f = x) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    (hc : Function.Surjective (map x x f h)) :
    ∃ U : X.left.Opens, (pointData x).point ∈ U ∧ Etale (U.ι ≫ f.left) := by
  let : Smooth X.hom := SmoothOfRelativeDimension.smooth d X.hom
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : LocallyOfFiniteType (f.left ≫ X.hom) := by rw [f.w]; infer_instance
  let : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left X.hom
  have he := localMap_formallyEtale_of_surjective x f h d hc
  have hs : (f.left.stalkMap (pointData x).point).hom.FormallyEtale := by
    exact (RingHom.FormallyEtale.respectsIso.cancel_left_isIso
      (X.left.presheaf.stalkCongr (.of_eq (point_eq x x f h).symm)).hom
      (f.left.stalkMap (pointData x).point)).mp he
  exact LocalRing.Etale.exists_etale_neighborhood_of_stalkMap_formallyEtale
    f.left (pointData x).point hs

end AlgebraicGeometry.Scheme.OverField.Cotangent
