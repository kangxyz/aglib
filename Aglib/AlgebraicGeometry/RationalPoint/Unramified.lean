/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalPoint.Cotangent
public import Aglib.RingTheory.Etale.LocalCotangent

/-!
# Unramifiedness from the original rational-point cotangent map

The actual pointed stalk map is essentially finite type, induces the identity
on the residue field for an endomorphism, and is formally unramified when its
cotangent pullback is surjective. These declarations retain their original
implementation from `Group.MultiplicationInvertible`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.OverField.Cotangent

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- The actual rational-point local map is essentially finite type when the
original scheme morphism is locally finite type. -/
theorem localMap_essFiniteType {X Y : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X)
    (y : 𝟙_ (FScheme k) ⟶ Y) (f : X ⟶ Y) (h : x ≫ f = y)
    [LocallyOfFiniteType f.left] : (localMap x y f h).EssFiniteType := by
  exact (RingHom.EssFiniteType.respectsIso.cancel_left_isIso
    (Y.left.presheaf.stalkCongr (.of_eq (point_eq x y f h).symm)).hom
    (f.left.stalkMap (pointData x).point)).mpr (LocallyOfFiniteType.stalkMap f.left _)

/-- A pointed endomorphism over the original field induces the actual identity
on the rational point's residue field. -/
theorem localMap_residue_id {X : FScheme k} (x : 𝟙_ (FScheme k) ⟶ X)
    (f : X ⟶ X) (h : x ≫ f = x) :
    IsLocalRing.ResidueField.map (localMap x x f h) = RingHom.id _ := by
  ext a
  obtain ⟨b, rfl⟩ := (pointData x).residueEquiv.symm.surjective a
  rw [(pointData x).residueEquiv_symm_apply, IsLocalRing.ResidueField.map_residue]
  have hc : localMap x x f h ((pointData x).constants b) = (pointData x).constants b :=
    DFunLike.congr_fun (localMap_constants x x f h) b
  exact congrArg (IsLocalRing.residue (pointData x).localRing) hc

/-- Surjectivity of the actual cotangent map makes a finite-type pointed
endomorphism unramified at its original rational-point stalk. -/
theorem localMap_formallyUnramified_of_surjective {X : FScheme k}
    (x : 𝟙_ (FScheme k) ⟶ X) (f : X ⟶ X) (h : x ≫ f = x)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType f.left]
    (hc : Function.Surjective (map x x f h)) : (localMap x x f h).FormallyUnramified := by
  let q := pointData x
  let R := q.localRing
  let := q.constants.toAlgebra
  let : LocallyOfFiniteType q.structureMap := ‹LocallyOfFiniteType X.hom›
  let : IsNoetherianRing R := q.localRing_isNoetherianRing
  let φ : R →ₐ[k] R :=
    { localMap x x f h with
      commutes' := fun a => DFunLike.congr_fun (localMap_constants x x f h) a }
  have hr : Function.Surjective (IsLocalRing.ResidueField.map φ.toRingHom) := by
    change Function.Surjective (IsLocalRing.ResidueField.map (localMap x x f h))
    rw [localMap_residue_id]
    exact Function.surjective_id
  exact φ.formallyUnramified_of_surjective_mapCotangent
    (localMap_essFiniteType x x f h) hr hc

end AlgebraicGeometry.Scheme.OverField.Cotangent
