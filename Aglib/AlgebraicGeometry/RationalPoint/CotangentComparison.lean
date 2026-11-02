/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalPoint.Cotangent
public import Aglib.AlgebraicGeometry.Stalk.Scalar

/-!
# Cotangent comparison through an open immersion

The comparison is induced by the original pointed stalk pullback. Its scalar
action agrees with the structural stalk constants, so no new cotangent model
or scalar action is selected at a geometric specialization.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.RationalPoint

-- The field-spectrum stalk and its underlying prime-spectrum point are definitionally equal.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Rational-point constants are the original structural stalk scalar map. -/
theorem constantsAt_eq_stalkScalar {k : Type u} [Field k] {X : Scheme.{u}}
    (q : RationalPoint k X) (x : X) :
    q.constantsAt x = q.structureMap.stalkScalar x := by
  have hs (s : Spec (.of k)) :
      (fieldStalkIso k s).inv = (Scheme.ΓSpecIso (.of k)).inv ≫
        (Spec (.of k)).presheaf.germ ⊤ s trivial := by
    obtain rfl : s = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    dsimp [fieldStalkIso, TopCat.Presheaf.stalkCongr]
    rw [TopCat.Presheaf.stalkSpecializes_refl, Category.comp_id,
      ← ΓSpecIso_hom_stalkClosedPointIso_inv]
    simp
  rw [constantsAt, Hom.stalkScalar_eq_local, hs]
  rfl

end AlgebraicGeometry.Scheme.RationalPoint

namespace AlgebraicGeometry.Scheme.OverField.Cotangent

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k] {X Y : FScheme k}

/-- The original pointed stalk map of an open immersion is bijective. -/
theorem localMap_bijective_of_isOpenImmersion
    (x : 𝟙_ (FScheme k) ⟶ X) (y : 𝟙_ (FScheme k) ⟶ Y)
    (f : X ⟶ Y) (h : x ≫ f = y) [IsOpenImmersion f.left] :
    Function.Bijective (localMap x y f h) := by
  let : IsIso (Scheme.stalkMapAt f.left (pointData x).point (pointData y).point
      (point_eq x y f h)) := by
    let e := Y.left.presheaf.stalkCongr (.of_eq (point_eq x y f h).symm)
    let : IsIso e.hom := e.isIso_hom
    change IsIso (e.hom ≫ f.left.stalkMap (pointData x).point)
    infer_instance
  exact (asIso (Scheme.stalkMapAt f.left (pointData x).point (pointData y).point
    (point_eq x y f h))).commRingCatIsoToRingEquiv.bijective

/-- The cotangent pullback of an open immersion is a linear equivalence on the
actual maximal-ideal quotients at the two rational points. -/
def equivOfIsOpenImmersion
    (x : 𝟙_ (FScheme k) ⟶ X) (y : 𝟙_ (FScheme k) ⟶ Y)
    (f : X ⟶ Y) (h : x ≫ f = y) [IsOpenImmersion f.left] :
    Space y ≃ₗ[k] Space x := by
  let := (pointData x).constants.toAlgebra
  let := (pointData y).constants.toAlgebra
  let φ : (pointData y).localRing →ₐ[k] (pointData x).localRing :=
    { localMap x y f h with
      commutes' := fun a => DFunLike.congr_fun (localMap_constants x y f h) a }
  let e : (pointData y).localRing ≃ₐ[k] (pointData x).localRing :=
    AlgEquiv.ofBijective φ (localMap_bijective_of_isOpenImmersion x y f h)
  let : IsLocalHom e.symm.toRingHom := IsLocalHom.of_surjective _ e.symm.surjective
  let ψ := Ideal.mapCotangent (IsLocalRing.maximalIdeal (pointData x).localRing)
    (IsLocalRing.maximalIdeal (pointData y).localRing) e.symm.toAlgHom
    (fun a ha => _root_.map_nonunit e.symm.toRingHom a ha)
  refine LinearEquiv.ofLinearMap (map x y f h) ψ ?_ ?_
  · ext a
    obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective (IsLocalRing.maximalIdeal _) a
    change (IsLocalRing.maximalIdeal _).toCotangent
      ⟨e (e.symm a), _⟩ = (IsLocalRing.maximalIdeal _).toCotangent a
    congr 1
    exact Subtype.ext (e.apply_symm_apply a)
  · ext a
    obtain ⟨a, rfl⟩ := Ideal.toCotangent_surjective (IsLocalRing.maximalIdeal _) a
    change (IsLocalRing.maximalIdeal _).toCotangent
      ⟨e.symm (e a), _⟩ = (IsLocalRing.maximalIdeal _).toCotangent a
    congr 1
    exact Subtype.ext (e.symm_apply_apply a)

/-- The equivalence retains the original cotangent map. -/
@[simp] theorem equivOfIsOpenImmersion_toLinearMap
    (x : 𝟙_ (FScheme k) ⟶ X) (y : 𝟙_ (FScheme k) ⟶ Y)
    (f : X ⟶ Y) (h : x ≫ f = y) [IsOpenImmersion f.left] :
    (equivOfIsOpenImmersion x y f h).toLinearMap = map x y f h := rfl

end AlgebraicGeometry.Scheme.OverField.Cotangent
