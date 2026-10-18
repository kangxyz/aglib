/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.RightAdjoint.Restriction

/-!
# The original closed-adjoint open comparison and its ordinary counit

The comparison constructed using extension by zero is also the right mate
of the original open base-change isomorphism. This retains the geometric
counit before passing to affine sections or derived resolutions.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {W U V X : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j]
  [IsClosedImmersion f] [IsClosedImmersion b] (h : IsPullback a b f j)

/-- The actual ordinary open comparison is compatible with the original
closed-adjunction counit and the inverse original open base-change map. -/
theorem closedImmersionRightAdjointOpenIso_pushforward_counit (N : X.Modules) :
    (pushforward b).map
        ((closedImmersionRightAdjointOpenIso a b f j h).hom.app N) ≫
      (closedImmersionRightAdjunction b).counit.app ((restrictFunctor j).obj N) =
    (cartesianOpenBaseChange a b f j h).inv.app
        ((closedImmersionRightAdjoint f).obj N) ≫
      (restrictFunctor j).map ((closedImmersionRightAdjunction f).counit.app N) := by
  let A := extensionByZeroRestrictAdjunction a
  let J := extensionByZeroRestrictAdjunction j
  let K := (closedImmersionRightAdjoint f).obj N
  let Z := (restrictFunctor a).obj K
  let d := cartesianOpenBaseChange a b f j h
  let q := (closedPushforwardExtensionByZeroIso a b f j h).hom.app Z
  have hq : (J.homEquiv ((pushforward b).obj Z) ((pushforward f).obj
      ((extensionByZero a).obj Z))) q =
      (pushforward b).map (A.unit.app Z) ≫ d.inv.app ((extensionByZero a).obj Z) := by
    rw [Adjunction.homEquiv_unit]
    simpa only [J, A, q, d, closedPushforwardExtensionByZeroIso_hom] using
      closedPushforwardExtensionByZeroMap_unit a b f j h Z
  have hd : d.inv.app ((extensionByZero a).obj Z) ≫
      (restrictFunctor j).map ((pushforward f).map (A.counit.app K)) =
      (pushforward b).map ((restrictFunctor a).map (A.counit.app K)) ≫ d.inv.app K :=
    (d.inv.naturality (A.counit.app K)).symm
  have ha : q ≫ (pushforward f).map (A.counit.app K) =
      (J.homEquiv ((pushforward b).obj Z) ((pushforward f).obj K)).symm (d.inv.app K) := by
    apply (J.homEquiv ((pushforward b).obj Z) ((pushforward f).obj K)).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right]
    change (J.homEquiv ((pushforward b).obj Z)
      ((pushforward f).obj ((extensionByZero a).obj Z))) q ≫
        (restrictFunctor j).map ((pushforward f).map (A.counit.app K)) = d.inv.app K
    rw [hq]
    calc
      ((pushforward b).map (A.unit.app Z) ≫ d.inv.app ((extensionByZero a).obj Z)) ≫
          (restrictFunctor j).map ((pushforward f).map (A.counit.app K)) =
        (pushforward b).map (A.unit.app Z) ≫
          (pushforward b).map ((restrictFunctor a).map (A.counit.app K)) ≫ d.inv.app K := by
        rw [Category.assoc, hd]
      _ = d.inv.app K := by
        rw [← (pushforward b).map_comp_assoc, A.right_triangle_components]
        exact (congrArg (fun z => z ≫ d.inv.app K)
          ((pushforward b).map_id ((restrictFunctor a).obj K))).trans (Category.id_comp _)
  apply (J.homEquiv ((pushforward b).obj Z) N).symm.injective
  calc
    (J.homEquiv ((pushforward b).obj Z) N).symm
        ((pushforward b).map
            ((closedImmersionRightAdjointOpenIso a b f j h).hom.app N) ≫
          (closedImmersionRightAdjunction b).counit.app ((restrictFunctor j).obj N)) =
      q ≫ (pushforward f).map (A.counit.app K) ≫
        (closedImmersionRightAdjunction f).counit.app N := by
      simpa only [Adjunction.homEquiv_counit, CategoryTheory.Functor.map_comp,
        CategoryTheory.Functor.comp_map, Adjunction.comp_counit_app, Category.assoc,
        q, A, J, K, Z] using closedImmersionRightAdjointOpenIso_counit a b f j h N
    _ = (J.homEquiv ((pushforward b).obj Z) ((pushforward f).obj K)).symm
        (d.inv.app K) ≫ (closedImmersionRightAdjunction f).counit.app N := by
      rw [← Category.assoc, ha]
    _ = (J.homEquiv ((pushforward b).obj Z) N).symm
        (d.inv.app K ≫
          (restrictFunctor j).map ((closedImmersionRightAdjunction f).counit.app N)) :=
      (J.homEquiv_naturality_right_symm (d.inv.app K)
        ((closedImmersionRightAdjunction f).counit.app N)).symm

/-- Applying the original restriction unit before the original open comparison
recovers the original closed counit after the base restriction unit. -/
theorem closedImmersionRightAdjointOpenIso_unit_counit (N : X.Modules) :
    (pushforward f).map
        ((restrictAdjunction a).unit.app ((closedImmersionRightAdjoint f).obj N)) ≫
      (cartesianPushforwardSquare a b f j h).hom.app
        ((restrictFunctor a).obj ((closedImmersionRightAdjoint f).obj N)) ≫
      (pushforward j).map
        ((pushforward b).map
            ((closedImmersionRightAdjointOpenIso a b f j h).hom.app N) ≫
          (closedImmersionRightAdjunction b).counit.app ((restrictFunctor j).obj N)) =
    (closedImmersionRightAdjunction f).counit.app N ≫
      (restrictAdjunction j).unit.app N := by
  rw [← Category.assoc, cartesianOpenBaseChange_unit, Category.assoc,
    closedImmersionRightAdjointOpenIso_pushforward_counit,
    CategoryTheory.Functor.map_comp, ← (pushforward j).map_comp_assoc,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact ((restrictAdjunction j).unit.naturality
    ((closedImmersionRightAdjunction f).counit.app N)).symm

end AlgebraicGeometry.Scheme.Modules
