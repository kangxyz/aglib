/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Root.Affine
public import Aglib.AlgebraicGeometry.Modules.Invertible.Root.Errors
public import Aglib.AlgebraicGeometry.Modules.Invertible.Root.ScalarPullback
public import Aglib.AlgebraicGeometry.Modules.Invertible.Root.SquareZeroUnits

/-! # Prescribed affine root-pair isomorphisms across square-zero thickenings -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible.TrivializedPower

namespace AlgebraicGeometry.Scheme.Modules.Invertible.Root

universe u

/-- Lift the original prescribed affine root-pair isomorphism. The scalar
correction is principal for the actual original square-zero section map. -/
theorem exists_iso_lift_affine_of_square_zero
    {X₀ X : Scheme.{u}} [IsAffine X₀] [IsAffine X]
    (i : X₀ ⟶ X) [IsClosedImmersion i] (hi : i.ker ^ 2 = ⊥)
    (L : LineBundle X) (n : ℕ) (hn : IsUnit (n : Γ(X, ⊤)))
    (P Q : Pair L n) (a₀ : Iso (P.pullback i) (Q.pullback i)) :
    ∃ a : Iso P Q, (Scheme.Modules.pullback i).map a.bundleIso.hom = a₀.bundleIso.hom := by
  obtain ⟨a, ha⟩ := exists_lineBundle_iso_lift_affine_closed_of_square_zero i hi
    P.bundle Q.bundle a₀.bundleIso
  have haIso : (Scheme.Modules.pullback i).mapIso a = a₀.bundleIso :=
    CategoryTheory.Iso.ext ha
  let e : L.val ≅ L.val := powerError P Q a
  have he : (Scheme.Modules.pullback i).mapIso e = CategoryTheory.Iso.refl _ := by
    change (Scheme.Modules.pullback i).mapIso (powerError P Q a) = CategoryTheory.Iso.refl _
    rw [← powerError_pullback]
    apply (powerError_eq_refl_iff _ _ _).mpr
    rw [haIso]
    exact a₀.comm
  let t : Γ(X, ⊤)ˣ := autUnit X L e
  have ht : Units.map i.appTop.hom.toMonoidHom t = 1 :=
    map_autUnit_eq_one_of_pullback_eq_refl i L e he
  have htinv : i.appTop.hom (↑t⁻¹ : Γ(X, ⊤)) = 1 := by
    have h : Units.map i.appTop.hom.toMonoidHom (t⁻¹) = 1 := by
      rw [map_inv, ht, inv_one]
    exact congrArg Units.val h
  have hiΓ : RingHom.ker i.appTop.hom ^ 2 = ⊥ :=
    ker_app_sq_of_kernel_sq i hi ⟨⊤, isAffineOpen_top X⟩
  obtain ⟨v, hv, hvn⟩ := exists_principal_unit_root_of_square_zero
    i.appTop.hom hiΓ n hn (t⁻¹) htinv
  let a' := ScalarAutomorphisms.scalarIso X P.bundle.val v ≪≫ a
  have heScalar : e = ScalarAutomorphisms.scalarIso X L.val t := aut_eq_scalar X L e
  have herror : powerError P Q a' = CategoryTheory.Iso.refl _ := by
    calc
      powerError P Q a' = ScalarAutomorphisms.scalarIso X L.val (v ^ n) ≪≫ e :=
        powerError_scalar_precomp P Q a v
      _ = ScalarAutomorphisms.scalarIso X L.val (t⁻¹) ≪≫
          ScalarAutomorphisms.scalarIso X L.val t := by rw [hvn, heScalar]
      _ = CategoryTheory.Iso.refl _ := by
        rw [scalarIso_trans, inv_mul_cancel, scalarIso_one]
  refine ⟨{ bundleIso := a', comm := (powerError_eq_refl_iff P Q a').mp herror }, ?_⟩
  change (Scheme.Modules.pullback i).map
      ((ScalarAutomorphisms.scalarIso X P.bundle.val v).hom ≫ a.hom) = a₀.bundleIso.hom
  rw [Functor.map_comp]
  change (Scheme.Modules.pullback i).map (scalarMap X P.bundle.val (v : Γ(X, ⊤))) ≫
    (Scheme.Modules.pullback i).map a.hom = a₀.bundleIso.hom
  rw [pullback_scalarMap i P.bundle.val (v : Γ(X, ⊤))]
  change scalarMap X₀ ((Scheme.Modules.pullback i).obj P.bundle.val)
      (i.appTop.hom (v : Γ(X, ⊤))) ≫ (Scheme.Modules.pullback i).map a.hom = a₀.bundleIso.hom
  rw [hv, ScalarAutomorphisms.scalarMap_one, Category.id_comp, ha]

end AlgebraicGeometry.Scheme.Modules.Invertible.Root
