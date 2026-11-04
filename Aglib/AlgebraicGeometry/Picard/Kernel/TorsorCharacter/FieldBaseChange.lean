/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.FamilyBaseChange.Lift
public import Aglib.AlgebraicGeometry.Picard.Kernel.Characters

/-! Original family transition units under field extension. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open Scheme.OverField Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {A B : Grp (FScheme k)} (q : A ⟶ B) (T : FScheme K)
  (M : LineBundle (pullback B.X.hom ((Over.map (Spec.algebraMap k K)).obj T).hom))
  (a : (Scheme.Modules.pullback
    (familyMapOfHom q.hom.hom ((Over.map (Spec.algebraMap k K)).obj T))).obj M.val ≅
      SheafOfModules.unit
        (pullback A.X.hom ((Over.map (Spec.algebraMap k K)).obj T).hom).ringCatSheaf)

local notation "b" => Spec.algebraMap k K
local notation "F" => Over.pullback b
local notation "T₀" => Functor.obj (Over.map b) T
local notation "q₀" => familyMapOfHom q.hom.hom T₀
local notation "qK" => CategoryTheory.Functor.map (Functor.mapGrp F) q
local notation "qOver" => Mon.Hom.hom (InducedCategory.Hom.hom qK)
local notation "q₁" => familyMapOfHom qOver T

/-- The frame on the scalar-extended source obtained from the original
frame through the canonical Cartesian family square. -/
def fieldBaseChangeFamilyFrame :
    (Scheme.Modules.pullback q₁).obj
      (pullbackLineBundle (familyBaseChangeIso B.X.hom b T).hom M).val ≅
      SheafOfModules.unit (pullback (((F).mapGrp.obj A).X).hom T.hom).ringCatSheaf :=
  PowerBaseChange.pullbackFrame (familyBaseChangeIso B.X.hom b T).hom M q₀ q₁
    (familyBaseChangeIso A.X.hom b T).hom
    (familyMapOfHom_baseChange q.hom.hom b T).symm a

/-- The original transition of the original transported frame has exactly
the original value on the two adjoint source points. -/
theorem familyTransitionUnit_fieldBaseChange {U : FScheme K}
    (x y : U ⟶ ((F).mapGrp.obj A).X) (t : U ⟶ T)
    (h : x ≫ qOver = y ≫ qOver) :
    let ad := Over.mapPullbackAdj b
    let x₀ := (ad.homEquiv U A.X).symm x
    let y₀ := (ad.homEquiv U A.X).symm y
    let t₀ := (Over.map b).map t
    let h₀ : x₀ ≫ q.hom.hom = y₀ ≫ q.hom.hom := by
      have hx : (ad.homEquiv U B.X).symm (x ≫ qOver) = x₀ ≫ q.hom.hom :=
        ad.homEquiv_naturality_right_symm x q.hom.hom
      have hy : (ad.homEquiv U B.X).symm (y ≫ qOver) = y₀ ≫ q.hom.hom :=
        ad.homEquiv_naturality_right_symm y q.hom.hom
      exact hx.symm.trans ((congrArg (ad.homEquiv U B.X).symm h).trans hy)
    familyTransitionUnit qK T
        (pullbackLineBundle (familyBaseChangeIso B.X.hom b T).hom M)
        (fieldBaseChangeFamilyFrame q T M a) x y t h =
      familyTransitionUnit q T₀ M a x₀ y₀ t₀ h₀ := by
  intro ad x₀ y₀ t₀ h₀
  let eA := (familyBaseChangeIso A.X.hom b T).hom
  let eB := (familyBaseChangeIso B.X.hom b T).hom
  let hQ : eA ≫ q₀ = q₁ ≫ eB := (familyMapOfHom_baseChange q.hom.hom b T).symm
  let s := (lift (x ≫ qOver) t).left
  let v := (lift x t).left
  let w := (lift y t).left
  let hv : v ≫ q₁ = s := lift_comp_familyMap qK T x t
  let hw : w ≫ q₁ = s := (lift_comp_familyMap qK T y t).trans
    (congrArg (fun z => (lift z t).left) h.symm)
  have hs : s ≫ eB = (lift (x₀ ≫ q.hom.hom) t₀).left := by
    have hx : (ad.homEquiv U B.X).symm (x ≫ qOver) = x₀ ≫ q.hom.hom :=
      ad.homEquiv_naturality_right_symm x q.hom.hom
    exact (lift_left_comp_familyBaseChangeIso b B.X (x ≫ qOver) t).trans
      (congrArg (fun z : (Over.map b).obj U ⟶ B.X => (lift z t₀).left) hx)
  have h₁ : v ≫ eA = (lift x₀ t₀).left := lift_left_comp_familyBaseChangeIso b A.X x t
  have h₂ : w ≫ eA = (lift y₀ t₀).left := lift_left_comp_familyBaseChangeIso b A.X y t
  have H := Scheme.Modules.TrivializedDescent.unit_pullbackFrame q₀ M a eB q₁ eA hQ s v w hv hw
  exact H.trans (Scheme.Modules.TrivializedDescent.unit_congr q₀ M a _ _ _ _ hs h₁ h₂)

end AlgebraicGeometry.Scheme.RelativePicard
