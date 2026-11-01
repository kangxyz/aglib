/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.Representatives
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.SchemeTorsorEffacement
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TorsorGaloisComponent

/-! # Pointed Galois effacement of original finite constant H1 classes

An actual representative torsor is restricted to the connected component
through a specified geometric fibre point. Its original inclusion kills the
original H1 class, and its actual deck-group order divides the coefficient
cardinality, hence a power of any annihilator. No curve or invertibility
hypothesis, arbitrary Galois refinement, or new cohomology model is used.
The source Ext universe is independent; the produced target uses the native
standard Ext instance.
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite

universe u w

attribute [local instance] hasSheafifyLarge HasExt.standard Over.cartesianMonoidalCategory

variable (A : Type u) [AddCommGroup A] [Finite A]
  {X : Scheme.{u}} [ConnectedSpace X]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)

/-- A chosen geometric point lifts to an actual connected surjective Galois
cover killing the unchanged finite constant class; its deck order divides
the original coefficient cardinality. -/
theorem exists_pointed_galois_effacement (c : H1Etale X (coefficient A X)) :
    ∃ (Z : Scheme.FiniteEtale X) (_z : Scheme.FiniteEtale.Fiber s Z),
      PreGaloisCategory.IsGalois Z ∧ ConnectedSpace Z.obj.left ∧ Surjective Z.obj.hom ∧
      Nat.card (Aut Z) ∣ Nat.card A ∧
      h1Pullback.{u, w, u + 2} Z.obj.hom (coefficient A X) c = 0 := by
  obtain ⟨Y, τ, hY, hc⟩ := exists_schemeTorsorRepresentative A X c
  let : Surjective Y.obj.hom := hY
  let G := (representation A X).group
  let : IsCommMonObj G.X := (representation A X).commutative
  let : Etale G.X.hom := (representation A X).etale
  let : Nonempty Y.obj.left :=
    Nonempty.map (fun x : X => (hY.surj x).choose) inferInstance
  let : Nonempty (Scheme.FiniteEtale.Fiber s Y) :=
    Scheme.FiniteEtale.nonempty_fiber_of_nonempty_cover s Y
  let y : Scheme.FiniteEtale.Fiber s Y := Classical.choice inferInstance
  let e : G.X ≅ (Scheme.FiniteEtale.trivialCover X A).obj := Iso.refl _
  obtain ⟨Z, i, z, _hz, _hi, hZ, hconn, hsurj, _δ, _hδ, _hover, hcard⟩ :=
    Scheme.FiniteEtale.TorsorGaloisComponent.exists_galois_component s G e Y τ y
  let t : Over.mk Z.obj.hom ⟶ Y.obj := Over.homMk i.hom.left (Over.w i.hom)
  have hzero := SchemeTorsorEffacement.h1Pullback_torsorExtClass_eq_zero.{u, w, u + 2}
    Z.obj.hom Y t G τ
  refine ⟨Z, z, hZ, hconn, hsurj, hcard, ?_⟩
  calc
    h1Pullback Z.obj.hom (coefficient A X) c =
        h1Pullback Z.obj.hom (coefficient A X)
          (coefficientMap (representation A X).iso.hom
            (torsorExtClass (torsorOfSchemeAction G Y τ))) :=
      congrArg (h1Pullback Z.obj.hom (coefficient A X)) hc.symm
    _ = coefficientMap ((inverseImage Z.obj.hom).map (representation A X).iso.hom)
        (h1Pullback Z.obj.hom (representedSheaf G)
          (torsorExtClass (torsorOfSchemeAction G Y τ))) :=
      h1Pullback_coefficientMap Z.obj.hom (representation A X).iso.hom _
    _ = 0 := by rw [hzero, map_zero]

/-- The same actual pointed cover has deck order dividing a power of the
original annihilator. Positivity and invertibility are unnecessary here. -/
theorem exists_pointed_galois_effacement_order (n : ℕ) (hn : ∀ a : A, n • a = 0)
    (c : H1Etale X (coefficient A X)) :
    ∃ (Z : Scheme.FiniteEtale X) (_z : Scheme.FiniteEtale.Fiber s Z),
      PreGaloisCategory.IsGalois Z ∧ ConnectedSpace Z.obj.left ∧ Surjective Z.obj.hom ∧
      Nat.card (Aut Z) ∣ n ^ Group.rank (Multiplicative A) ∧
      h1Pullback.{u, w, u + 2} Z.obj.hom (coefficient A X) c = 0 := by
  obtain ⟨Z, z, hZ, hconn, hsurj, hcard, hzero⟩ := exists_pointed_galois_effacement A s c
  refine ⟨Z, z, hZ, hconn, hsurj, hcard.trans ?_, hzero⟩
  exact card_dvd_exponent_pow_rank' (Multiplicative A)
    (fun a => congrArg Multiplicative.ofAdd (hn a.toAdd))

end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite
