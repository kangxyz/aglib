/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.ConstantOpenFieldExtension
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.PointedEffacement
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisBaseChange

/-! # Pointed finite constant H1 effacement after curve field extension

The original target class descends through the proved constant comparison. An
actual pointed Galois component killing that source class is then pulled back
by the literal finite-etale base-change functor. The lifted point and the
class-killing equation retain the original projections and constant transports.
This is an algebraically closed H1 statement, not relative tame extension or
all-degree strict-local effacement.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves.PointedGaloisEffacement

attribute [local instance] hasSheafifyLarge HasExt.standard

/-- A prescribed rational point lifts to the literal base change of an actual
source Galois cover of annihilator-power order killing the original target
class. The displayed point equation retains the original source lift. -/
theorem exists_pointed_source_galois_effacement
    (k K : Type u) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] [Algebra k K]
    (X : FScheme k) (hX : Curve.Properties X)
    {U : Scheme.{u}} [Nonempty U] (j : U ⟶ X.left) [IsOpenImmersion j]
    (x : Spec (.of k) ⟶ U) (hx : x ≫ (j ≫ X.hom) = 𝟙 _)
    (A : Type u) [AddCommGroup A] [Finite A]
    (n : ℕ) (hpos : 0 < n) (hn : ∀ a : A, n • a = 0)
    (hk : IsUnit (n : Γ(Spec (.of k), ⊤)))
    (c : H1Etale (pullback (j ≫ X.hom) (Spec.algebraMap k K))
      (ConstantFinite.coefficient A _)) :
    letI : IsIntegral X.left := Curve.curveProperties_isIntegral
      Scheme.smoothFieldNormality Scheme.normalComponentsOpen hX
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    let q := Spec.algebraMap k K
    let g := pullback.fst (j ≫ X.hom) q
    let xK := pullback.lift (q ≫ x) (𝟙 _)
      (by rw [Category.assoc, hx, Category.comp_id, Category.id_comp])
    ∃ (Z : Scheme.FiniteEtale U) (z : Scheme.FiniteEtale.Fiber x Z)
      (zK : Scheme.FiniteEtale.Fiber xK ((Scheme.FiniteEtale.baseChange g).obj Z)),
      PreGaloisCategory.IsGalois Z ∧ ConnectedSpace Z.obj.left ∧ Surjective Z.obj.hom ∧
      Nat.card (Aut Z) ∣ n ^ Group.rank (Multiplicative A) ∧
      zK.left ≫ pullback.fst Z.obj.hom g = q ≫ z.left ∧
      h1Pullback.{u, u + 2, u + 2} ((Scheme.FiniteEtale.baseChange g).obj Z).obj.hom
        (ConstantFinite.coefficient A _) c = 0 := by
  let : IsIntegral X.left := Curve.curveProperties_isIntegral
    Scheme.smoothFieldNormality Scheme.normalComponentsOpen hX
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let q := Spec.algebraMap k K
  let g := pullback.fst (j ≫ X.hom) q
  let xK := pullback.lift (q ≫ x) (𝟙 _)
    (by rw [Category.assoc, hx, Category.comp_id, Category.id_comp])
  obtain ⟨c₀, hc₀⟩ := (ConstantOpenFieldExtension.constantRestriction_bijective
    k K X hX j A n hpos hn hk).surjective c
  obtain ⟨Z, z, hZ, hconn, hsurj, hcard, hzero⟩ :=
    ConstantFinite.exists_pointed_galois_effacement_order A x n hn c₀
  let b : Scheme.FiniteEtale.Fiber (xK ≫ g) Z := Over.homMk (q ≫ z.left) (by
    rw [Category.assoc, Over.w z]
    exact (pullback.lift_fst _ _ _).symm)
  let zK := Scheme.FiniteEtale.fiberBaseChangeEquiv g xK Z b
  refine ⟨Z, z, zK, hZ, hconn, hsurj, hcard, ?_, ?_⟩
  · exact (congrArg (fun t => t ≫ pullback.fst Z.obj.hom g)
      (Scheme.FiniteEtale.fiberBaseChangeEquiv_left g xK Z b)).trans
        (pullback.lift_fst b.left xK (Over.w b))
  · let ZK := (Scheme.FiniteEtale.baseChange g).obj Z
    let a : ZK.obj.left ⟶ Z.obj.left := pullback.fst Z.obj.hom g
    have hs : constantRestriction.{u, u + 2, u + 2} A Z.obj.hom 1 c₀ = 0 := by
      rw [constantRestriction_apply, cohomologyPullback_one]
      change Sheaf.H.map _ 1 (h1Pullback Z.obj.hom (ConstantFinite.coefficient A U) c₀) = 0
      rw [hzero, map_zero]
    have hsq : ZK.obj.hom ≫ g = a ≫ Z.obj.hom := pullback.condition.symm
    have hz : constantRestriction.{u, u + 2, u + 2} A ZK.obj.hom 1 c = 0 := by
      calc
        constantRestriction.{u, u + 2, u + 2} A ZK.obj.hom 1 c =
            constantRestriction.{u, u + 2, u + 2} A ZK.obj.hom 1
              (constantRestriction.{u, u + 2, u + 2} A g 1 c₀) :=
          congrArg (constantRestriction.{u, u + 2, u + 2} A ZK.obj.hom 1) hc₀.symm
        _ = constantRestriction.{u, u + 2, u + 2} A (ZK.obj.hom ≫ g) 1 c₀ :=
          (constantRestriction_comp.{u, u + 2, u + 2, u + 2} A g ZK.obj.hom 1 c₀).symm
        _ = constantRestriction.{u, u + 2, u + 2} A (a ≫ Z.obj.hom) 1 c₀ :=
          congrArg (fun f => constantRestriction.{u, u + 2, u + 2} A f 1 c₀) hsq
        _ = constantRestriction.{u, u + 2, u + 2} A a 1
            (constantRestriction.{u, u + 2, u + 2} A Z.obj.hom 1 c₀) :=
          constantRestriction_comp.{u, u + 2, u + 2, u + 2} A Z.obj.hom a 1 c₀
        _ = 0 := by rw [hs, map_zero]
    apply (cohomologyMapIso_bijective
      ((inverseImageConstantIso ZK.obj.hom).app (ConstantFinite.value A)) 1).injective
    rw [map_zero]
    rw [constantRestriction_apply, cohomologyPullback_one] at hz
    exact hz

/-- The actual pulled-back pointed cover is itself Galois, with the same deck
order and hence the same annihilator-power bound. It kills the original target
class along its literal structural map, not along a replacement cover. -/
theorem exists_pointed_galois_effacement
    (k K : Type u) [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K] [Algebra k K]
    (X : FScheme k) (hX : Curve.Properties X)
    {U : Scheme.{u}} [Nonempty U] (j : U ⟶ X.left) [IsOpenImmersion j]
    (x : Spec (.of k) ⟶ U) (hx : x ≫ (j ≫ X.hom) = 𝟙 _)
    (A : Type u) [AddCommGroup A] [Finite A]
    (n : ℕ) (hpos : 0 < n) (hn : ∀ a : A, n • a = 0)
    (hk : IsUnit (n : Γ(Spec (.of k), ⊤)))
    (c : H1Etale (pullback (j ≫ X.hom) (Spec.algebraMap k K))
      (ConstantFinite.coefficient A _)) :
    letI : IsIntegral X.left := Curve.curveProperties_isIntegral
      Scheme.smoothFieldNormality Scheme.normalComponentsOpen hX
    letI : IsIntegral U := isIntegral_of_isOpenImmersion j
    let q := Spec.algebraMap k K
    letI : GeometricallyConnected q := Scheme.Geometrically.fieldSpec_geometricallyConnected k K
    let g := pullback.fst (j ≫ X.hom) q
    let xK := pullback.lift (q ≫ x) (𝟙 _)
      (by rw [Category.assoc, hx, Category.comp_id, Category.id_comp])
    ∃ (Z : Scheme.FiniteEtale U) (z : Scheme.FiniteEtale.Fiber x Z)
      (zK : Scheme.FiniteEtale.Fiber xK ((Scheme.FiniteEtale.baseChange g).obj Z)),
      let ZK := (Scheme.FiniteEtale.baseChange g).obj Z
      PreGaloisCategory.IsGalois Z ∧ PreGaloisCategory.IsGalois ZK ∧
      ConnectedSpace ZK.obj.left ∧ Surjective ZK.obj.hom ∧
      Nat.card (Aut ZK) = Nat.card (Aut Z) ∧
      Nat.card (Aut ZK) ∣ n ^ Group.rank (Multiplicative A) ∧
      zK.left ≫ pullback.fst Z.obj.hom g = q ≫ z.left ∧
      h1Pullback.{u, u + 2, u + 2} ZK.obj.hom (ConstantFinite.coefficient A _) c = 0 := by
  let : IsIntegral X.left := Curve.curveProperties_isIntegral
    Scheme.smoothFieldNormality Scheme.normalComponentsOpen hX
  let : IsIntegral U := isIntegral_of_isOpenImmersion j
  let : GeometricallyConnected (Spec.algebraMap k K) :=
    Scheme.Geometrically.fieldSpec_geometricallyConnected k K
  obtain ⟨Z, z, zK, hZ, _hconn, hsurj, hcard, hpoint, hzero⟩ :=
    exists_pointed_source_galois_effacement k K X hX j x hx A n hpos hn hk c
  let : PreGaloisCategory.IsGalois Z := hZ
  let : Surjective Z.obj.hom := hsurj
  have hG := Scheme.FiniteEtale.fieldExtension_baseChange_isGalois k K (j ≫ X.hom) Z
  have hC := Scheme.FiniteEtale.fieldExtension_baseChange_connected k K (j ≫ X.hom) Z
  have hcardEq := Scheme.FiniteEtale.fieldExtension_baseChange_card_aut k K (j ≫ X.hom) Z
  refine ⟨Z, z, zK, hZ, hG, hC, ?_, hcardEq, (by rw [hcardEq]; exact hcard), hpoint, hzero⟩
  exact inferInstanceAs (Surjective
    (pullback.snd Z.obj.hom (pullback.fst (j ≫ X.hom) (Spec.algebraMap k K))))

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves.PointedGaloisEffacement
