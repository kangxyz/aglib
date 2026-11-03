/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.Boundary
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.AlgebraicExtension.FiniteConstantDescent
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.FiniteConstantOpenVanishing
public import Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Fibre

/-! # Higher constant classes vanish after an actual finite field extension

Algebraically closed ordinary curve vanishing is used only on the actual
algebraic-closure base change. Native zero descent then returns a finite
intermediate field. The original source class and restriction map are unchanged;
no separably closed vanishing or purely inseparable comparison is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.OverField

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

private theorem noetherian_open {X U : Scheme.{u}} [IsNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] : IsNoetherian U := by
  let : IsLocallyNoetherian U := isLocallyNoetherian_of_isOpenImmersion j
  let : TopologicalSpace.NoetherianSpace U :=
    j.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  exact ⟨⟩

/-- Every original higher finite-constant class on the specified noncomplete
open curve becomes zero at an actual finite algebraic field stage. -/
theorem exists_finiteField_killing_higher_constant
    (k : Type u) [Field k] (X : FScheme k) (hX : Curve.Properties X)
    {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j]
    (hx : ∃ x : X.left, x ∉ Set.range j)
    (A : Type u) [AddCommGroup A] [Finite A]
    (n : ℕ) (hn : 0 < n) (hkill : ∀ a : A, n • a = 0) (hunit : IsUnit (n : k))
    (q : ℕ) (hq : 2 ≤ q)
    (c : Sheaf.H.{u + 2} (ConstantFinite.coefficient A U) q) :
    ∃ s : Finset (AlgebraicClosure k),
      Curves.constantRestriction.{u, u + 2, u + 2} A
        ((FiniteEtale.FieldLimit.schemeDiagram k (AlgebraicClosure k) (j ≫ X.hom)).obj
          (op s)).hom q c = 0 := by
  let Ω := AlgebraicClosure k
  let b := Spec.algebraMap k Ω
  let p := j ≫ X.hom
  let XΩ : FScheme Ω := Over.mk (pullback.snd X.hom b)
  have hXΩ : Curve.Properties XΩ := Curve.curveProperties_baseChange hX Ω b
  let : IsNoetherian X.left := Curve.curveProperties_isNoetherian hX
  let : IsNoetherian U := noetherian_open j
  let : IsNoetherian XΩ.left := Curve.curveProperties_isNoetherian hXΩ
  let jΩ : pullback p b ⟶ XΩ.left := Hom.fibreInclusion X.hom j b
  have H := Hom.fibreInclusion_isPullback X.hom j b
  let : IsOpenImmersion jΩ := MorphismProperty.of_isPullback H inferInstance
  let : Surjective b := inferInstanceAs (Surjective (Spec.algebraMap k Ω))
  let a : XΩ.left ⟶ X.left := pullback.fst X.hom b
  let : Surjective a := inferInstanceAs (Surjective (pullback.fst X.hom b))
  have hboundary : ∃ x : XΩ.left, IsClosed ({x} : Set XΩ.left) ∧ x ∉ Set.range jΩ :=
    exists_closedPoint_outside_of_surjective_square j jΩ a (pullback.fst p b) H.w.symm hx
  have hunitΩ : IsUnit (n : Ω) := by
    simpa only [map_natCast] using hunit.map (algebraMap k Ω)
  have hzero := Curves.finiteConstant_subsingleton_H_of_isOpenImmersion
    hXΩ jΩ hboundary A n hn hkill hunitΩ q hq
  have hc : Curves.constantRestriction.{u, u + 2, u + 2} A (pullback.fst p b) q c = 0 :=
    hzero.elim _ _
  exact ConstantFinite.AlgebraicExtension.exists_finiteField_constantRestriction_eq_zero
    k Ω p A q c hc

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
