/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteColimits.ConstantRestriction
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sigma

/-! # Actual local value maps for finite constant source families

Finite intersections of the original section-lifting covers give a single
actual etale chart on which all original source values lift. Injectivity
of the original constant unit at the retained chart point proves the
additive laws. The unit-normalized constant restriction then identifies
the full original restricted arrows with the produced value maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteColimits

universe u v

attribute [local instance] hasSheafifyLarge

/-- A finite family of sections of original constant sheaves lifts to
literal additive values on one actual etale chart at the given point. -/
theorem exists_etale_constant_labels_at_point (X : Scheme.{u})
    {ι : Type v} [Finite ι] (B : ι → AddCommGrpCat.{u + 1})
    (s : ∀ i, ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (B i)).obj.obj
      (op (etaleTerminal X))) (x : X) :
    ∃ (U : X.Etale) (g : U ⟶ etaleTerminal X) (y : U.left), U.hom y = x ∧
      ∃ b : ∀ i, B i,
        ∀ i, (constantPresheafUnit X (B i)).app (op U) (b i) =
          ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (B i)).obj.map
            g.op (s i) := by
  classical
  let := Fintype.ofFinite ι
  let R (i : ι) : X.smallEtaleTopology.Cover (etaleTerminal X) :=
    ⟨Presheaf.imageSieve (constantPresheafUnit X (B i)) (s i),
      Presheaf.imageSieve_mem X.smallEtaleTopology (constantPresheafUnit X (B i)) (s i)⟩
  let T : X.smallEtaleTopology.Cover (etaleTerminal X) := Finset.univ.inf R
  have hT := T.condition
  change _ ∈ X.smallGrothendieckTopology @Etale (etaleTerminal X) at hT
  rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
    Scheme.mem_toGrothendieck_smallPretopology] at hT
  obtain ⟨U, g, y, hg, _, hy⟩ := hT x
  have hlabel (i : ι) : ∃ b : B i,
      (constantPresheafUnit X (B i)).app (op U) b =
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (B i)).obj.map
          g.op (s i) := by
    have hle : T ≤ R i := Finset.inf_le (Finset.mem_univ i)
    exact hle g hg
  choose b hb using hlabel
  have hw : (g.left : U.left ⟶ X) = U.hom := by
    have hw := MorphismProperty.Over.w g
    change g.left ≫ 𝟙 X = U.hom at hw
    exact (Category.comp_id g.left).symm.trans hw
  change g.left y = x at hy
  exact ⟨U, g, y, (congrArg (fun f : U.left ⟶ X => f y) hw).symm.trans hy, b, hb⟩

/-- Original maps from a finite family of finite constant sources become
actual additive value maps on one actual etale chart at an original point.
No connectedness or Noetherian condition is used, and target values need
not be finite for this local lifting statement. -/
theorem exists_etale_valueMaps_at_point (X : Scheme.{u})
    {ι : Type v} [Finite ι] (A B : ι → AddCommGrpCat.{u + 1}) [∀ i, Finite (A i)]
    (q : ∀ i, (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (A i) ⟶
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (B i)) (x : X) :
    ∃ (U : X.Etale) (y : U.left), U.hom y = x ∧ ∃ g : ∀ i, A i ⟶ B i,
      ∀ i, (etaleRestrictionConstantIso U.hom (A i)).hom ≫ (etaleRestriction U.hom).map (q i) =
        (constantSheaf U.left.smallEtaleTopology AddCommGrpCat.{u + 1}).map (g i) ≫
          (etaleRestrictionConstantIso U.hom (B i)).hom := by
  let K := Σ i, A i
  let s (k : K) := (q k.1).hom.app (op (etaleTerminal X))
    ((constantPresheafUnit X (A k.1)).app (op (etaleTerminal X)) k.2)
  obtain ⟨U, r, y, hy, b, hb⟩ := exists_etale_constant_labels_at_point X
    (fun k : K => B k.1) s x
  have hv (i : ι) (a : A i) :
      (constantPresheafUnit X (B i)).app (op U) (b ⟨i, a⟩) =
        (q i).hom.app (op U) ((constantPresheafUnit X (A i)).app (op U) a) := by
    calc
      _ = ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (B i)).obj.map
          r.op ((q i).hom.app (op (etaleTerminal X))
            ((constantPresheafUnit X (A i)).app (op (etaleTerminal X)) a)) := hb ⟨i, a⟩
      _ = (q i).hom.app (op U)
          (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (A i)).obj.map r.op
            ((constantPresheafUnit X (A i)).app (op (etaleTerminal X)) a)) :=
        (ConcreteCategory.congr_hom ((q i).hom.naturality r.op)
          ((constantPresheafUnit X (A i)).app (op (etaleTerminal X)) a)).symm
      _ = _ := congrArg ((q i).hom.app (op U))
        (ConcreteCategory.congr_hom ((constantPresheafUnit X (A i)).naturality r.op) a).symm
  let g (i : ι) : A i ⟶ B i := AddCommGrpCat.ofHom {
    toFun := fun a => b ⟨i, a⟩
    map_zero' := by
      apply constantPresheafUnit_injective_at_point X (B i) U y
      rw [hv i 0]
      simp
    map_add' := by
      intro a a'
      apply constantPresheafUnit_injective_at_point X (B i) U y
      rw [map_add, hv i (a + a'), hv i a, hv i a']
      simp only [map_add] }
  exact ⟨U, y, hy, g, fun i =>
    etaleRestriction_map_constant_of_unit_eq U (A i) (B i) (q i) (g i) (hv i)⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteColimits
