/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Monoidal.Cartesian.CommutativeGroupSections
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup

/-!
# Reflection on the original represented group and section carriers

The exact supplied representation selects its original group object. The actual
monoidal inclusion and fully faithful test inclusion extend its universal product
law to every test. Additive maps on the same lifted sections reflect both group
map laws on the original raw preimage, using actual terminal and product tests.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open scoped CategoryTheory.MonObj

namespace CategoryTheory.CommutativeGroupSections

universe wH wK wA uD vD uE vE uB vB
variable {D : Type uD} [Category.{vD} D]
  [CartesianMonoidalCategory D]
variable {E : Type uE} [Category.{vE} E]

section OriginalRepresentation

variable {B : Type uB} [Category.{vB} B]
  [CartesianMonoidalCategory B] [BraidedCategory B]
variable (T : E ⥤ D) (I : B ⥤ E) (J : B ⥤ D) [J.Monoidal]
variable (β : I ⋙ T ≅ J) (hT : T.FullyFaithful)
variable (A : Eᵒᵖ ⥤ AddCommGrpCat.{wA}) (Y : B)
variable (α : ((I.op ⋙ A ⋙ AddCommGrpCat.toCommGrp) ⋙ CategoryTheory.forget _).RepresentableBy Y)
variable (ξ : ∀ U, (T.obj U ⟶ J.obj Y) ≃ A.obj (op U))
variable (hξ : ∀ {U V} (q : U ⟶ V) (g : T.obj V ⟶ J.obj Y),
  ξ U (T.map q ≫ g) = A.map q.op (ξ V g))
variable (hα : ∀ (Z : B) (f : Z ⟶ Y),
  (α.homEquiv f).toAdd = ξ (I.obj Z) ((β.app Z).hom ≫ J.map f))

include β hT hξ hα in
/-- The exact original representation and monoidal image give the section law on all tests.
The universal product equation is derived from the original constructor, not assumed. -/
theorem sectionEquiv_mul_of_original_representation :
    letI := CommGrpObj.ofRepresentableBy Y (I.op ⋙ A ⋙ AddCommGrpCat.toCommGrp) α
    let H : Grp D := J.mapGrp.obj { X := Y }
    ∀ (U : E) (f g : T.obj U ⟶ H.X), ξ U (f * g) = ξ U f + ξ U g := by
  let := CommGrpObj.ofRepresentableBy Y (I.op ⋙ A ⋙ AddCommGrpCat.toCommGrp) α
  let H : Grp D := J.mapGrp.obj { X := Y }
  change ∀ (U : E) (f g : T.obj U ⟶ H.X), ξ U (f * g) = ξ U f + ξ U g
  intro U f g
  change T.obj U ⟶ J.obj Y at f g
  let V := I.obj (Y ⊗ Y)
  let eP : (Y ⊗ Y ⟶ Y) ≃ Multiplicative (A.obj (op V)) := α.homEquiv
  have hmα : (eP (μ[Y])).toAdd =
      (eP (fst Y Y)).toAdd + (eP (snd Y Y)).toAdd := by
    exact congrArg (fun x : Multiplicative (A.obj (op V)) => x.toAdd) (eP.apply_symm_apply
      (Multiplicative.ofAdd ((eP (fst Y Y)).toAdd + (eP (snd Y Y)).toAdd)))
  have hm : ξ V ((β.app (Y ⊗ Y)).hom ≫ J.map μ[Y]) =
      ξ V ((β.app (Y ⊗ Y)).hom ≫ J.map (fst Y Y)) +
        ξ V ((β.app (Y ⊗ Y)).hom ≫ J.map (snd Y Y)) :=
    (hα (Y ⊗ Y) μ[Y]).symm.trans (hmα.trans
      (congrArg₂ (fun x y : A.obj (op V) => x + y)
        (hα (Y ⊗ Y) (fst Y Y)) (hα (Y ⊗ Y) (snd Y Y))))
  let d : T.obj U ⟶ J.obj (Y ⊗ Y) := lift f g ≫ Functor.LaxMonoidal.μ J Y Y
  let q : U ⟶ V := hT.preimage (d ≫ (β.app (Y ⊗ Y)).inv)
  have hq : T.map q ≫ (β.app (Y ⊗ Y)).hom = d := by
    calc
      _ = (d ≫ (β.app (Y ⊗ Y)).inv) ≫ (β.app (Y ⊗ Y)).hom :=
        congrArg (fun k : T.obj U ⟶ T.obj V => k ≫ (β.app (Y ⊗ Y)).hom)
          (hT.map_preimage (d ≫ (β.app (Y ⊗ Y)).inv))
      _ = d ≫ ((β.app (Y ⊗ Y)).inv ≫ (β.app (Y ⊗ Y)).hom) := Category.assoc _ _ _
      _ = d ≫ 𝟙 _ := congrArg (fun k => d ≫ k) (β.app (Y ⊗ Y)).inv_hom_id
      _ = d := Category.comp_id _
  have hf : T.map q ≫ ((β.app (Y ⊗ Y)).hom ≫ J.map (fst Y Y)) = f := by
    rw [← Category.assoc, hq]
    dsimp [d]
    rw [Category.assoc, Functor.Monoidal.μ_fst, lift_fst]
  have hg : T.map q ≫ ((β.app (Y ⊗ Y)).hom ≫ J.map (snd Y Y)) = g := by
    rw [← Category.assoc, hq]
    dsimp [d]
    rw [Category.assoc, Functor.Monoidal.μ_snd, lift_snd]
  change ξ U (lift f g ≫ (Functor.LaxMonoidal.μ J Y Y ≫ J.map μ[Y])) = _
  rw [← Category.assoc]
  change ξ U (d ≫ J.map μ[Y]) = _
  calc
    _ = ξ U (T.map q ≫ ((β.app (Y ⊗ Y)).hom ≫ J.map μ[Y])) := by
      rw [← Category.assoc, hq]
    _ = A.map q.op (ξ V ((β.app (Y ⊗ Y)).hom ≫ J.map μ[Y])) := hξ q _
    _ = A.map q.op (ξ V ((β.app (Y ⊗ Y)).hom ≫ J.map (fst Y Y)) +
        ξ V ((β.app (Y ⊗ Y)).hom ≫ J.map (snd Y Y))) := congrArg (A.map q.op) hm
    _ = A.map q.op (ξ V ((β.app (Y ⊗ Y)).hom ≫ J.map (fst Y Y))) +
        A.map q.op (ξ V ((β.app (Y ⊗ Y)).hom ≫ J.map (snd Y Y))) := map_add _ _ _
    _ = ξ U (T.map q ≫ ((β.app (Y ⊗ Y)).hom ≫ J.map (fst Y Y))) +
        ξ U (T.map q ≫ ((β.app (Y ⊗ Y)).hom ≫ J.map (snd Y Y))) :=
      congrArg₂ (fun x y : A.obj (op U) => x + y) (hξ q _).symm (hξ q _).symm
    _ = ξ U f + ξ U g := by rw [hf, hg]

end OriginalRepresentation

section Reflection

variable [BraidedCategory D]
variable (T : E ⥤ D)
variable (H K : Grp D) [IsCommMonObj H.X] [IsCommMonObj K.X]
variable (U₀ U₂ : E)
variable (κ₀ : T.obj U₀ ≅ 𝟙_ D) (κ₂ : T.obj U₂ ≅ H.X ⊗ H.X)
variable (Q : ∀ U, Sections.{wH} H (T.obj U) →+ Sections.{wK} K (T.obj U))
variable (r : H.X ⟶ K.X)
variable (hr : ∀ U (f : T.obj U ⟶ H.X),
  (ULift.up (Additive.ofMul (f ≫ r)) : Sections.{wK} K (T.obj U)) =
    Q U (ULift.up (Additive.ofMul f)))

include T U₀ U₂ κ₀ κ₂ Q hr in
/-- Whole reflected laws for the SAME raw preimage and its literal ordinary component formula.
No desired monoid-hom conclusion is an input. -/
theorem isMonHom_of_original_test_sections : IsMonHom r where
  one_hom := by
    let a : Sections.{wH} H (T.obj U₀) := ULift.up (Additive.ofMul (κ₀.hom ≫ η[H.X]))
    have hz : a = 0 := by
      apply ULift.ext
      change κ₀.hom ≫ η[H.X] = toUnit (T.obj U₀) ≫ η[H.X]
      exact congrArg (fun f : T.obj U₀ ⟶ 𝟙_ D => f ≫ η[H.X]) (toUnit_unique _ _)
    have hzero : Q U₀ a = 0 :=
      (congrArg (fun s : Sections.{wH} H (T.obj U₀) => Q U₀ s) hz).trans (Q U₀).map_zero
    have he := congrArg (fun s : Sections.{wK} K (T.obj U₀) => s.down.toMul)
      ((hr U₀ (κ₀.hom ≫ η[H.X])).trans hzero)
    change (κ₀.hom ≫ η[H.X]) ≫ r = toUnit (T.obj U₀) ≫ η[K.X] at he
    apply (cancel_epi κ₀.hom).mp
    calc
      κ₀.hom ≫ (η[H.X] ≫ r) = (κ₀.hom ≫ η[H.X]) ≫ r := (Category.assoc _ _ _).symm
      _ = toUnit (T.obj U₀) ≫ η[K.X] := he
      _ = κ₀.hom ≫ η[K.X] :=
        congrArg (fun f : T.obj U₀ ⟶ 𝟙_ D => f ≫ η[K.X]) (toUnit_unique _ _)
  mul_hom := by
    let a : Sections.{wH} H (T.obj U₂) :=
      ULift.up (Additive.ofMul (κ₂.hom ≫ fst H.X H.X))
    let b : Sections.{wH} H (T.obj U₂) :=
      ULift.up (Additive.ofMul (κ₂.hom ≫ snd H.X H.X))
    have ha := hr U₂ a.down.toMul
    have hb := hr U₂ b.down.toMul
    have hab := hr U₂ (a + b).down.toMul
    have heq :
        (ULift.up (Additive.ofMul ((a + b).down.toMul ≫ r)) : Sections.{wK} K (T.obj U₂)) =
          ULift.up (Additive.ofMul (a.down.toMul ≫ r)) +
            ULift.up (Additive.ofMul (b.down.toMul ≫ r)) :=
      hab.trans (((Q U₂).map_add a b).trans
        (congrArg₂ (fun x y : Sections.{wK} K (T.obj U₂) => x + y) ha.symm hb.symm))
    have he := congrArg (fun s : Sections.{wK} K (T.obj U₂) => s.down.toMul) heq
    change ((κ₂.hom ≫ fst H.X H.X) * (κ₂.hom ≫ snd H.X H.X)) ≫ r =
      ((κ₂.hom ≫ fst H.X H.X) ≫ r) * ((κ₂.hom ≫ snd H.X H.X) ≫ r) at he
    have he' :
        κ₂.hom ≫ ((fst H.X H.X * snd H.X H.X) ≫ r) =
          κ₂.hom ≫ ((fst H.X H.X ≫ r) * (snd H.X H.X ≫ r)) := by
      simpa only [← Category.assoc, MonObj.comp_mul] using he
    apply (cancel_epi κ₂.hom).mp
    calc
      κ₂.hom ≫ (μ[H.X] ≫ r) = κ₂.hom ≫ ((fst H.X H.X * snd H.X H.X) ≫ r) := by
        rw [MonObj.mul_eq_mul]
      _ = κ₂.hom ≫ ((fst H.X H.X ≫ r) * (snd H.X H.X ≫ r)) := he'
      _ = κ₂.hom ≫ ((r ⊗ₘ r) ≫ μ[K.X]) := by
        change κ₂.hom ≫ (lift (fst H.X H.X ≫ r) (snd H.X H.X ≫ r) ≫ μ[K.X]) = _
        rw [lift_fst_comp_snd_comp]

end Reflection

end CategoryTheory.CommutativeGroupSections
