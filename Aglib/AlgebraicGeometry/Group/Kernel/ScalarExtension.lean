/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Kernel.Basic
public import Aglib.AlgebraicGeometry.Group.BaseChange.MarkedKernel
public import Aglib.AlgebraicGeometry.Group.MultiplicationSmoothEtale

/-! # Etaleness of the original scalar-extended multiplication kernel

The existing universal kernel marking is pulled back, not replaced by a new
kernel model. Its original square proves etaleness from the base-changed
group morphism. For multiplication, the power is the pointwise group law on
group-object morphisms: it is not the composition monoid of endomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group.Kernel

universe u
attribute [local instance] Over.cartesianMonoidalCategory

variable {S T : Scheme.{u}} (f : T ⟶ S) {G E : Grp (Over S)} (p : G ⟶ E)

/-- The literal pullback of the existing kernel is etale if the original
base-changed group morphism is etale. -/
theorem etale_pullback_of_etale_map
    (hp : Etale ((BaseChange.groupSchemeBaseChange f).functor.map p).hom.hom.left) :
    Etale (pullback.snd (group p).X.hom f) := by
  have h := (BaseChange.kernelMarking f (marking p)).isPullback.map (Over.forget T)
  exact MorphismProperty.of_isPullback h hp

variable (G : Grp (Over S)) [IsCommMonObj G.X]

/-- Base change preserves pointwise multiplication by the same scalar. -/
theorem map_multiplication_hom (n : ℕ) :
    ((BaseChange.groupSchemeBaseChange f).functor.map ((𝟙 G) ^ n)).hom.hom =
      (𝟙 ((BaseChange.groupSchemeBaseChange f).functor.obj G).X) ^ n := by
  let F := Over.pullback f
  let : GrpObj (F.obj G.X) := Functor.grpObjObj
  change F.map (((𝟙 G) ^ n).hom.hom) = (𝟙 (F.obj G.X)) ^ n
  have hp : (((𝟙 G) ^ n).hom.hom) = (𝟙 G.X) ^ n := by
    simp only [Grp.Hom.hom_pow, Mon.Hom.hom_pow]
    rfl
  rw [hp]
  calc
    _ = (F.map (𝟙 G.X)) ^ n := (F.homMonoidHom (X := G.X) (M := G.X)).map_pow _ _
    _ = _ := by rw [CategoryTheory.Functor.map_id]

/-- On test objects, the displayed power is the actual pointwise nth power. -/
theorem point_multiplication (n : ℕ) {V : Over S} (x : V ⟶ G.X) :
    x ≫ (((𝟙 G) ^ n).hom.hom) = x ^ n := by
  have hp : (((𝟙 G) ^ n).hom.hom) = (𝟙 G.X) ^ n := by
    simp only [Grp.Hom.hom_pow, Mon.Hom.hom_pow]
    rfl
  rw [hp, MonObj.comp_pow, Category.comp_id]

/-- A smooth original field fibre of the group makes the original
multiplication kernel etale on that field fibre. No properness, identity
component comparison, or finite-torsion hypothesis is required. -/
theorem etale_pullback_multiplication_of_smooth
    {k : Type u} [Field k] (t : Spec (.of k) ⟶ S)
    [Smooth (pullback.snd G.X.hom t)] (n : ℕ) (hn : IsUnit (n : k)) :
    Etale (pullback.snd (group ((𝟙 G) ^ n)).X.hom t) := by
  let G' := (BaseChange.groupSchemeBaseChange t).functor.obj G
  let : GrpObj ((Over.pullback t).obj G.X) := Functor.grpObjObj
  let : IsCommMonObj G'.X := inferInstanceAs (IsCommMonObj ((Over.pullback t).obj G.X))
  let : Smooth G'.X.hom := inferInstanceAs (Smooth (pullback.snd G.X.hom t))
  apply etale_pullback_of_etale_map
  rw [map_multiplication_hom]
  exact Multiplication.multiplication_etale_of_smooth_of_isUnit
    ((BaseChange.groupSchemeBaseChange t).functor.obj G) n hn

end AlgebraicGeometry.Scheme.Group.Kernel
