/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Kernel.TorsorCharacter.FieldBaseChange
public import Aglib.AlgebraicGeometry.Group.Kernel.BaseChange

/-! Scalar extension of the original kernel multiplier. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory
open Scheme.OverField Scheme.Group Scheme.Modules.Invertible
open scoped CategoryTheory.MonObj

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
local notation "qK" => CategoryTheory.Functor.map (Functor.mapGrp F) q
local notation "T₀" => Functor.obj (Over.map b) T
local notation "G" => Kernel.group q
local notation "Gnew" => Kernel.group qK
local notation "e" => Kernel.baseChangeIso b q

private theorem transition_congr_second {U : FScheme k} (x y z : U ⟶ A.X) (t : U ⟶ T₀)
    (hy : x ≫ q.hom.hom = y ≫ q.hom.hom) (hz : x ≫ q.hom.hom = z ≫ q.hom.hom)
    (h : y = z) :
    familyTransitionUnit q T₀ M a x y t hy = familyTransitionUnit q T₀ M a x z t hz := by
  subst z
  rfl

/-- The multiplier of the transported original frame is the pullback of the
original multiplier along the inverse kernel comparison and family comparison. -/
theorem kernelMultiplier_fieldBaseChange [IsProper A.X.hom] [GeometricallyIntegral A.X.hom] :
    kernelMultiplier qK (Kernel.marking qK) T
        (pullbackLineBundle (familyBaseChangeIso B.X.hom b T).hom M)
        (fieldBaseChangeFamilyFrame q T M a) =
      Units.map
        (familyMapOfHom (e).inv.hom.hom T ≫
          (familyBaseChangeIso (G).X.hom b T).hom).appTop.hom.toMonoidHom
        (kernelMultiplier q (Kernel.marking q) T₀ M a) := by
  let U := (Gnew).X ⊗ T
  let g : U ⟶ (Gnew).X := fst (Gnew).X T
  let t : U ⟶ T := snd (Gnew).X T
  let g' := g ≫ (e).inv.hom.hom
  let ad := Over.mapPullbackAdj b
  let x : U ⟶ ((F).mapGrp.obj A).X := 1
  let y := (Kernel.marking qK).toTorsorAction.act g x
  let x₀ := (ad.homEquiv U A.X).symm x
  let y₀ := (ad.homEquiv U A.X).symm y
  let g₀ := (ad.homEquiv U (G).X).symm g'
  let t₀ := (Over.map b).map t
  have hI : (e).inv ≫ (F).mapGrp.map (Kernel.inclusion q) = Kernel.inclusion qK := by
    calc
      _ = (e).inv ≫ ((e).hom ≫ Kernel.inclusion qK) :=
        congrArg (fun f => (e).inv ≫ f) (Kernel.baseChangeIso_hom_inclusion b q).symm
      _ = _ := (e).inv_hom_id_assoc _
  have hi : (e).inv.hom.hom ≫ (F).map (Kernel.inclusion q).hom.hom =
      (Kernel.inclusion qK).hom.hom :=
    congrArg (fun f : Gnew ⟶ ((F).mapGrp.obj A) => f.hom.hom) hI
  have hg : g' ≫ (F).map (Kernel.inclusion q).hom.hom = g ≫ (Kernel.inclusion qK).hom.hom :=
    (Category.assoc _ _ _).trans (congrArg (fun f => g ≫ f) hi)
  let pointEquiv := MultiplicativeBaseChange.pullbackSectionsEquiv b A U
  have ha : (ad.homEquiv U A.X).symm (g' ≫ (F).map (Kernel.inclusion q).hom.hom) =
      g₀ ≫ (Kernel.inclusion q).hom.hom :=
    ad.homEquiv_naturality_right_symm g' (Kernel.inclusion q).hom.hom
  have hy : y₀ = (Kernel.marking q).toTorsorAction.act g₀ x₀ := calc
    _ = pointEquiv ((g ≫ (Kernel.inclusion qK).hom.hom) * x) := rfl
    _ = pointEquiv (g ≫ (Kernel.inclusion qK).hom.hom) * pointEquiv x := map_mul pointEquiv _ _
    _ = pointEquiv (g' ≫ (F).map (Kernel.inclusion q).hom.hom) * pointEquiv x :=
      congrArg (fun f => pointEquiv f * pointEquiv x) hg.symm
    _ = _ := congrArg (fun f => f * x₀) ha
  have h₀ := ((Kernel.marking q).toTorsorAction.over g₀ x₀).symm
  have h : x₀ ≫ q.hom.hom = y₀ ≫ q.hom.hom :=
    h₀.trans (congrArg (fun f => f ≫ q.hom.hom) hy.symm)
  have hbase : kernelMultiplier qK (Kernel.marking qK) T
        (pullbackLineBundle (familyBaseChangeIso B.X.hom b T).hom M)
        (fieldBaseChangeFamilyFrame q T M a) =
      familyTransitionUnit q T₀ M a x₀ y₀ t₀ h :=
    familyTransitionUnit_fieldBaseChange q T M a x y t
      ((Kernel.marking qK).toTorsorAction.over g x).symm
  have hp : (lift g' t).left = familyMapOfHom (e).inv.hom.hom T := by
    have h' := lift_comp_familyMap (e).inv T g t
    have hgt : lift g t = 𝟙 U := by simp only [g, t, U, lift_fst_snd]
    rw [hgt, Over.id_left, Category.id_comp] at h'
    exact h'.symm
  have hf : (lift g₀ t₀).left = familyMapOfHom (e).inv.hom.hom T ≫
      (familyBaseChangeIso (G).X.hom b T).hom :=
    (lift_left_comp_familyBaseChangeIso b (G).X g' t).symm.trans
      (congrArg (fun f => f ≫ (familyBaseChangeIso (G).X.hom b T).hom) hp)
  exact hbase.trans ((transition_congr_second q T M a x₀ y₀ _ t₀ h h₀ hy).trans
    ((familyTransitionUnit_kernel_translate q (Kernel.marking q) T₀ M a x₀ g₀ t₀).trans
      (congrArg (fun f => Units.map f.appTop.hom.toMonoidHom
        (kernelMultiplier q (Kernel.marking q) T₀ M a)) hf)))

end AlgebraicGeometry.Scheme.RelativePicard
