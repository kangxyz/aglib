/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.BaseChange.Group

/-! # The whole original Cartier evaluation commutes with native base change -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

universe u
open AlgebraicGeometry.Scheme.OverField (FScheme Base)
attribute [local instance] Over.cartesianMonoidalCategory

/-- Equality against the whole original evaluation detects actual maps to the dual. -/
theorem dual_point_ext {k : Type u} [Field k] (G : Grp (FScheme k))
    [IsFinite G.X.hom] [IsCommMonObj G.X] (T : FScheme k)
    {p q : T ⟶ (dualGroup G).X}
    (h : (𝟙 G.X ⊗ₘ p) ≫ evaluation G = (𝟙 G.X ⊗ₘ q) ≫ evaluation G) : p = q := by
  apply characterOfPoint_injective G T
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w _).trans (Over.w _).symm
  · have hp := characterOfPoint_evaluation G T p
    have hq := characterOfPoint_evaluation G T q
    have hv := congrArg (fun a => a.left ≫ prod.snd) h
    exact hp.trans (hv.trans hq.symm)

private theorem groupPullbackBaseMap_tensor_same {k : Type u} [Field k]
    (G : Grp (FScheme k)) {T U : FScheme k} (h : U ⟶ T) :
    groupPullbackBaseMap G h = (𝟙 G.X ⊗ₘ h).left := rfl

variable {k : Type u} [Field k] (K : Type u) [Field K]
  (G : Grp (FScheme k)) [IsFinite G.X.hom] [IsCommMonObj G.X]

/-- The whole original evaluation diagram, on the same pulled primal and dual objects. -/
theorem dualGroupBaseChangeIso_evaluation (i : Base K ⟶ Base k) :
    (𝟙 ((Over.pullback i).mapGrp.obj G).X ⊗ₘ
        (dualGroupBaseChangeIso K G i).hom.hom.hom) ≫
        evaluation (k := K) ((Over.pullback i).mapGrp.obj G) =
      (Functor.LaxMonoidal.μ (Over.pullback i) G.X (dualGroup G).X) ≫
        (Over.pullback i).map (evaluation G) ≫
        (MultiplicativeBaseChange.unitsBaseChangeIso i).hom.hom.hom := by
  let H := (Over.pullback i).mapGrp.obj G
  let T := ((Over.pullback i).mapGrp.obj (dualGroup G)).X
  let q := ((Over.mapPullbackAdj i).homEquiv T (dualGroup G).X).symm (𝟙 T)
  have hcharacter := dualGroupBaseChangeOverIso_character K G i T (𝟙 T)
  have hbase := characterEquivBaseChange_toOriginal G (Over.mk i) T (𝟙 T)
  have hchar := congrArg
    (fun c => (BaseChange.groupSchemeBaseChangeComp T.hom i).hom.app G ≫ c) hcharacter
  dsimp only [Over.mk_hom, Over.mk_left] at hbase
  have hwhole := hchar.trans hbase
  have hcoord := congrArg (fun c => c.hom.hom.left ≫ prod.snd) hwhole
  have hleft := characterOfPoint_evaluation (k := K) H T
    (dualGroupBaseChangeOverIso K G i).hom
  have horiginal := characterOfPoint_evaluation G ((Over.map i).obj T) q
  have hq : q.left = pullback.fst (dualGroup G).X.hom i := by
    simp only [q, MultiplicativeBaseChange.pullbackAdj_symm_left,
      Over.id_left, Category.id_comp]
  have hprojection :
      ((BaseChange.groupSchemeBaseChangeComp T.hom i).hom.app G).hom.hom.left ≫
        (Functor.LaxMonoidal.μ (Over.pullback i) G.X (dualGroup G).X).left ≫
        pullback.fst (G.X ⊗ (dualGroup G).X).hom i = groupPullbackBaseMap G q := by
    have h1 := BaseChange.groupSchemeBaseChangeComp_hom_left_fst_fst T.hom i G
    have h2 := BaseChange.groupSchemeBaseChangeComp_hom_left_snd T.hom i G
    have hm1 := Over.μ_pullback_left_fst_fst (f := i) G.X (dualGroup G).X
    have hm2 := Over.μ_pullback_left_fst_snd (f := i) G.X (dualGroup G).X
    dsimp only [T, BaseChange.groupSchemeBaseChange, Functor.comp_obj,
      Functor.mapGrp_obj_X, Over.pullback_obj_hom, Over.pullback_obj_left,
      Over.map_obj_hom] at h1 h2 hm1 hm2 ⊢
    apply pullback.hom_ext
    · simpa only [Category.assoc, groupPullbackBaseMap_fst, Over.map_obj_hom,
        Over.pullback_obj_hom, hm1] using h1
    · simp only [Category.assoc, hm2, groupPullbackBaseMap_snd, hq]
      exact congrArg (fun a => a ≫ pullback.fst (dualGroup G).X.hom i) h2
  have hraw :
      (groupPullbackBaseMap (k := K) H (dualGroupBaseChangeOverIso K G i).hom) ≫
          (evaluation (k := K) H).left ≫ prod.snd =
      (Functor.LaxMonoidal.μ (Over.pullback i) G.X (dualGroup G).X).left ≫
        pullback.fst (G.X ⊗ (dualGroup G).X).hom i ≫
          (evaluation G).left ≫ prod.snd := by
    simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc,
      Category.id_comp, characterEquiv_apply] at hcoord
    have hL := congrArg
      (fun a => ((BaseChange.groupSchemeBaseChangeComp T.hom i).hom.app G).hom.hom.left ≫ a)
      hleft
    dsimp only [q, H, T, Over.map_obj_hom, Over.map_obj_left,
      BaseChange.groupSchemeBaseChange, Functor.comp_obj, Functor.mapGrp_obj_X,
      Over.pullback_obj_hom, Over.pullback_obj_left] at hL hcoord horiginal
    have hC := hL.symm.trans (hcoord.trans horiginal)
    have hP := congrArg (fun a => a ≫ (evaluation G).left ≫ prod.snd) hprojection
    simp only [Category.assoc] at hP
    apply (cancel_epi
      ((BaseChange.groupSchemeBaseChangeComp T.hom i).hom.app G).hom.hom.left).mp
    dsimp only [q, H, T, Over.map_obj_hom, Over.map_obj_left,
      BaseChange.groupSchemeBaseChange, Functor.comp_obj, Functor.mapGrp_obj_X,
      Over.pullback_obj_hom, Over.pullback_obj_left] at hP ⊢
    exact hC.trans hP.symm
  rw [dualGroupBaseChangeIso_hom]
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w _).trans (Over.w _).symm
  · simp only [Over.comp_left, Category.assoc,
      MultiplicativeBaseChange.unitsBaseChangeIso_coordinate,
      Over.pullback_map_left, pullback.lift_fst_assoc]
    rw [← groupPullbackBaseMap_tensor_same]
    dsimp only [H, T, Functor.mapGrp_obj_X, Over.pullback_obj_left,
      Over.tensorObj_left] at hraw ⊢
    exact hraw

end AlgebraicGeometry.Scheme.Group.CartierDuality
