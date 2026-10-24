/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.LinearSystem.Basic
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Congr
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Composition
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Adjoint
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Mate
public import Aglib.AlgebraicGeometry.Modules.BaseChange.CartesianInvertibility
public import Aglib.AlgebraicGeometry.Modules.Pullback.Triangle

/-!
# The evaluation map of a family and its base change

Let `p : X ⟶ S`, `L` a line bundle on `X` and `E = p_* L`. For `T` over `S`, with
`g_T : X_T ⟶ X` and `q_T : X_T ⟶ T`, the base-change map `bc_T : E_T ⟶ q_{T*} g_T^* L`
(`familyBaseChangeMap`, the cartesian mate; `familyBaseChangeMap_eq` identifies it with
`moduleBaseChangeMap p T.hom L`) has the adjoint

`ev_T : q_T^* E_T ⟶ g_T^* L` (`evaluationMap`),

which evaluates sections of `E_T` on `X_T`. When every `moduleBaseChangeMap p g L` is an
isomorphism (cohomology and base change, statement 15a), so is the cartesian mate of every square
over the family `X_T ⟶ T` (`isIso_cartesianBaseChangeMap_family`, from transitivity
`cartesianBaseChangeMap_comp`).

* `pullback_map_evaluationMap`: for `t : T' ⟶ T` the evaluation map of `T'` is the pullback of the
  evaluation map of `T` along `b : X_{T'} ⟶ X_T`, under the canonical comparisons
  `E_{T'} ≅ t^* E_T`, `q_{T'}^* t^* ≅ b^* q_T^*` and `g_{T'}^* ≅ b^* g_T^*`. Equivalently the
  base-change maps are natural in `T`; the proof is the adjoint form of transitivity of base change
  (`cartesianBaseChangeMap_adjoint`, `cartesianBaseChangeMap_comp`,
  `cartesianBaseChangeMap_congr`).
* `pullback_fst_map_ne_zero_of_pullback_map_homEquiv_ne_zero`: a map `θ : q_T^* M ⟶ g_T^* L`
  whose adjoint is nonzero after pulling back along `v : V ⟶ T` is nonzero on `X_T ×_T V`.

This is the base-change compatibility used in Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, proof of Thm 3.13, p. 25 ("(3.13.1)", the base change of (3.10.1)) and
Ex. 3.14, p. 26. Arbitrary schemes over `S`; no Noetherian hypothesis enters these statements.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.LinearSystem

open Scheme.Modules Scheme.Modules.Invertible Scheme.RelativePicard

variable {X S : Scheme.{u}} (p : X ⟶ S) (L : LineBundle X)

/-- The base-change map `E_T ⟶ q_{T*} g_T^* L` of `E = p_* L` along `T ⟶ S`: the cartesian
mate of the defining square of `X_T`. -/
def familyBaseChangeMap (T : Over S) :
    overPullback ((pushforward p).obj L.val) T ⟶
      (pushforward (Limits.pullback.snd p T.hom)).obj
        ((Scheme.Modules.pullback (Limits.pullback.fst p T.hom)).obj L.val) :=
  (cartesianBaseChangeMap (Limits.pullback.fst p T.hom) (Limits.pullback.snd p T.hom) p T.hom
    (IsPullback.of_hasPullback p T.hom)).app L.val

/-- The family base-change map is the canonical `moduleBaseChangeMap`. -/
theorem familyBaseChangeMap_eq (T : Over S) :
    familyBaseChangeMap p L T = moduleBaseChangeMap p T.hom L.val :=
  (moduleBaseChangeMap_eq_cartesianBaseChangeMap p T.hom L.val).symm

/-- **The evaluation map** `ev_T : q_T^* E_T ⟶ g_T^* L`, the adjoint of the base-change map. -/
def evaluationMap (T : Over S) :
    (Scheme.Modules.pullback (Limits.pullback.snd p T.hom)).obj
        (overPullback ((pushforward p).obj L.val) T) ⟶
      (Scheme.Modules.pullback (Limits.pullback.fst p T.hom)).obj L.val :=
  ((pullbackPushforwardAdjunction (Limits.pullback.snd p T.hom)).homEquiv _ _).symm
    (familyBaseChangeMap p L T)

theorem homEquiv_evaluationMap (T : Over S) :
    (pullbackPushforwardAdjunction (Limits.pullback.snd p T.hom)).homEquiv _ _
      (evaluationMap p L T) = familyBaseChangeMap p L T :=
  Equiv.apply_symm_apply _ _

/-- **Base change over the family is invertible**: if every `moduleBaseChangeMap p g L` is an
isomorphism, then so is the cartesian mate of every square over `X_T ⟶ T`, at `g_T^* L`. -/
theorem isIso_cartesianBaseChangeMap_family
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (T : Over S) {W V : Scheme.{u}} (c : W ⟶ Limits.pullback p T.hom) (d : W ⟶ V)
    (v : V ⟶ T.left) (h : IsPullback c d (Limits.pullback.snd p T.hom) v) :
    IsIso ((cartesianBaseChangeMap c d (Limits.pullback.snd p T.hom) v h).app
      ((Scheme.Modules.pullback (Limits.pullback.fst p T.hom)).obj L.val)) := by
  have hT := IsPullback.of_hasPullback p T.hom
  have H := h.paste_horiz hT
  have hcomp := cartesianBaseChangeMap_comp (Limits.pullback.fst p T.hom)
    (Limits.pullback.snd p T.hom) p T.hom hT c d v h H L.val
  have h1 : IsIso ((cartesianBaseChangeMap (c ≫ Limits.pullback.fst p T.hom) d p (v ≫ T.hom)
      H).app L.val) :=
    isIso_cartesianBaseChangeMap_of_isIso_moduleBaseChangeMap _ _ _ _ H L.val (hbc _ _)
  have h2 : IsIso ((cartesianBaseChangeMap (Limits.pullback.fst p T.hom)
      (Limits.pullback.snd p T.hom) p T.hom hT).app L.val) :=
    isIso_cartesianBaseChangeMap_of_isIso_moduleBaseChangeMap _ _ _ _ hT L.val (hbc _ _)
  have h3 : IsIso ((Scheme.Modules.pullback v).map ((cartesianBaseChangeMap
      (Limits.pullback.fst p T.hom) (Limits.pullback.snd p T.hom) p T.hom hT).app L.val) ≫
      (cartesianBaseChangeMap c d (Limits.pullback.snd p T.hom) v h).app
        ((Scheme.Modules.pullback (Limits.pullback.fst p T.hom)).obj L.val) ≫
        (pushforward d).map ((pullbackComp c (Limits.pullback.fst p T.hom)).hom.app L.val)) := by
    rw [← hcomp]
    infer_instance
  have h4 : IsIso ((cartesianBaseChangeMap c d (Limits.pullback.snd p T.hom) v h).app
        ((Scheme.Modules.pullback (Limits.pullback.fst p T.hom)).obj L.val) ≫
        (pushforward d).map ((pullbackComp c (Limits.pullback.fst p T.hom)).hom.app L.val)) :=
    IsIso.of_isIso_comp_left ((Scheme.Modules.pullback v).map ((cartesianBaseChangeMap
      (Limits.pullback.fst p T.hom) (Limits.pullback.snd p T.hom) p T.hom hT).app L.val)) _
  exact IsIso.of_isIso_comp_right _
    ((pushforward d).map ((pullbackComp c (Limits.pullback.fst p T.hom)).hom.app L.val))

/-- **The evaluation map commutes with base change** (`(3.13.1)` of Kleiman's proof of Thm 3.13):
for `t : T' ⟶ T`, the pullback along `b : X_{T'} ⟶ X_T` of `ev_T`, after `E_{T'} ≅ t^* E_T` and
`q_{T'}^* t^* ≅ b^* q_T^*`, is `ev_{T'}` followed by `g_{T'}^* ≅ b^* g_T^*`. -/
theorem pullback_map_evaluationMap {T T' : Over S} (t : T' ⟶ T) :
    (Scheme.Modules.pullback (Limits.pullback.snd p T'.hom)).map
        (overPullbackIso ((pushforward p).obj L.val) t).hom ≫
      (pullbackSquareIso (familyMap p t) (Limits.pullback.snd p T'.hom)
        (Limits.pullback.snd p T.hom) t.left (familyMap_snd p t)).hom.app
          (overPullback ((pushforward p).obj L.val) T) ≫
      (Scheme.Modules.pullback (familyMap p t)).map (evaluationMap p L T) =
    evaluationMap p L T' ≫
      (pullbackTriangleIso (familyMap p t) (Limits.pullback.fst p T.hom)
        (Limits.pullback.fst p T'.hom) (familyMap_fst p t)).inv.app L.val := by
  have hT := IsPullback.of_hasPullback p T.hom
  have h' := isPullback_familyMap p t
  have H := h'.paste_horiz hT
  have h1 := cartesianBaseChangeMap_adjoint (familyMap p t)
    (Limits.pullback.snd p T'.hom) (Limits.pullback.snd p T.hom) t.left h'
    (overPullback ((pushforward p).obj L.val) T)
    ((Scheme.Modules.pullback (Limits.pullback.fst p T.hom)).obj L.val) (evaluationMap p L T)
  rw [homEquiv_evaluationMap] at h1
  have hcomp := cartesianBaseChangeMap_comp (Limits.pullback.fst p T.hom)
    (Limits.pullback.snd p T.hom) p T.hom hT (familyMap p t)
    (Limits.pullback.snd p T'.hom) t.left h' H L.val
  have hcomp' : (Scheme.Modules.pullback t.left).map (familyBaseChangeMap p L T) ≫
      (cartesianBaseChangeMap (familyMap p t) (Limits.pullback.snd p T'.hom)
        (Limits.pullback.snd p T.hom) t.left h').app
          ((Scheme.Modules.pullback (Limits.pullback.fst p T.hom)).obj L.val) =
      (pullbackComp t.left T.hom).hom.app ((pushforward p).obj L.val) ≫
        (cartesianBaseChangeMap (familyMap p t ≫ Limits.pullback.fst p T.hom)
          (Limits.pullback.snd p T'.hom) p (t.left ≫ T.hom) H).app L.val ≫
        (pushforward (Limits.pullback.snd p T'.hom)).map
          ((pullbackComp (familyMap p t) (Limits.pullback.fst p T.hom)).inv.app
            L.val) := by
    rw [← Category.assoc, hcomp]
    simp only [familyBaseChangeMap, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      Functor.comp_obj, CategoryTheory.Functor.map_id, Category.comp_id]
  have hcongr := cartesianBaseChangeMap_congr (Limits.pullback.snd p T'.hom) p
    (familyMap_fst p t) (Over.w t) H (IsPullback.of_hasPullback p T'.hom) L.val
  apply ((pullbackPushforwardAdjunction (Limits.pullback.snd p T'.hom)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, ← h1, Adjunction.homEquiv_naturality_right,
    homEquiv_evaluationMap, hcomp', overPullbackIso_hom, pullbackTriangleIso_inv_app,
    pullbackTriangleIso_inv_app]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]
  rw [← Category.assoc, hcongr, Category.assoc]
  rfl

/-- **Fibre nonvanishing from the adjoint**: if base change over the family is invertible, a map
`θ : q_T^* M ⟶ g_T^* L` whose adjoint `M ⟶ q_{T*} g_T^* L` is nonzero after pullback along
`v : V ⟶ T` is nonzero after pullback to `X_T ×_T V`. -/
theorem pullback_fst_map_ne_zero_of_pullback_map_homEquiv_ne_zero
    (hbc : ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (moduleBaseChangeMap p g L.val))
    (T : Over S) {M : T.left.Modules}
    (θ : (Scheme.Modules.pullback (Limits.pullback.snd p T.hom)).obj M ⟶
      (Scheme.Modules.pullback (Limits.pullback.fst p T.hom)).obj L.val)
    {V : Scheme.{u}} (v : V ⟶ T.left)
    (hθ : (Scheme.Modules.pullback v).map
      ((pullbackPushforwardAdjunction (Limits.pullback.snd p T.hom)).homEquiv _ _ θ) ≠ 0) :
    (Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd p T.hom) v)).map θ ≠ 0 := by
  intro h0
  apply hθ
  have hv := IsPullback.of_hasPullback (Limits.pullback.snd p T.hom) v
  have := isIso_cartesianBaseChangeMap_family p L hbc T _ _ v hv
  have hadj := cartesianBaseChangeMap_adjoint _ _ (Limits.pullback.snd p T.hom) v hv M
    ((Scheme.Modules.pullback (Limits.pullback.fst p T.hom)).obj L.val) θ
  have hz : (pullbackPushforwardAdjunction
      (Limits.pullback.snd (Limits.pullback.snd p T.hom) v)).homEquiv _ _
      ((pullbackSquareIso _ _ _ _ hv.w).hom.app M ≫
        (Scheme.Modules.pullback (Limits.pullback.fst (Limits.pullback.snd p T.hom) v)).map θ) =
      0 := by
    rw [h0, comp_zero, Adjunction.homEquiv_unit, CategoryTheory.Functor.map_zero, comp_zero]
  exact (cancel_mono _).mp ((hadj.trans hz).trans zero_comp.symm)

end AlgebraicGeometry.Scheme.LinearSystem
