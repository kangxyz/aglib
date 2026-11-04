/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.EvaluationLaws

/-! Native character restriction and representability under field base change. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

universe u

open AlgebraicGeometry.Scheme.OverField (FScheme Base)

/-- Native group pullback preserves finiteness of its structural scheme map. -/
instance groupPullback_finite {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
    (G : Grp (Over S)) [IsFinite G.X.hom] :
    IsFinite ((Over.pullback f).mapGrp.obj G).X.hom := by
  change IsFinite (pullback.snd G.X.hom f)
  infer_instance

/-- Native group pullback preserves the original commutative group structure. -/
instance groupPullback_isComm {S T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
    (G : Grp (Over S)) [IsCommMonObj G.X] :
    IsCommMonObj ((Over.pullback f).mapGrp.obj G).X := by
  change IsCommMonObj ((Over.pullback f).obj G.X)
  infer_instance

variable {k : Type u} [Field k] (K : Type u) [Field K]
  (G : Grp (FScheme k))

private theorem baseChangeComp_baseMap (i : Base K ⟶ Base k)
    {U V : FScheme K} (h : V ⟶ U) :
    let H : Grp (FScheme K) := (Over.pullback i).mapGrp.obj G
    ((BaseChange.groupSchemeBaseChangeComp V.hom i).hom.app G).hom.hom.left ≫
        groupPullbackBaseMap (k := K) H h =
      groupPullbackBaseMap (k := k) G ((Over.map i).map h) ≫
        ((BaseChange.groupSchemeBaseChangeComp U.hom i).hom.app G).hom.hom.left := by
  intro H
  let a := ((BaseChange.groupSchemeBaseChangeComp V.hom i).hom.app G).hom.hom.left
  let b := ((BaseChange.groupSchemeBaseChangeComp U.hom i).hom.app G).hom.hom.left
  let u := groupPullbackBaseMap (k := K) H h
  let v := groupPullbackBaseMap (k := k) G ((Over.map i).map h)
  have hHfG := groupPullbackBaseMap_fst_assoc (k := K) H h (pullback.fst G.X.hom i)
  have hHfK := groupPullbackBaseMap_fst_assoc (k := K) H h (pullback.snd G.X.hom i)
  have hHs := groupPullbackBaseMap_snd (k := K) H h
  have hGf := groupPullbackBaseMap_fst (k := k) G ((Over.map i).map h)
  have hGs := groupPullbackBaseMap_snd (k := k) G ((Over.map i).map h)
  have hVf := BaseChange.groupSchemeBaseChangeComp_hom_left_fst_fst V.hom i G
  have hVk := BaseChange.groupSchemeBaseChangeComp_hom_left_fst_snd V.hom i G
  have hVs := BaseChange.groupSchemeBaseChangeComp_hom_left_snd V.hom i G
  have hUf := BaseChange.groupSchemeBaseChangeComp_hom_left_fst_fst U.hom i G
  have hUk := BaseChange.groupSchemeBaseChangeComp_hom_left_fst_snd U.hom i G
  have hUs := BaseChange.groupSchemeBaseChangeComp_hom_left_snd U.hom i G
  have hL1 := congrArg (fun q => a ≫ q) hHfG
  have hR1 := congrArg (fun q => v ≫ q) hUf
  have hE1 := hL1.trans (hVf.trans (hR1.trans hGf).symm)
  have hL2 := congrArg (fun q => a ≫ q) hHfK
  have hR2 := congrArg (fun q => v ≫ q) hUk
  have hGsK := congrArg (fun q => q ≫ U.hom) hGs
  simp only [Category.assoc] at hGsK
  have hw := congrArg (fun q => pullback.snd G.X.hom (V.hom ≫ i) ≫ q) (Over.w h)
  have hE2 := hL2.trans (hVk.trans (hR2.trans (hGsK.trans hw)).symm)
  have hL3 := congrArg (fun q => a ≫ q) hHs
  have hR3 := congrArg (fun q => v ≫ q) hUs
  have hVsH := congrArg (fun q => q ≫ h.left) hVs
  have hE3 := hL3.trans (hVsH.trans (hR3.trans hGs).symm)
  dsimp only [H, a, b, u, v, BaseChange.groupSchemeBaseChange,
    Functor.comp_obj, Functor.mapGrp_obj_X, Over.pullback_obj_hom,
    Over.pullback_obj_left] at hE1 hE2 hE3 ⊢
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · let p := pullback.fst H.X.hom U.hom
      let q := pullback.fst G.X.hom i
      have hAL := (Category.assoc (a ≫ u) p q).trans (Category.assoc a u (p ≫ q))
      have hAR := (Category.assoc (v ≫ b) p q).trans (Category.assoc v b (p ≫ q))
      exact hAL.trans (hE1.trans hAR.symm)
    · let p := pullback.fst H.X.hom U.hom
      let q := pullback.snd G.X.hom i
      have hAL := (Category.assoc (a ≫ u) p q).trans (Category.assoc a u (p ≫ q))
      have hAR := (Category.assoc (v ≫ b) p q).trans (Category.assoc v b (p ≫ q))
      exact hAL.trans (hE2.trans hAR.symm)
  · exact (Category.assoc a u (pullback.snd H.X.hom U.hom)).trans
      (hE3.trans (Category.assoc v b (pullback.snd H.X.hom U.hom)).symm)

private theorem gm_groupMap_ext {S : AlgebraicGeometry.Scheme.{u}} {X : Grp (Over S)}
    {f g : X ⟶ MultiplicativeGroup.groupScheme S}
    (h : f.hom.hom.left ≫ prod.snd = g.hom.hom.left ≫ prod.snd) : f = g := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w f.hom.hom).trans (Over.w g.hom.hom).symm
  · exact h

private theorem gm_comp_coordinates {S : AlgebraicGeometry.Scheme.{u}}
    {X Y : Grp (Over S)} (a : X ⟶ Y) (c : Y ⟶ MultiplicativeGroup.groupScheme S) :
    (a ≫ c).hom.hom.left ≫ prod.snd =
      a.hom.hom.left ≫ c.hom.hom.left ≫ prod.snd := by
  exact Category.assoc a.hom.hom.left c.hom.hom.left prod.snd

/-- Character restriction commutes with the original native pullback-composition comparison. -/
theorem restrictCharacter_baseChange (i : Base K ⟶ Base k) :
    let H : Grp (FScheme K) := (Over.pullback i).mapGrp.obj G
    ∀ {U V : FScheme K} (h : V ⟶ U)
      (c : (Over.pullback U.hom).mapGrp.obj H ⟶ MultiplicativeGroup.groupScheme U.left),
      (BaseChange.groupSchemeBaseChangeComp V.hom i).hom.app G ≫
          restrictCharacter (k := K) H h c =
        restrictCharacter (k := k) G ((Over.map i).map h)
          ((BaseChange.groupSchemeBaseChangeComp U.hom i).hom.app G ≫ c) := by
  intro H U V h c
  let a := (BaseChange.groupSchemeBaseChangeComp V.hom i).hom.app G
  let b := (BaseChange.groupSchemeBaseChangeComp U.hom i).hom.app G
  let v := groupPullbackBaseMap (k := k) G ((Over.map i).map h)
  have hLC := gm_comp_coordinates a (restrictCharacter (k := K) H h c)
  have hL := congrArg (fun q => a.hom.hom.left ≫ q)
    (restrictCharacter_coordinates (k := K) H h c)
  have hSquare := baseChangeComp_baseMap K G i h
  have hS0 := congrArg (fun q => q ≫ c.hom.hom.left ≫ prod.snd) hSquare
  have hSA := (Category.assoc a.hom.hom.left (groupPullbackBaseMap (k := K) H h)
    (c.hom.hom.left ≫ prod.snd)).symm
  have hSB := Category.assoc v b.hom.hom.left (c.hom.hom.left ≫ prod.snd)
  have hS := hSA.trans (hS0.trans hSB)
  have hR := restrictCharacter_coordinates (k := k) G ((Over.map i).map h) (b ≫ c)
  have hRC := congrArg (fun q => v ≫ q) (gm_comp_coordinates b c)
  have hRF := hR.trans hRC
  have hLF := hLC.trans hL
  have hFinal := hLF.trans (hS.trans hRF.symm)
  have hMaps := gm_groupMap_ext
    (f := a ≫ restrictCharacter (k := K) H h c)
    (g := restrictCharacter (k := k) G ((Over.map i).map h) (b ≫ c)) hFinal
  dsimp only [a, b, v] at hMaps
  exact hMaps

variable [IsFinite G.X.hom] [IsCommMonObj G.X]

/-- The original base-change point-to-character equivalence is natural in the actual tests. -/
theorem characterEquivBaseChange_naturality_actual (i : Base K ⟶ Base k)
    {U V : FScheme K} (h : V ⟶ U)
    (p : U ⟶ ((Over.pullback (i)).mapGrp.obj (dualGroup G)).X) :
    characterEquivBaseChange G (Over.mk (i)) V (h ≫ p) =
      restrictCharacter (k := K) ((Over.pullback (i)).mapGrp.obj G) h
        (characterEquivBaseChange G (Over.mk (i)) U p) := by
  have hn := characterEquivBaseChange_naturality G (Over.mk (i)) h p
  have hc := restrictCharacter_baseChange K G i h
    (characterEquivBaseChange G (Over.mk (i)) U p)
  dsimp only [Over.mk_left, Over.mk_hom] at hn hc
  apply (cancel_epi ((BaseChange.groupSchemeBaseChangeComp V.hom i).hom.app G)).mp
  exact hn.trans hc.symm

/-- The same native pulled-back dual represents the actual character functor of the pulled group. -/
def characterRepresentableByBaseChange (i : Base K ⟶ Base k) :
    (characterFunctor (k := K) ((Over.pullback (i)).mapGrp.obj G)).RepresentableBy
      ((Over.pullback (i)).mapGrp.obj (dualGroup G)).X where
  homEquiv {U} := characterEquivBaseChange G (Over.mk (i)) U
  homEquiv_comp {U V} h p := by
    exact characterEquivBaseChange_naturality_actual K G i h p

end AlgebraicGeometry.Scheme.Group.CartierDuality
