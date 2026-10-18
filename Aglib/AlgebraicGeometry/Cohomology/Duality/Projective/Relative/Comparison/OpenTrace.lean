/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology.Coherence

/-!
# Original relative trace under derived open restriction

The ordinary open equation for the normalized top higher-image trace lifts to
the installed bounded-below derived open comparison. The lift uses the actual
upper bound and the original exact-single and exact-homology comparisons.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules

universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)
  {X Y : Scheme.{u}} (a : X ⟶ ProjectiveSpace R ι) (p : X ⟶ Y)
  (f : Y ⟶ Spec (.of R)) (h : IsPullback a p (toSpec R ι) f)
  [Y.IsSeparated]

/-- Top homology of the original trace through the installed bounded-below inclusion. -/
private theorem tracePlus_homology (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] :
    (DerivedCategory.Plus.homologyFunctor Y.Modules (n : ℤ)).map
        (relativeProjectiveTracePlus R ι a p f h n e N) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso Y.Modules (n : ℤ)).hom.app N =
    ((Scheme.Modules.pushforward p).rightDerivedSingleHomologyIso n).inv.app
      ((relativeTopDifferentialCoefficientsFunctor p n).obj N) ≫
        relativeProjectiveHigherTrace R ι a p f h n e N := by
  change (DerivedCategory.homologyFunctor Y.Modules (n : ℤ)).map
    (DerivedCategory.Plus.ι.map (relativeProjectiveTracePlus R ι a p f h n e N)) ≫ _ = _
  rw [relativeProjectiveTracePlus_ι]
  exact relativeProjectiveTrace_homology R ι a p f h n e N

/-- The original normalized derived trace commutes with every original Cartesian open
restriction, through the native derived base-change and exact-single comparisons. -/
theorem relativeProjectiveTracePlus_open
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {W U : Scheme.{u}}
    (i : W ⟶ X) (q : W ⟶ U) (j : U ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (H : IsPullback i q p j)
    (N : Y.Modules) [N.IsQuasicoherent] :
    letI : U.IsSeparated := ⟨by rw [← terminal.comp_from j]; infer_instance⟩
    (Scheme.Modules.derivedOpenBaseChangeIso i q p j H).hom.app
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
          ((relativeTopDifferentialCoefficientsFunctor p n).obj N)) ≫
      (Scheme.Modules.derivedPushforwardPlus q).map
        (((Scheme.Modules.restrictFunctor i).rightDerivedFunctorPlusSingleIso 0).hom.app
          ((relativeTopDifferentialCoefficientsFunctor p n).obj N)) ≫
      (Scheme.Modules.derivedPushforwardPlus q).map
        ((DerivedCategory.Plus.singleFunctor W.Modules 0).map
          ((relativeTopDifferentialCoefficientsRestrictionIso p i q j H.w n).hom.app N)) ≫
      relativeProjectiveTracePlus R ι (i ≫ a) q (j ≫ f) (H.paste_horiz h) n e (N.restrict j) =
    (Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlus.map
        (relativeProjectiveTracePlus R ι a p f h n e N) ≫
      ((Scheme.Modules.restrictFunctor j).rightDerivedFunctorPlusSingleIso (n : ℤ)).hom.app N := by
  let : U.IsSeparated := ⟨by rw [← terminal.comp_from j]; infer_instance⟩
  let P := Scheme.Modules.pushforward p
  let B := Scheme.Modules.pushforward q
  let J := Scheme.Modules.restrictFunctor j
  let A := Scheme.Modules.restrictFunctor i
  let V := (relativeTopDifferentialCoefficientsFunctor p n).obj N
  let K := P.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj V)
  let : (DerivedCategory.Plus.ι.obj K).IsLE (n : ℤ) :=
    relativeProjectiveDifferentialCoefficientsDerived_isLE R ι a p f h n e N
  let : (DerivedCategory.Plus.ι.obj (J.rightDerivedFunctorPlus.obj K)).IsLE (n : ℤ) := by
    rw [DerivedCategory.isLE_iff]
    intro k hk
    exact (J.map_isZero (DerivedCategory.isZero_of_isLE
      (DerivedCategory.Plus.ι.obj K) n k hk)).of_iso
        ((J.rightDerivedFunctorPlusHomologyIso k).app K)
  apply DerivedCategory.Plus.ι.map_injective
  apply (DerivedCategory.homToSingleAddEquiv
    (DerivedCategory.Plus.ι.obj (J.rightDerivedFunctorPlus.obj K)) (n : ℤ) (N.restrict j)).injective
  simp only [DerivedCategory.homToSingleAddEquiv_apply, Functor.map_comp]
  let HP := DerivedCategory.Plus.homologyFunctor Y.Modules (n : ℤ)
  let HU := DerivedCategory.Plus.homologyFunctor U.Modules (n : ℤ)
  let t := relativeProjectiveTracePlus R ι a p f h n e N
  let t' := relativeProjectiveTracePlus R ι (i ≫ a) q (j ≫ f) (H.paste_horiz h)
    n e (N.restrict j)
  let c := (relativeTopDifferentialCoefficientsRestrictionIso p i q j H.w n).hom.app N
  let b := (Scheme.Modules.derivedOpenBaseChangeIso i q p j H).hom.app
    ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj V)
  let s := B.rightDerivedFunctorPlus.map ((A.rightDerivedFunctorPlusSingleIso 0).hom.app V)
  let v := B.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor W.Modules 0).map c)
  let z := (J.rightDerivedFunctorPlusSingleIso (n : ℤ)).hom.app N
  change HU.map b ≫ HU.map s ≫ HU.map v ≫ HU.map t' ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso U.Modules (n : ℤ)).hom.app
        (N.restrict j) =
    HU.map (J.rightDerivedFunctorPlus.map t) ≫ HU.map z ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso U.Modules (n : ℤ)).hom.app
        (N.restrict j)
  have ht := tracePlus_homology R ι a p f h n e N
  have ht' := tracePlus_homology R ι (i ≫ a) q (j ≫ f)
    (H.paste_horiz h) n e (N.restrict j)
  change HP.map t ≫ _ = _ at ht
  change HU.map t' ≫ _ = _ at ht'
  rw [ht', J.rightDerivedFunctorPlusSingleIso_homology]
  have hv := (B.rightDerivedSingleHomologyIso n).inv.naturality c
  change HU.map v ≫ (B.rightDerivedSingleHomologyIso n).inv.app _ =
    (B.rightDerivedSingleHomologyIso n).inv.app _ ≫ (B.rightDerived n).map c at hv
  erw [← Category.assoc (HU.map v), hv]
  have hn := (J.rightDerivedFunctorPlusHomologyIso (n : ℤ)).hom.naturality t
  change HU.map (J.rightDerivedFunctorPlus.map t) ≫
      (J.rightDerivedFunctorPlusHomologyIso (n : ℤ)).hom.app _ =
    (J.rightDerivedFunctorPlusHomologyIso (n : ℤ)).hom.app K ≫ J.map (HP.map t) at hn
  rw [← Category.assoc (HU.map (J.rightDerivedFunctorPlus.map t)), hn]
  simp only [Category.assoc]
  erw [← J.map_comp, ht]
  let E := J.mapIso ((P.rightDerivedSingleHomologyIso n).app V) ≪≫
    ((J.rightDerivedFunctorPlusHomologyIso (n : ℤ)).app K).symm
  apply (cancel_epi E.hom).mp
  have hbase : E.hom ≫ HU.map b ≫ HU.map s ≫
      (B.rightDerivedSingleHomologyIso n).inv.app (V.restrict i) =
    (Scheme.Modules.higherDirectImageOpenRestrictionIso i q p j H n).hom.app V := by
    simp only [E, b, s, P, B, J, A, HU, K,
      Scheme.Modules.higherDirectImageOpenRestrictionIso,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.comp_obj, Category.id_comp, Category.assoc]
    erw [CategoryTheory.Functor.map_id]
    simp only [Iso.app_inv, Scheme.Modules.restrict, Category.id_comp]
  erw [← Category.assoc E.hom (HU.map b), ← Category.assoc _ (HU.map s),
    ← Category.assoc _ ((B.rightDerivedSingleHomologyIso n).inv.app (V.restrict i)), hbase]
  have hopen := relativeProjectiveHigherTrace_open R ι a p f h n e i q j H N
  erw [hopen]
  dsimp only [E, P, J, V, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app_assoc]

end AlgebraicGeometry.Scheme.Cohomology
