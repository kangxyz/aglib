/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.CohomologyTransfers
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.OriginalClassZeroTransport

/-! # Pointed zero transport through original coefficient returns

A stage class returns by the original cohomological pullback and an arbitrary
coefficient morphism, in particular the original direct-image counit after
the smooth ordinary mate. A pointed etale zero chart at the stage pulls back
to a pointed etale zero chart on the original target. The marking scheme is
arbitrary: no finite-presentation hypothesis or replacement geometric point
is needed. This transports an existing stage zero; it does not produce one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u e

attribute [local instance] hasSheafifyLarge HasExt.standard

/-- Zero survives an original coefficient return on any commuting square.
The stage and original classes retain their independent chosen Ext universe;
the two refinement schemes use the standard Ext realization. -/
theorem transfer_zero_of_square
    {Y Yi W Wi : Scheme.{u}}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Yi)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
    (f : Y ⟶ Yi) (w : W ⟶ Y) (wi : Wi ⟶ Yi) (v : W ⟶ Wi)
    (h : v ≫ wi = w ≫ f)
    (F : AbelianSheaf.{u, u + 1} Yi) (G : AbelianSheaf.{u, u + 1} Y)
    (φ : (inverseImage f).obj F ⟶ G) (q : ℕ) (c : Sheaf.H.{e} F q)
    (hc : cohomologyPullback.{u, e, u + 2} wi F q c = 0) :
    cohomologyPullback.{u, e, u + 2} w G q (cohomologyTransfer f φ q c) = 0 := by
  have hz := TwoFieldEffacement.original_class_zero_of_map_law v wi (w ≫ f)
    h F q c hc
  have hp := cohomologyPullback_comp.{u, e, e, u + 2} f w F q c
  rw [hz, map_zero] at hp
  change cohomologyPullback w G q (Sheaf.H.map φ q (cohomologyPullback f F q c)) = 0
  rw [cohomologyPullback_coefficientMap, ← hp, map_zero]

/-- Pull a stage target chart back to the original target, retaining the exact
mark and zero of the class returned by the original coefficient map. Only the
commuting family square is required; no second geometric limit is selected. -/
theorem exists_pointed_etale_zero_of_stage_transfer
    {X Xi Y Yi P : Scheme.{u}}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Yi)]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
    (p : X ⟶ Xi) (a : Y ⟶ X) (ai : Yi ⟶ Xi) (f : Y ⟶ Yi)
    (h : a ≫ p = f ≫ ai)
    (F : AbelianSheaf.{u, u + 1} Yi) (G : AbelianSheaf.{u, u + 1} Y)
    (φ : (inverseImage f).obj F ⟶ G) (q : ℕ) (c : Sheaf.H.{e} F q)
    (x : P ⟶ X) (U : Xi.Etale) (xi : P ⟶ U.left)
    (hx : xi ≫ U.hom = x ≫ p)
    (hc : cohomologyPullback.{u, e, u + 2} (pullback.snd U.hom ai) F q c = 0) :
    ∃ (V : X.Etale) (xV : P ⟶ V.left), xV ≫ V.hom = x ∧
      cohomologyPullback.{u, e, u + 2} (pullback.snd V.hom a) G q
        (cohomologyTransfer f φ q c) = 0 := by
  let V : X.Etale := Etale.mk (pullback.snd U.hom p)
  let xV : P ⟶ V.left := pullback.lift xi x hx
  let v : pullback V.hom a ⟶ pullback U.hom ai :=
    pullback.lift
      (pullback.fst V.hom a ≫ pullback.fst U.hom p)
      (pullback.snd V.hom a ≫ f) (by
        calc
          (pullback.fst V.hom a ≫ pullback.fst U.hom p) ≫ U.hom =
              pullback.fst V.hom a ≫ (pullback.fst U.hom p ≫ U.hom) :=
            Category.assoc _ _ _
          _ = pullback.fst V.hom a ≫ (pullback.snd U.hom p ≫ p) :=
            congrArg (fun k => pullback.fst V.hom a ≫ k) (pullback.condition ..)
          _ = (pullback.fst V.hom a ≫ V.hom) ≫ p :=
            (Category.assoc _ _ _).symm
          _ = (pullback.snd V.hom a ≫ a) ≫ p :=
            congrArg (fun k => k ≫ p) (pullback.condition ..)
          _ = pullback.snd V.hom a ≫ (a ≫ p) := Category.assoc _ _ _
          _ = pullback.snd V.hom a ≫ (f ≫ ai) :=
            congrArg (fun k => pullback.snd V.hom a ≫ k) h
          _ = (pullback.snd V.hom a ≫ f) ≫ ai := (Category.assoc _ _ _).symm)
  refine ⟨V, xV, pullback.lift_snd .., ?_⟩
  exact transfer_zero_of_square f (pullback.snd V.hom a) (pullback.snd U.hom ai)
    v (pullback.lift_snd ..) F G φ q c hc

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
