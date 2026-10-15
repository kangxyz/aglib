/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.Geometric

/-! # Whole-space normalization of geometric open cohomology

The native open-free geometric map agrees at the whole space with the
original constant-sheaf geometric map on `Sheaf.H`. The comparison retains
the original represented sections and native adjunction units.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}}

/-- The native whole-space open-free comparison retains the original integer-section map. -/
theorem additiveOpenTopIsoInteger_hom_comp
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (a : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ A) :
    additiveOpenHomEquiv X ⊤ A ((additiveOpenTopIsoInteger X).hom ≫ a) =
      integerSheafHomEquiv A a := by
  rw [additiveOpenHomEquiv_naturality_coefficient]
  change a.hom.app (op ⊤)
    ((additiveOpenHomEquiv X ⊤ _)
      ((additiveOpenHomEquiv X ⊤ _).symm (integerSheafHomEquiv _ (𝟙 _)))) = _
  rw [Equiv.apply_symm_apply, ← integerSheafHomEquiv_comp, Category.id_comp]

/-- The original integer-section equivalence evaluates the original adjoint on its generator. -/
theorem integerSheafHomEquiv_apply
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (a : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ A) :
    integerSheafHomEquiv A a =
      ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
        isTerminalTop).homEquiv _ _ a) (ULift.up (1 : ℤ)) := by
  change (uliftZMultiplesHom (A.obj.obj (op ⊤))).symm
    (((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      isTerminalTop).homEquiv _ _ a).hom) = _
  rw [uliftZMultiplesHom_symm_apply]
  rfl

/-- The actual constant-sheaf pullback comparison has the same represented generator. -/
theorem constantPullbackIso_integerSheafHomEquiv (p : Y ⟶ X) :
    (pushforwardSectionsIso p).hom.app
        ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))
      (integerSheafHomEquiv
        ((zariskiPushforward p).obj
          ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
            (AddCommGrpCat.of (ULift.{u} ℤ))))
        (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} p.base).homEquiv _ _)
          ((constantPullbackIso p).hom.app (AddCommGrpCat.of (ULift.{u} ℤ))))) =
      integerSheafHomEquiv
        ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))) (𝟙 _) := by
  let adjX := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u} isTerminalTop
  let adjY := constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u} isTerminalTop
  let adjP := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} p.base
  let adj := (adjX.comp adjP).ofNatIsoRight (pushforwardSectionsIso p)
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app adj adjY
    (AddCommGrpCat.of (ULift.{u} ℤ))
  change adj.homEquiv _ _ ((constantPullbackIso p).hom.app
    (AddCommGrpCat.of (ULift.{u} ℤ))) = adjY.unit.app _ at h
  rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
  rw [← adjY.homEquiv_id (AddCommGrpCat.of (ULift.{u} ℤ))] at h
  have h' := congrArg (fun k => k (ULift.up (1 : ℤ))) h
  simp only [integerSheafHomEquiv_apply]
  change (pushforwardSectionsIso p).hom.app _
      ((adjX.homEquiv _ _ ((adjP.homEquiv _ _)
        ((constantPullbackIso p).hom.app (AddCommGrpCat.of (ULift.{u} ℤ)))))
          (ULift.up (1 : ℤ))) =
    (adjY.homEquiv _ _ (𝟙 _)) (ULift.up (1 : ℤ)) at h'
  exact h'

/-- At the whole space the original open-free pullback comparison agrees with the
original constant-sheaf pullback comparison. -/
theorem additiveOpenPullbackIso_top_hom (p : Y ⟶ X) :
    (zariskiPullback p).map (additiveOpenTopIsoInteger X).hom ≫
        (constantPullbackIso p).hom.app (AddCommGrpCat.of (ULift.{u} ℤ)) =
      (additiveOpenPullbackIso p).hom.app ⊤ ≫ (additiveOpenTopIsoInteger Y).hom := by
  let CY := (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  apply (TopCat.Sheaf.openFreeAbelianPullbackHomEquiv p.base ⊤ CY).injective
  change TopCat.Sheaf.openFreeAbelianPullbackHomEquiv p.base ⊤ CY
      ((zariskiPullback p).map (additiveOpenTopIsoInteger X).hom ≫
        (constantPullbackIso p).hom.app (AddCommGrpCat.of (ULift.{u} ℤ))) =
    TopCat.Sheaf.openFreeAbelianPullbackHomEquiv p.base ⊤ CY
      ((TopCat.Sheaf.openFreeAbelianPullbackObjIso p.base ⊤).hom ≫
        (additiveOpenTopIsoInteger Y).hom)
  erw [TopCat.Sheaf.openFreeAbelianPullbackHomEquiv_comp p.base ⊤
    (TopCat.Sheaf.openFreeAbelianPullbackObjIso p.base ⊤).hom
    (additiveOpenTopIsoInteger Y).hom]
  rw [TopCat.Sheaf.openFreeAbelianPullbackHomEquiv_hom, Category.id_comp]
  apply (TopCat.Sheaf.openFreeAbelianHomEquiv Y.toTopCat ⊤ CY).injective
  erw [TopCat.Sheaf.openFreeAbelianPullbackHomEquiv_sections p.base ⊤ CY
    ((zariskiPullback p).map (additiveOpenTopIsoInteger X).hom ≫
      (constantPullbackIso p).hom.app (AddCommGrpCat.of (ULift.{u} ℤ)))]
  erw [(TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    p.base).homEquiv_naturality_left]
  change additiveOpenHomEquiv X ⊤ ((zariskiPushforward p).obj CY)
      ((additiveOpenTopIsoInteger X).hom ≫
        ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} p.base).homEquiv _ _)
          ((constantPullbackIso p).hom.app (AddCommGrpCat.of (ULift.{u} ℤ)))) =
    additiveOpenHomEquiv Y ⊤ CY (additiveOpenTopIsoInteger Y).hom
  rw [additiveOpenTopIsoInteger_hom_comp]
  have hy := additiveOpenTopIsoInteger_hom_comp CY (𝟙 CY)
  rw [Category.comp_id] at hy
  rw [hy]
  have hc := constantPullbackIso_integerSheafHomEquiv p
  change CY.obj.map (𝟙 (op ⊤))
      (integerSheafHomEquiv ((zariskiPushforward p).obj CY)
        (((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} p.base).homEquiv _ _)
          ((constantPullbackIso p).hom.app (AddCommGrpCat.of (ULift.{u} ℤ))))) =
    integerSheafHomEquiv CY (𝟙 CY) at hc
  rw [CategoryTheory.Functor.map_id] at hc
  exact hc

/-- The inverse generator comparison retains the same original native pullback maps. -/
theorem additiveOpenPullbackIso_top_inv (p : Y ⟶ X) :
    (additiveOpenTopIsoInteger Y).inv ≫ (additiveOpenPullbackIso p).inv.app ⊤ =
      (constantPullbackIso p).inv.app (AddCommGrpCat.of (ULift.{u} ℤ)) ≫
        (zariskiPullback p).map (additiveOpenTopIsoInteger X).inv := by
  have h : (zariskiPullback p).mapIso (additiveOpenTopIsoInteger X) ≪≫
      (constantPullbackIso p).app (AddCommGrpCat.of (ULift.{u} ℤ)) =
    (additiveOpenPullbackIso p).app ⊤ ≪≫ additiveOpenTopIsoInteger Y := by
    apply Iso.ext
    exact additiveOpenPullbackIso_top_hom p
  exact (congrArg Iso.inv h).symm

/-- The actual geometric open-cohomology map at the whole space is the original
geometric map on the unchanged `Sheaf.H`. -/
theorem sheafHPrimeTopAddEquiv_geometric (p : Y ⟶ X)
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (B : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})
    (a : (zariskiPullback p).obj A ⟶ B) (n : ℕ) (x : Sheaf.H'.{u + 1} A n ⊤) :
    sheafHPrimeTopAddEquiv Y B n ((zariskiCohomologyOpenMap p A B a n).app (op ⊤) x) =
      zariskiCohomologyMap p A B a n (sheafHPrimeTopAddEquiv X A n x) := by
  change Ext.{u + 1} ((additiveOpenFreeFunctor X).obj ⊤) A n at x
  change (Ext.mk₀ (additiveOpenTopIsoInteger Y).inv).comp
      (((Ext.mk₀ ((additiveOpenPullbackIso p).inv.app ⊤)).comp
        (x.mapExactFunctor (zariskiPullback p)) (Nat.zero_add n)).comp
        (Ext.mk₀ a) (Nat.add_zero n)) (Nat.zero_add n) =
    ((Ext.mk₀ ((constantPullbackIso p).inv.app (AddCommGrpCat.of (ULift.{u} ℤ)))).comp
      (((Ext.mk₀ (additiveOpenTopIsoInteger X).inv).comp x (Nat.zero_add n)).mapExactFunctor
        (zariskiPullback p)) (Nat.zero_add n)).comp (Ext.mk₀ a) (Nat.add_zero n)
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc_of_third_deg_zero, ← Ext.comp_assoc_of_second_deg_zero,
    Ext.mk₀_comp_mk₀]
  exact congrArg (fun k => ((Ext.mk₀ k).comp (x.mapExactFunctor (zariskiPullback p))
    (Nat.zero_add n)).comp (Ext.mk₀ a) (Nat.add_zero n)) (additiveOpenPullbackIso_top_inv p)

end AlgebraicGeometry.Scheme.Cohomology
