/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.InternalExtSource
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.CompactSupportPairing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.LocallyConstantExt
public import Aglib.AlgebraicGeometry.EtaleCohomology.Duality.TracePairing
public import Aglib.Algebra.Homology.DerivedCategory.Ext.PairingZero

/-!
# Canonical ordinary-cohomology evaluation through original Yoneda action

The whole biadditive action is the original compact-support Yoneda action with
its second variable precomposed by the independent derived-unit map rho. It is
defined before finite local constancy, any inverse comparison, or perfectness.
The underived evaluation is Hom-first, while Yoneda composition is F-first;
no comparison with a separately ordered Cech product or its signs is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.TorsionZMod.Ringed

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u eM eX eA eC

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

section OriginalAction

variable {A A' E H O E' H' O' : Type*}
  [AddCommGroup A] [AddCommGroup A'] [AddCommGroup E] [AddCommGroup H] [AddCommGroup O]
  [AddCommGroup E'] [AddCommGroup H'] [AddCommGroup O']

private theorem originalAction_value (P : A →+ E →+ O) (rho : H →+ E)
    (B : A →+ H →+ O) (hB : B = P.compl₂ rho)
    (V : A → E → O) (hV : ∀ c e, P c e = V c e) (c : A) (a : H) :
    B c a = V c (rho a) := by
  rw [hB]
  exact hV c (rho a)

private theorem originalAction_comparison (e : E ≃+ H) (rho : H →+ E)
    (hrho : rho = e.symm.toAddMonoidHom)
    (P : A →+ E →+ O) (B : A →+ H →+ O) (hB : B = P.compl₂ rho) :
    B.compl₂ e.toAddMonoidHom = P := by
  rw [hB, hrho]
  ext c x
  exact congrArg (P c) (e.symm_apply_apply x)

private theorem originalAction_comparison_value (e : E ≃+ H) (rho : H →+ E)
    (hrho : rho = e.symm.toAddMonoidHom)
    (P : A →+ E →+ O) (B : A →+ H →+ O) (hB : B = P.compl₂ rho)
    (c : A) (x : E) (y : O) (hy : P c x = y) : B c (e x) = y := by
  have h := congrArg (fun T : A →+ E →+ O => T c x)
    (originalAction_comparison e rho hrho P B hB)
  exact h.trans hy

/-- Whole original two-slot action comparison before native coefficient evaluation. -/
theorem originalAction_target {rho : H →+ E} {rho' : H' →+ E'}
    {f : E → E'} {g : H →+ H'} (hrho : ∀ a, rho' (g a) = f (rho a))
    (P : A →+ E →+ O) (P' : A →+ E' →+ O') (v : O →+ O')
    (B : A →+ H →+ O) (B' : A →+ H' →+ O')
    (hB : B = P.compl₂ rho) (hB' : B' = P'.compl₂ rho')
    (hP : ∀ c e, P' c (f e) = v (P c e)) : B'.compl₂ g = B.compr₂ v := by
  rw [hB, hB']
  ext c a
  change P' c (rho' (g a)) = v (P c (rho a))
  rw [hrho, hP]

/-- Whole original two-slot action comparison before native coefficient evaluation. -/
theorem originalAction_source {rho : H →+ E} {rho' : H' →+ E'}
    {g : H' →+ H} {u : E' →+ E} (hrho : rho.comp g = u.comp rho')
    (P : A →+ E →+ O) (P' : A' →+ E' →+ O) (f : A →+ A')
    (B : A →+ H →+ O) (B' : A' →+ H' →+ O)
    (hB : B = P.compl₂ rho) (hB' : B' = P'.compl₂ rho')
    (hP : ∀ c e, P' (f c) e = P c (u e)) : B'.comp f = B.compl₂ g := by
  rw [hB, hB']
  ext c a
  change P' (f c) (rho' a) = P c (rho (g a))
  rw [hP]
  exact congrArg (P c) (congrArg (fun r : H' →+ E => r a) hrho).symm

end OriginalAction

attribute [local instance] hasSheafifyRingStandard hasSheafifyAbStandard
  ringWEqualsLocallyBijectiveStandard abWEqualsLocallyBijectiveStandard
  hasSheafifyLarge hasSheafifyModules abelianSheafEnoughInjectivesLarge

local instance internalHomPairing_enoughInjectives (Y : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] :
    EnoughInjectives (SheafOfModulesOfCommRing.{u + 1, u + 1, u}
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf Y.smallEtaleTopology A)) :=
  SheafOfModules.enoughInjectivesLarge.{u + 1, u, 0}
    ((sheafCompose Y.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (ModuleCat.Sheaf.ConstantRing.commutativeSheaf Y.smallEtaleTopology A))

set_option backward.isDefEq.respectTransparency false in
local instance internalHomPairing_genericEnoughInjectives (Y : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] :
    EnoughInjectives (ModuleCat.Sheaf.ConstantRing.ModuleSheaf.{u + 1, u, u + 1, u + 1}
      Y.smallEtaleTopology A) :=
  inferInstanceAs (EnoughInjectives (SheafOfModulesOfCommRing.{u + 1, u + 1, u}
    (ModuleCat.Sheaf.ConstantRing.commutativeSheaf Y.smallEtaleTopology A)))

set_option backward.isDefEq.respectTransparency false in
local instance internalHomPairing_homFunctor_additive (Y : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] (F : ModuleSheaf Y A) :
    (SheafOfModules.InternalHom.homFunctor.{u + 1, u, 0}
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf Y.smallEtaleTopology A) F).Additive :=
  SheafOfModules.InternalHom.homFunctor_additive.{u + 1, u, 0}
    (ModuleCat.Sheaf.ConstantRing.commutativeSheaf Y.smallEtaleTopology A) F

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (Λ : Type (u + 1)) [CommRing Λ]
  [HasExt.{eM} (ModuleSheaf U Λ)] [HasExt.{eX} (ModuleSheaf X Λ)]
  [HasExt.{eA} (AbelianSheaf.{u, u + 1} U)]
  [HasExt.{eC} (AbelianSheaf.{u, u + 1} X)]

set_option backward.isDefEq.respectTransparency false in
local instance internalHomPairing_nativeHasExt :
    HasExt.{eM} (SheafOfModulesOfCommRing.{u + 1, u + 1, u}
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ)) :=
  inferInstanceAs (HasExt.{eM} (ModuleSheaf U Λ))

omit [HasExt.{eA} (AbelianSheaf.{u, u + 1} U)] in
/-- The original compact-support action commutes with target coefficient maps. -/
theorem originalCompactAction_target (F N N' : ModuleSheaf U Λ) (b : N ⟶ N')
    (r s t : ℕ) (h : r + s = t)
    (c : CompactSupport.H.{eC} j ((SheafOfModules.toSheaf (constantRing U Λ)).obj F) r)
    (e : Ext.{eM} F N s) :
    compactSupportPairingHom.{eM, eX, eC} j Λ F N' r s t h c
        (e.comp (Ext.mk₀ b) (add_zero s)) =
      CompactSupport.H.map.{eC} j ((SheafOfModules.toSheaf (constantRing U Λ)).map b) t
        (compactSupportPairingHom.{eM, eX, eC} j Λ F N r s t h c e) := by
  exact (compactSupportPairingHom_apply_apply.{eM, eX, eC} j Λ F N' r s t h c
      (e.comp (Ext.mk₀ b) (add_zero s))).trans
    ((compactSupportPairing_comp_mk₀ b c e h).trans
      (congrArg (CompactSupport.H.map.{eC} j
        ((SheafOfModules.toSheaf (constantRing U Λ)).map b) t)
        (compactSupportPairingHom_apply_apply.{eM, eX, eC} j Λ F N r s t h c e)).symm)

omit [HasExt.{eA} (AbelianSheaf.{u, u + 1} U)] in
/-- The original compact-support action commutes with source coefficient maps. -/
theorem originalCompactAction_source (F F' N : ModuleSheaf U Λ) (a : F ⟶ F')
    (r s t : ℕ) (h : r + s = t)
    (c : CompactSupport.H.{eC} j ((SheafOfModules.toSheaf (constantRing U Λ)).obj F) r)
    (e : Ext.{eM} F' N s) :
    compactSupportPairingHom.{eM, eX, eC} j Λ F' N r s t h
        (CompactSupport.H.map.{eC} j ((SheafOfModules.toSheaf (constantRing U Λ)).map a) r c) e =
      compactSupportPairingHom.{eM, eX, eC} j Λ F N r s t h c
        (((Ext.mk₀ a).precomp N (zero_add s)) e) := by
  have hPre : ((Ext.mk₀ a).precomp N (zero_add s)) e =
      (Ext.mk₀ a).comp e (zero_add s) :=
    Ext.bilinearComp_apply_apply F F' N 0 s s (zero_add s) (Ext.mk₀ a) e
  exact (compactSupportPairingHom_apply_apply.{eM, eX, eC} j Λ F' N r s t h
      (CompactSupport.H.map.{eC} j ((SheafOfModules.toSheaf (constantRing U Λ)).map a) r c)
      e).trans
    ((compactSupportPairing_naturality a c e h).trans
      ((congrArg (fun z => compactSupportPairing.{eM, eX} j Λ c z h) hPre).symm.trans
        (compactSupportPairingHom_apply_apply.{eM, eX, eC} j Λ F N r s t h c
          (((Ext.mk₀ a).precomp N (zero_add s)) e)).symm))

/-- Canonical ordinary-H evaluation is original Yoneda action after the independent rho.
Its definition has no local-constancy, target-acyclicity or perfectness hypothesis. -/
def internalHomEvaluationPairingHom (F N : ModuleSheaf U Λ)
    (r s t : ℕ) (h : r + s = t) :=
  (compactSupportPairingHom.{eM, eX, eC} j Λ F N r s t h).compl₂
    (Sheaf.InternalExt.cohomologyExtReverse.{u + 1, u, eM, eA}
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ)
      terminalIsTerminal F N s)

/-- The actual value uses the original Yoneda action after the independent rho. -/
theorem internalHomEvaluationPairingHom_apply_apply (F N : ModuleSheaf U Λ)
    (r s t : ℕ) (h : r + s = t)
    (c a) :
    internalHomEvaluationPairingHom.{u, eM, eX, eA, eC} j Λ F N r s t h c a =
      compactSupportPairing.{eM, eX} j Λ c
        (Sheaf.InternalExt.cohomologyExtReverse.{u + 1, u, eM, eA}
          (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ)
          terminalIsTerminal F N s a) h := by
  exact originalAction_value
    (compactSupportPairingHom.{eM, eX, eC} j Λ F N r s t h)
    (Sheaf.InternalExt.cohomologyExtReverse.{u + 1, u, eM, eA}
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ)
      terminalIsTerminal F N s)
    (internalHomEvaluationPairingHom.{u, eM, eX, eA, eC} j Λ F N r s t h) rfl
    (fun x e => compactSupportPairing.{eM, eX} j Λ x e h)
    (compactSupportPairingHom_apply_apply.{eM, eX, eC} j Λ F N r s t h) c a

/-- At an actually acyclic target, the full second-slot comparison is the unchanged
original compact-support pairing. This precedes degree and trace specializations. -/
theorem internalHomEvaluationPairingHom_comparison (F N : ModuleSheaf U Λ)
    (hN : ∀ q : ℕ, IsZero (((SheafOfModules.InternalHom.homFunctor.{u + 1, u, 0}
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ) F).rightDerived (q
        + 1)).obj N))
    (r s t : ℕ) (h : r + s = t) :
    (internalHomEvaluationPairingHom.{u, eM, eX, eA, eC} j Λ F N r s t h).compl₂
        (Sheaf.InternalExt.extCohomologyAddEquivOfAcyclic.{u + 1, u, eM, eA}
          (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ)
          terminalIsTerminal F N hN s).toAddMonoidHom =
      compactSupportPairingHom.{eM, eX, eC} j Λ F N r s t h := by
  have hInverse := Sheaf.InternalExt.cohomologyExtReverse_eq_symm.{u + 1, u, eM, eA}
    (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ) terminalIsTerminal F
      N hN s
  have hApply := originalAction_comparison (A := (CompactSupport.H.{eC} j
    ((SheafOfModules.toSheaf (constantRing U Λ)).obj F) r)) (O := (CompactSupport.H.{eC} j
    ((SheafOfModules.toSheaf (constantRing U Λ)).obj N) t))
    (Sheaf.InternalExt.extCohomologyAddEquivOfAcyclic.{u + 1, u, eM, eA}
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ) terminalIsTerminal
        F N hN s) (Sheaf.InternalExt.cohomologyExtReverse.{u + 1, u, eM, eA}
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ) terminalIsTerminal
        F N s) hInverse
  let pOld := (compactSupportPairingHom.{eM, eX, eC} j Λ F N r s t h)
  let bOld := (internalHomEvaluationPairingHom.{u, eM, eX, eA, eC} j Λ F N r s t h)
  dsimp only [SheafOfModulesOfCommRing, Coefficients.ModuleSheaf,
    ModuleCat.Sheaf.ConstantRing.ModuleSheaf, Coefficients.constantRing] at hApply pOld bOld
  simp only [ModuleCat.Sheaf.ConstantRing.commutativeSheaf_forget] at hApply pOld bOld
  have hOriginal := hApply pOld bOld rfl
  exact hOriginal

omit [HasExt.{eA} (AbelianSheaf.{u, u + 1} U)] in
/-- Original coefficient postcomposition is the degree-zero Yoneda action in every r. -/
theorem compactSupportPairing_mk₀_right {F N : ModuleSheaf U Λ} (f : F ⟶ N) (r : ℕ)
    (c : CompactSupport.H.{eC} j ((SheafOfModules.toSheaf (constantRing U Λ)).obj F) r) :
    compactSupportPairing.{eM, eX} j Λ c (Ext.mk₀.{eM} f) (add_zero r) =
      CompactSupport.H.map.{eC} j ((SheafOfModules.toSheaf (constantRing U Λ)).map f) r c := by
  obtain ⟨x, rfl⟩ := (moduleLowerShriekCohomologyAddEquiv.{eX, eC} j Λ F r).surjective c
  rw [compactSupportPairing_moduleLowerShriekCohomologyAddEquiv,
    moduleLowerShriekPairing, Functor.extPairing_mk₀_right,
    moduleLowerShriekCohomologyAddEquiv_naturality, CompactSupport.H.map_apply]

/-- At s=0 the actual Hom coefficient acts by its original compact-support map. -/
theorem internalHomEvaluationPairingHom_mk₀ {F N : ModuleSheaf U Λ}
    (hN : ∀ q : ℕ, IsZero (((SheafOfModules.InternalHom.homFunctor.{u + 1, u, 0}
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ) F).rightDerived (q
        + 1)).obj N))
    (f : F ⟶ N) (r : ℕ)
    (c : CompactSupport.H.{eC} j ((SheafOfModules.toSheaf (constantRing U Λ)).obj F) r) :
    internalHomEvaluationPairingHom.{u, eM, eX, eA, eC} j Λ F N r 0 r (add_zero r) c
        (SheafOfModules.InternalHom.extZeroCohomologyAddEquiv
          (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ)
          terminalIsTerminal F N (Ext.mk₀.{eM} f)) =
      CompactSupport.H.map.{eC} j ((SheafOfModules.toSheaf (constantRing U Λ)).map f) r c := by
  have hZero := Sheaf.InternalExt.cohomologyExtReverse_zero_of_acyclic.{u + 1, u, eM, eA}
    (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ) terminalIsTerminal F N hN
  have hOriginal := originalAction_comparison_value
    (SheafOfModules.InternalHom.extZeroCohomologyAddEquiv.{u + 1, u, eM, eA}
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ) terminalIsTerminal
        F N) (Sheaf.InternalExt.cohomologyExtReverse.{u + 1, u, eM, eA}
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ) terminalIsTerminal
        F N 0) hZero
    (compactSupportPairingHom.{eM, eX, eC} j Λ F N r 0 r (add_zero r))
      (internalHomEvaluationPairingHom.{u, eM, eX, eA, eC} j Λ F N r 0 r (add_zero r)) rfl
    c (Ext.mk₀.{eM} f)
    (CompactSupport.H.map.{eC} j ((SheafOfModules.toSheaf (constantRing U Λ)).map f) r c)
    (compactSupportPairing_mk₀_right j Λ f r c)
  exact hOriginal

/-- The original identity coefficient acts as the identity in every compact-support degree. -/
theorem internalHomEvaluationPairingHom_id (F : ModuleSheaf U Λ)
    (hF : ∀ q : ℕ, IsZero (((SheafOfModules.InternalHom.homFunctor.{u + 1, u, 0}
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ) F).rightDerived (q
        + 1)).obj F)) (r : ℕ) :
    (internalHomEvaluationPairingHom.{u, eM, eX, eA, eC} j Λ F F r 0 r (add_zero r)).flip
        (SheafOfModules.InternalHom.extZeroCohomologyAddEquiv
          (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ)
          terminalIsTerminal F F (Ext.mk₀.{eM} (𝟙 F))) = AddMonoidHom.id _ := by
  ext c
  rw [AddMonoidHom.flip_apply, internalHomEvaluationPairingHom_mk₀ j Λ hF,
    CategoryTheory.Functor.map_id, CompactSupport.H.map_id_apply]
  rfl

/-- Target coefficient naturality uses the original H-map on internal Hom and the
original compact-support coefficient map. Actual target acyclicity remains explicit. -/
theorem internalHomEvaluationPairingHom_naturality_target (F : ModuleSheaf U Λ)
    {N N' : ModuleSheaf U Λ} (b : N ⟶ N')
    (hN : ∀ q : ℕ, IsZero (((SheafOfModules.InternalHom.homFunctor.{u + 1, u, 0}
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ) F).rightDerived (q
        + 1)).obj N))
    (hN' : ∀ q : ℕ, IsZero (((SheafOfModules.InternalHom.homFunctor.{u + 1, u, 0}
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ) F).rightDerived (q
        + 1)).obj N'))
    (r s t : ℕ) (h : r + s = t) :
    (internalHomEvaluationPairingHom.{u, eM, eX, eA, eC} j Λ F N' r s t h).compl₂
        (Sheaf.H.map.{eA} ((SheafOfModules.toSheaf
          ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ))).map
          (SheafOfModules.InternalHom.map.{u + 1, u, u + 1, u + 1}
            (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ)
            (𝟙 F) b)) s) =
      (internalHomEvaluationPairingHom.{u, eM, eX, eA, eC} j Λ F N r s t h).compr₂
        (CompactSupport.H.map.{eC} j ((SheafOfModules.toSheaf (constantRing U Λ)).map b) t) := by
  have hCoefficient := Sheaf.InternalExt.cohomologyExtReverse_naturality_of_acyclic.{u + 1, u,
    eM, eA} (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ)
    terminalIsTerminal F b hN hN' s
  have hApply := originalAction_target (A := (CompactSupport.H.{eC} j
    ((SheafOfModules.toSheaf (constantRing U Λ)).obj F) r))
    (O := (CompactSupport.H.{eC} j ((SheafOfModules.toSheaf (constantRing U Λ)).obj N) t))
    (O' := (CompactSupport.H.{eC} j ((SheafOfModules.toSheaf (constantRing U Λ)).obj N') t))
    (rho := Sheaf.InternalExt.cohomologyExtReverse.{u + 1, u, eM, eA}
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ)
      terminalIsTerminal F N s)
    (rho' := Sheaf.InternalExt.cohomologyExtReverse.{u + 1, u, eM, eA}
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ)
      terminalIsTerminal F N' s)
    (f := fun e : Ext.{eM} F N s => e.comp (Ext.mk₀.{eM} b) (add_zero s))
    hCoefficient
  let pOld := (compactSupportPairingHom.{eM, eX, eC} j Λ F N r s t h)
  let pOld' := (compactSupportPairingHom.{eM, eX, eC} j Λ F N' r s t h)
  let bOld := (internalHomEvaluationPairingHom.{u, eM, eX, eA, eC} j Λ F N r s t h)
  let bOld' := (internalHomEvaluationPairingHom.{u, eM, eX, eA, eC} j Λ F N' r s t h)
  have hCoefficientFamily := hApply
  have hFirst := hCoefficientFamily pOld
  have hSecond := hFirst pOld'
  have hOutput := hSecond
    (CompactSupport.H.map.{eC} j ((SheafOfModules.toSheaf (constantRing U Λ)).map b) t)
  have hActions := hOutput bOld bOld'
  have hValues := hActions rfl rfl
  have hOriginal := hValues (originalCompactAction_target j Λ F N N' b r s t h)
  exact hOriginal

/-- The whole ordinary-H action commutes with the original source coefficient map.
The independent rho source square is used before applying original Yoneda naturality. -/
theorem internalHomEvaluationPairingHom_naturality_source
    {F F' : ModuleSheaf U Λ} (a : F ⟶ F') (N : ModuleSheaf U Λ)
    (r s t : ℕ) (h : r + s = t) :
    (internalHomEvaluationPairingHom.{u, eM, eX, eA, eC} j Λ F' N r s t h).comp
        (CompactSupport.H.map.{eC} j ((SheafOfModules.toSheaf (constantRing U Λ)).map a) r) =
      (internalHomEvaluationPairingHom.{u, eM, eX, eA, eC} j Λ F N r s t h).compl₂
        (Sheaf.H.map.{eA} ((SheafOfModules.toSheaf
          ((sheafCompose U.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ))).map
          (SheafOfModules.InternalHom.map.{u + 1, u, u + 1, u + 1}
            (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ)
            a (𝟙 N))) s) := by
  have hSource := Sheaf.InternalExt.cohomologyExtReverse_precompose.{u + 1, u, eM, eA}
    (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ) terminalIsTerminal a N s
  have hApply := originalAction_source (A := (CompactSupport.H.{eC} j ((SheafOfModules.toSheaf
    (constantRing U Λ)).obj F) r)) (A' := (CompactSupport.H.{eC} j ((SheafOfModules.toSheaf
    (constantRing U Λ)).obj F') r))
    (O := (CompactSupport.H.{eC} j ((SheafOfModules.toSheaf (constantRing U Λ)).obj N) t))
    hSource
  let pOld := (compactSupportPairingHom.{eM, eX, eC} j Λ F N r s t h)
  let pOld' := (compactSupportPairingHom.{eM, eX, eC} j Λ F' N r s t h)
  let bOld := (internalHomEvaluationPairingHom.{u, eM, eX, eA, eC} j Λ F N r s t h)
  let bOld' := (internalHomEvaluationPairingHom.{u, eM, eX, eA, eC} j Λ F' N r s t h)
  have hFirst := hApply pOld
  have hSecond := hFirst pOld'
  have hInput := hSecond
    (CompactSupport.H.map.{eC} j ((SheafOfModules.toSheaf (constantRing U Λ)).map a) r)
  have hActions := hInput bOld bOld'
  have hValues := hActions rfl rfl
  have hOriginal := hValues (originalCompactAction_source j Λ F F' N a r s t h)
  exact hOriginal

/-- The degree-zero class of an original lifted-unit section acts by its original
uncurried coefficient arrow. Pure-section evaluation is the original counit law. -/
theorem internalHomEvaluationPairingHom_liftedUnitSection {F N : ModuleSheaf U Λ}
    (hN : ∀ q : ℕ, IsZero (((SheafOfModules.InternalHom.homFunctor.{u + 1, u, 0}
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ) F).rightDerived (q
        + 1)).obj N))
    (f : moduleUnit U Λ ⟶ SheafOfModules.InternalHom.sheaf
      (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ) F N)
    (r : ℕ)
    (c : CompactSupport.H.{eC} j ((SheafOfModules.toSheaf (constantRing U Λ)).obj F) r) :
    internalHomEvaluationPairingHom.{u, eM, eX, eA, eC} j Λ F N r 0 r (add_zero r) c
        (Sheaf.ModuleCoefficients.cohomologyMap.{u + 1, u, u + 1, u + 1, eM, eA}
          terminalIsTerminal
          ((sheafCompose U.smallEtaleTopology
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ))
          (SheafOfModules.InternalHom.sheaf
            (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ) F N)
          0 (Ext.mk₀.{eM} f)) =
      CompactSupport.H.map.{eC} j ((SheafOfModules.toSheaf (constantRing U Λ)).map
        ((SheafOfModules.InternalHom.liftedUnitCoyonedaIso.{u + 1, u, 0}
          (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ) F).hom.app N f))
        r c := by
  let R := ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ
  let e := ((SheafOfModules.InternalHom.liftedUnitCoyonedaIso.{u + 1, u, 0} R F).app
    N).addCommGroupIsoToAddEquiv
  let b := e f
  have hInv := e.symm_apply_apply f
  have hZero := SheafOfModules.InternalHom.extZeroCohomologyAddEquiv_mk₀.{u + 1, u, eM, eA}
    R terminalIsTerminal F N b
  have hInput := hZero.trans (congrArg (fun z =>
    Sheaf.ModuleCoefficients.cohomologyMap.{u + 1, u, u + 1, u + 1, eM, eA}
      terminalIsTerminal
      ((sheafCompose U.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
      (SheafOfModules.InternalHom.sheaf R F N) 0 (Ext.mk₀.{eM} z)) hInv)
  have hAction := congrArg (fun z =>
    internalHomEvaluationPairingHom.{u, eM, eX, eA, eC} j Λ F N r 0 r (add_zero r) c z) hInput
  have hNative := internalHomEvaluationPairingHom_mk₀.{u, eM, eX, eA, eC} j Λ hN b r c
  run_tac Lean.Elab.Tactic.withMainContext do
    let mut action : Option Lean.Expr := none
    let mut native : Option Lean.Expr := none
    let mut ring : Option (Lean.Expr × Lean.Expr) := none
    for decl in ← Lean.getLCtx do
      let name := decl.userName.eraseMacroScopes.toString
      if name == "hAction" || name == "hNative" then
        let actualType ← Lean.instantiateMVars decl.type
        let actualType ← Lean.Meta.whnf actualType
        let args := actualType.getAppArgs
        unless args.size == 3 do
          throwError "W4 diagnostic: equality does not have three arguments"
        Lean.logInfo m!"W4.actual.{name}: typeHead={actualType.getAppFn}, lhsHead={args[1]!.getAppFn}"
        if name == "hAction" then action := some args[1]!
        else native := some args[1]!
      if name == "R" then
        if let some value := decl.value? then
          let value ← Lean.instantiateMVars value
          ring := some (decl.toExpr, value)
    let some actionValue := action | throwError "W4 diagnostic: hAction missing"
    let some nativeValue := native | throwError "W4 diagnostic: hNative missing"
    let mut cases := [("raw", actionValue, nativeValue)]
    if let some (ringExpr, value) := ring then
      let normalize := fun e : Lean.Expr => e.replace fun part =>
        if part == ringExpr then some value else none
      cases := cases ++ [("ring", normalize actionValue, normalize nativeValue)]
    for (label, left, right) in cases do
      Lean.logInfo m!"W4.middle.{label}Same={left == right}"
      let mut pending := [("middle", left, right)]
      let mut difference : Option (String × Lean.Expr × Lean.Expr) := none
      for _ in [:4096] do
        if difference.isSome then break
        match pending with
        | [] => break
        | (path, a, b) :: rest =>
          pending := rest
          unless a == b do
            match a, b with
            | .mdata _ inner, _ => pending := (path ++ ".metaL", inner, b) :: pending
            | _, .mdata _ inner => pending := (path ++ ".metaR", a, inner) :: pending
            | .app af aa, .app bf ba =>
              pending := (path ++ ".fn", af, bf) :: (path ++ ".arg", aa, ba) :: pending
            | _, _ => difference := some (path, a, b)
      if let some (path, a, b) := difference then
        Lean.logInfo m!"W4.middle.{label}Path={path}"
        Lean.logInfo m!"W4.middle.{label}Left={reprStr a}"
        Lean.logInfo m!"W4.middle.{label}Right={reprStr b}"
      else unless pending.isEmpty do
        Lean.logError m!"W4 structural diagnostic reached its4096-node reporting bound"
  have hFinal := hAction.symm.trans hNative
  exact hFinal

/-- The native unit-source normalization retains the original all-degree
module-unit Ext/H comparison, before any finite-LCC hypothesis. -/
theorem internalHomUnitCohomologyExtMap_comparison (N : ModuleSheaf U Λ) (q : ℕ) :
    (fun {P : Prop} (_h : P) => P)
      (Sheaf.InternalExt.cohomologyExtReverse_unit.{u + 1, u, eM, eA}
        (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ)
        terminalIsTerminal N q) :=
  Sheaf.InternalExt.cohomologyExtReverse_unit.{u + 1, u, eM, eA}
    (ModuleCat.Sheaf.ConstantRing.commutativeSheaf U.smallEtaleTopology Λ)
    terminalIsTerminal N q

section FiniteLocallyConstant

variable (k : Type u) [Field k] [IsAlgClosed k] (n : ℕ)
  (hn : 0 < n) (hunit : IsUnit (n : k)) (p : U ⟶ Spec (.of k))
  [HasExt.{eM} (ModuleSheaf U (ULift.{u + 1} (ZMod n)))]
  [HasExt.{eX} (ModuleSheaf X (ULift.{u + 1} (ZMod n)))]

/-- At every positive invertible level, the finite-LCC comparison identifies the
whole canonical ordinary-H evaluation with the unchanged native Yoneda action. -/
theorem locallyConstantInternalHomEvaluationPairingHom_comparison
    (F : ModuleSheaf U (ULift.{u + 1} (ZMod n)))
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence U (ULift.{u + 1} (ZMod n))).inverse.obj F))
    (r s t : ℕ) (h : r + s = t) :
    (internalHomEvaluationPairingHom.{u, eM, eX, eA, eC}
      j (ULift.{u + 1} (ZMod n)) F (moduleRootsOfUnity U n) r s t h).compl₂
        (locallyConstantExtCohomologyAddEquiv k n hn hunit p F hF s).toAddMonoidHom =
      compactSupportPairingHom.{eM, eX, eC}
        j (ULift.{u + 1} (ZMod n)) F (moduleRootsOfUnity U n) r s t h :=
  internalHomEvaluationPairingHom_comparison j (ULift.{u + 1} (ZMod n)) F
    (moduleRootsOfUnity U n) (moduleRoots_internalHom_rightDerived_isZero k n hn hunit p F hF)
    r s t h

end FiniteLocallyConstant

section Trace

open Scheme.OverField

variable {k : Type u} [Field k] [IsAlgClosed k] (Y : FScheme k) (hY : Curve.Properties Y)
  (D : Set Y.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set Y.left))
  {V : Scheme.{u}} (i : V ⟶ Y.left) [IsOpenImmersion i] (hD : Set.range i = Dᶜ)
  (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hinv : IsUnit (n : Γ(Y.left, ⊤)))
  [HasExt.{eM} (ModuleSheaf V (ULift.{u + 1} (ZMod n)))]
  [HasExt.{eX} (ModuleSheaf Y.left (ULift.{u + 1} (ZMod n)))]
  [HasExt.{eA} (AbelianSheaf.{u, u + 1} V)]
  [HasExt.{eC} (AbelianSheaf.{u, u + 1} Y.left)]

/-- Ordinary compact-support trace on the original underlying roots module:
the original roots coefficient isomorphism followed by the existing normalized trace. -/
def internalHomOrdinaryTraceHom :
    CompactSupport.H.{eC} i
      ((SheafOfModules.toSheaf (constantRing V (ULift.{u + 1} (ZMod n)))).obj
        (moduleRootsOfUnity V n)) 2 →+ ZMod n :=
  (Curves.compactSupportTraceAddEquiv Y hY D hfin hclosed i hD n hn hunit hinv).toAddMonoidHom.comp
      (CompactSupport.H.map i (moduleRootsOfUnityUnderlyingIso V n).hom 2)

omit [HasExt.{eM} (ModuleSheaf V (ULift.{u + 1} (ZMod n)))]
  [HasExt.{eA} (AbelianSheaf.{u, u + 1} V)] in
/-- The whole ordinary trace retains the unchanged original module trace under alpha. -/
theorem internalHomOrdinaryTraceHom_moduleComparison :
    (internalHomOrdinaryTraceHom Y hY D hfin hclosed i hD n hn hunit hinv).comp
        (moduleLowerShriekCohomologyAddEquiv.{eX, eC} i (ULift.{u + 1} (ZMod n))
          (moduleRootsOfUnity V n) 2).toAddMonoidHom =
      (moduleCompactSupportTraceAddEquiv Y hY D hfin hclosed i hD n hn hunit
        hinv).toAddMonoidHom := by
  rw [moduleCompactSupportTraceAddEquiv_toAddMonoidHom]
  rfl

/-- The canonical ordinary-H evaluation followed by the actual normalized trace.
It is constructed for every F, before a finite-LCC inverse or perfectness is used. -/
def internalHomTracePairingHom (F : ModuleSheaf V (ULift.{u + 1} (ZMod n)))
    (r s : ℕ) (h : r + s = 2) :=
  (internalHomEvaluationPairingHom.{u, eM, eX, eA, eC}
    i (ULift.{u + 1} (ZMod n)) F (moduleRootsOfUnity V n) r s 2 h).compr₂
      (internalHomOrdinaryTraceHom Y hY D hfin hclosed i hD n hn hunit hinv)

/-- The complete ordinary-H traced operator, after its two original comparison maps,
is the unchanged native Yoneda/trace pairing in both slots. -/
theorem internalHomTracePairingHom_comparison
    (F : ModuleSheaf V (ULift.{u + 1} (ZMod n)))
    (hF : Constructible.Modules.IsFiniteTypeLocallyConstant
      ((moduleSheafEquivalence V (ULift.{u + 1} (ZMod n))).inverse.obj F))
    (r s : ℕ) (h : r + s = 2) :
    (fun c =>
      (((internalHomTracePairingHom.{u, eM, eX, eA, eC}
        Y hY D hfin hclosed i hD n hn hunit hinv F r s h).comp
          (moduleLowerShriekCohomologyAddEquiv.{eX, eC}
            i (ULift.{u + 1} (ZMod n)) F r).toAddMonoidHom).compl₂
        (locallyConstantExtCohomologyAddEquiv k n hn hunit (i ≫ Y.hom) F hF s).toAddMonoidHom) c) =
      (fun c =>
        (moduleTracePairingLinearMap Y hY D hfin hclosed i hD n hn hunit hinv F r s h
          c).toAddMonoidHom) := by
  funext c
  apply AddMonoidHom.ext
  intro e
  have hWhole := locallyConstantInternalHomEvaluationPairingHom_comparison
    i k n hn hunit (i ≫ Y.hom) F hF r s 2 h
  have hValue := congrArg (fun T =>
    T (moduleLowerShriekCohomologyAddEquiv.{eX, eC}
      i (ULift.{u + 1} (ZMod n)) F r c) e) hWhole
  have hTrace := congrArg (fun T =>
    T (moduleLowerShriekPairing i (ULift.{u + 1} (ZMod n)) c e h))
    (internalHomOrdinaryTraceHom_moduleComparison Y hY D hfin hclosed i hD n hn hunit hinv)
  have hPairValue := compactSupportPairingHom_apply_apply.{eM, eX, eC}
    i (ULift.{u + 1} (ZMod n)) F (moduleRootsOfUnity V n) r s 2 h
      (moduleLowerShriekCohomologyAddEquiv.{eX, eC}
        i (ULift.{u + 1} (ZMod n)) F r c) e
  have hPairComparison := compactSupportPairing_moduleLowerShriekCohomologyAddEquiv.{eM, eX, eC}
    (j := i) (Λ := ULift.{u + 1} (ZMod n)) c e h
  have hOriginal := hValue.trans (hPairValue.trans hPairComparison)
  have hTraced := congrArg
    (internalHomOrdinaryTraceHom Y hY D hfin hclosed i hD n hn hunit hinv) hOriginal
  have hNative := moduleTracePairingLinearMap_apply_apply Y hY D hfin hclosed i hD n hn hunit
    hinv F r s h c e
  have hFinal := hTraced.trans (hTrace.trans hNative.symm)
  simpa only [internalHomTracePairingHom, AddMonoidHom.comp_apply,
    AddMonoidHom.compl₂_apply, AddMonoidHom.compr₂_apply, AddEquiv.coe_toAddMonoidHom,
    LinearMap.toAddMonoidHom_coe] using hFinal

end Trace

end AlgebraicGeometry.Scheme.EtaleCohomology
