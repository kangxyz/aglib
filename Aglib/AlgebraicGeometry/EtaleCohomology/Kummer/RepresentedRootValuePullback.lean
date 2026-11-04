/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.BoundaryNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel.CoverSectionPullback
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedMultiplicationBaseChange

/-! The original degree-zero roots pullback of a represented character value. -/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

@[expose] public noncomputable section

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

open Scheme.Group Scheme.Group.BaseChange RepresentedKernel

universe u wX wY

attribute [local instance] hasSheafifyLarge Over.cartesianMonoidalCategory
  groupSchemeBaseChange_isCommMonObj

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) (hn : 0 < n) (hi : IsUnit (n : Γ(X, ⊤)))
  [HasExt.{wX} (AbelianSheaf.{u, u + 1} X)] [HasExt.{wY} (AbelianSheaf.{u, u + 1} Y)]

/-- The actual degree-zero roots pullback retains the original represented point. -/
theorem rootsCohomologyPullback_mk₀_represented
    (s : Over.mk (𝟙 X) ⟶ (MultiplicativeGroup.rootsGroupScheme X n).X) :
    let A := MultiplicativeGroup.rootsGroupScheme X n
    let r := (MultiplicativeBaseChange.rootsBaseChangeIso f n).hom
    rootsCohomologyPullback.{u, wX, wY} f n hn hi 0
        (Ext.mk₀ (representedIntegerSection A s)) =
      Ext.mk₀ (representedIntegerSection (MultiplicativeGroup.rootsGroupScheme Y n)
        ((Scheme.Etale.forget Y).map (siteBaseChangeTerminalIso f).inv ≫
          (Over.pullback f).map s ≫ r.hom.hom)) := by
  intro A r
  let : Etale A.X.hom := RootsFiniteEtale.rootsScheme_etale X n hn hi
  let e := representedSheafBaseChangeIso f A
  let a := representedIntegerSection A s
  let b := (inverseImageIntegerIso f).inv ≫ (inverseImage f).map a
  let j := (Scheme.Etale.forget Y).map (siteBaseChangeTerminalIso f).inv ≫
    (Over.pullback f).map s
  have he : representedCoefficientPullback f A = e.hom :=
    SchemeTorsorBaseChange.representedCoefficientUnit_adjoint f A
  have h₁ : b ≫ e.hom = representedIntegerSection (baseChangedGroup f A) j := by
    rw [← he]
    exact representedIntegerSection_pullback f A s
  have h₂ : (rootsPullbackIso f n hn hi).hom = e.hom ≫ representedSheafMap r := rfl
  have h₃ : b ≫ (rootsPullbackIso f n hn hi).hom =
      representedIntegerSection (MultiplicativeGroup.rootsGroupScheme Y n) (j ≫ r.hom.hom) := by
    let r' := representedSheafMap r
    exact (congrArg (fun q => b ≫ q) h₂).trans
      ((Category.assoc b e.hom r').symm.trans
        ((congrArg (fun q => q ≫ r') h₁).trans (representedIntegerSection_map r j)))
  change Sheaf.H.map (rootsPullbackIso f n hn hi).hom 0
    (cohomologyPullback.{u, wX, wY} f (mu X n) 0 (Ext.mk₀ a)) = _
  have h₀ : cohomologyPullback.{u, wX, wY} f (mu X n) 0 (Ext.mk₀ a) =
      Ext.mk₀ b := h0Pullback_mk₀ f a
  exact (congrArg (Sheaf.H.map (rootsPullbackIso f n hn hi).hom 0) h₀).trans
    ((Ext.mk₀_comp_mk₀ b (rootsPullbackIso f n hn hi).hom).trans
      (congrArg (fun q : constantIntegerSheaf Y ⟶ mu Y n =>
        (Ext.mk₀ q : Sheaf.H.{wY} (mu Y n) 0)) h₃))

/-- The original pullback of a terminal point, expressed by the original adjunction. -/
abbrev terminalPointPullback {M : Over X} (x : Over.mk (𝟙 X) ⟶ M) :=
  let T := Over.mk (𝟙 Y)
  let T' := (Over.map f).obj T
  let d : T' ⟶ Over.mk (𝟙 X) := Over.homMk T'.hom (Category.comp_id T'.hom)
  ((Over.mapPullbackAdj f).homEquiv T M) (d ≫ x)

omit [HasExt.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{wY} (AbelianSheaf.{u, u + 1} Y)] in
/-- The original site terminal comparison gives the same original adjoint point. -/
theorem terminalPointPullback_eq_siteBaseChange {M : Over X}
    (x : Over.mk (𝟙 X) ⟶ M) :
    terminalPointPullback f x =
      (Scheme.Etale.forget Y).map (siteBaseChangeTerminalIso f).inv ≫
        (Over.pullback f).map x := by
  let T := Over.mk (𝟙 Y)
  let T' := (Over.map f).obj T
  let d : T' ⟶ Over.mk (𝟙 X) := Over.homMk T'.hom (Category.comp_id T'.hom)
  let e := (Scheme.Etale.forget Y).map (siteBaseChangeTerminalIso f).inv
  let a := Over.mapPullbackAdj f
  have h : a.homEquiv T (Over.mk (𝟙 X)) d = e := by
    apply (a.homEquiv T (Over.mk (𝟙 X))).symm.injective
    exact Over.mkIdTerminal.hom_ext _ _
  exact (a.homEquiv_naturality_right d x).trans (congrArg (fun r => r ≫ (Over.pullback f).map x) h)

/-- The original degree-zero pullback of a character value is the same
represented value at the original terminal point after base change. -/
theorem rootsCohomologyPullback_characterValue {G : Grp (Over X)} [IsCommMonObj G.X]
    (χ : G ⟶ MultiplicativeGroup.rootsGroupScheme X n)
    (x : Over.mk (𝟙 X) ⟶ G.X) :
    let A := MultiplicativeGroup.rootsGroupScheme X n
    let φ := (Over.pullback f).mapGrp.map χ ≫ (MultiplicativeBaseChange.rootsBaseChangeIso f n).hom
    let a := representedIntegerSection (baseChangedGroup f G) (terminalPointPullback f x)
    rootsCohomologyPullback.{u, wX, wY} f n hn hi 0
        (Ext.mk₀ (representedIntegerSection A (x ≫ χ.hom.hom))) =
      Ext.mk₀ (a ≫ representedSheafMap φ) := by
  intro A φ a
  let F := Over.pullback f
  let e := (Scheme.Etale.forget Y).map (siteBaseChangeTerminalIso f).inv
  let r := (MultiplicativeBaseChange.rootsBaseChangeIso f n).hom
  let z := terminalPointPullback f x
  have h := rootsCohomologyPullback_mk₀_represented f n hn hi (x ≫ χ.hom.hom)
  have hz : z ≫ φ.hom.hom = e ≫ F.map (x ≫ χ.hom.hom) ≫ r.hom.hom := by
    have hs : z = e ≫ F.map x := terminalPointPullback_eq_siteBaseChange f x
    have hφ : φ.hom.hom = F.map χ.hom.hom ≫ r.hom.hom := rfl
    calc
      _ = (e ≫ F.map x) ≫ φ.hom.hom := congrArg (fun q => q ≫ φ.hom.hom) hs
      _ = (e ≫ F.map x) ≫ F.map χ.hom.hom ≫ r.hom.hom :=
        congrArg (fun q => (e ≫ F.map x) ≫ q) hφ
      _ = e ≫ (F.map x ≫ F.map χ.hom.hom) ≫ r.hom.hom :=
        (Category.assoc _ _ _).trans (congrArg (fun q => e ≫ q) (Category.assoc _ _ _).symm)
      _ = _ := congrArg (fun q => e ≫ q ≫ r.hom.hom) (F.map_comp x χ.hom.hom).symm
  let c := representedIntegerSection (MultiplicativeGroup.rootsGroupScheme Y n)
  have hmap : a ≫ representedSheafMap φ = c (z ≫ φ.hom.hom) :=
    representedIntegerSection_map φ z
  exact h.trans (congrArg Ext.mk₀ ((congrArg c hz.symm).trans hmap.symm))

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
