/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackComposition
public import Aglib.CategoryTheory.Sites.SheafCohomology.OriginalSections.Zero
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.EtaleH1.DegreeZeroPullback` at R5
revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`bc1c5b4813b0ea9b8bc3717ad8fc5a34eea24f61306e3782891a0ecf21873e50`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleCohomology

/-!
# Actual global sections and degree-zero pullback

This constructs the map on actual terminal-object sections from the existing
inverse-image unit and direct-image global-sections transport, and identifies
it with the constant-integer transport used by actual Ext-based H1 pullback.
-/
noncomputable section
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u w w'
attribute [local instance] hasSheafifyLarge
variable {X S : Scheme.{u}} (f : S ⟶ X)

/-- Actual pullback of global sections: the inverse-image unit followed by
canonical transport of the terminal etale object. -/
def globalSectionsPullback (L : AbelianSheaf.{u, u + 1} X) :
    (globalSections X).obj L ⟶ (globalSections S).obj ((inverseImage f).obj L) :=
  (globalSections X).map ((inverseImageAdjunction f).unit.app L) ≫
    (directImageGlobalSectionsIso f).hom.app ((inverseImage f).obj L)

/-- The actual constant-sheaf comparison is the mate of the actual map on
terminal-object sections, for every coefficient group and every sheaf map. -/
theorem constantTransport_homEquiv (A : AddCommGrpCat.{u + 1})
    {L : AbelianSheaf.{u, u + 1} X}
    (a : (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A ⟶ L) :
    (constantAdjunction S).homEquiv A _
      (((inverseImageConstantIso f).app A).inv ≫ (inverseImage f).map a) =
    (constantAdjunction X).homEquiv A L a ≫ globalSectionsPullback f L :=
  Adjunction.unitSectionMap_homEquiv (constantAdjunction X) (inverseImageAdjunction f)
    (constantAdjunction S)
    (directImageGlobalSectionsIso f) (inverseImageConstantIso f)
    (inverseImageConstantCanonicalIso_eq f).symm a

section Cohomology
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- Degree-zero pullback uses the same exact inverse image and constant-integer
transport as the existing h1Pullback. -/
def h0Pullback (L : AbelianSheaf.{u, u + 1} X) :
    Sheaf.H.{w} L 0 →+ Sheaf.H.{w'} ((inverseImage f).obj L) 0 :=
  ((Abelian.Ext.mk₀ (((inverseImageConstantIso f).app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv)).precomp _ (zero_add 0)).comp
      ((inverseImage f).mapExtAddHom _ L 0)

theorem h0Pullback_mk₀ {L : AbelianSheaf.{u, u + 1} X}
    (a : (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ L) :
    h0Pullback f L (Abelian.Ext.mk₀ a) =
      Abelian.Ext.mk₀ (((inverseImageConstantIso f).app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv ≫ (inverseImage f).map a) :=
  (inverseImage f).extPrecompMap_mk₀
    ((inverseImageConstantIso f).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ))) a

omit [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)] in
theorem h0_equiv_mk₀ {L : AbelianSheaf.{u, u + 1} X}
    (a : (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ L) :
    Sheaf.H.equiv₀ L (etaleTerminalIsTerminal X) (Abelian.Ext.mk₀ a) =
      AddCommGrpCat.uliftZMultiplesAddEquiv ((globalSections X).obj L)
        ((constantAdjunction X).homEquiv _ _ a) :=
  Adjunction.integerExtZeroSectionsEquiv_mk₀ (constantAdjunction X) a

/-- The cohomological degree-zero map is exactly pullback of actual global sections. -/
theorem h0Pullback_equiv₀ (L : AbelianSheaf.{u, u + 1} X) (x : Sheaf.H.{w} L 0) :
    Sheaf.H.equiv₀ ((inverseImage f).obj L) (etaleTerminalIsTerminal S)
        (h0Pullback f L x) =
      globalSectionsPullback f L (Sheaf.H.equiv₀ L (etaleTerminalIsTerminal X) x) :=
  Adjunction.integerExtZeroSectionsEquiv_pullback (constantAdjunction X) (inverseImageAdjunction f)
    (constantAdjunction S)
    (directImageGlobalSectionsIso f) (inverseImageConstantIso f)
    (inverseImageConstantCanonicalIso_eq f).symm L x

/-- The actual global-section description of degree-zero pullback, in the
orientation used to evaluate connecting maps on sections. -/
theorem h0Pullback_equiv₀_symm (L : AbelianSheaf.{u, u + 1} X)
    (z : (globalSections X).obj L) :
    h0Pullback f L ((Sheaf.H.equiv₀ L (etaleTerminalIsTerminal X)).symm z) =
      (Sheaf.H.equiv₀ ((inverseImage f).obj L) (etaleTerminalIsTerminal S)).symm
        (globalSectionsPullback f L z) :=
  Adjunction.integerExtZeroSectionsEquiv_pullback_symm (constantAdjunction X)
    (inverseImageAdjunction f) (constantAdjunction S)
    (directImageGlobalSectionsIso f) (inverseImageConstantIso f)
    (inverseImageConstantCanonicalIso_eq f).symm L z

/-- Cross-site connecting naturality with the actual h1Pullback and degree-zero
map. The short exact sequence is arbitrary here; the native application
supplies the constructed actual finite coefficient sequence. -/
theorem connecting_h0Pullback (T : ShortComplex (AbelianSheaf.{u, u + 1} X))
    (hT : T.ShortExact) (x : Sheaf.H.{w} T.X₃ 0) :
    h1Pullback f T.X₁ (Sheaf.H.δ hT 0 1 rfl x) =
      Sheaf.H.δ (hT.map_of_exact (inverseImage f)) 0 1 rfl (h0Pullback f T.X₃ x) :=
  (congrArg (fun k => k x)
    ((inverseImage f).extPrecompMap_connecting
      ((inverseImageConstantIso f).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ))) T hT 0)).symm

/-- The same square on actual terminal-object sections. -/
theorem connecting_globalSectionsPullback (T : ShortComplex (AbelianSheaf.{u, u + 1} X))
    (hT : T.ShortExact) (z : (globalSections X).obj T.X₃) :
    h1Pullback f T.X₁
      (Sheaf.H.δ hT 0 1 rfl ((Sheaf.H.equiv₀ T.X₃ (etaleTerminalIsTerminal X)).symm z)) =
    Sheaf.H.δ (hT.map_of_exact (inverseImage f)) 0 1 rfl
      ((Sheaf.H.equiv₀ ((inverseImage f).obj T.X₃) (etaleTerminalIsTerminal S)).symm
        (globalSectionsPullback f T.X₃ z)) := by
  rw [connecting_h0Pullback, h0Pullback_equiv₀_symm]

end Cohomology
end AlgebraicGeometry.Scheme.EtaleCohomology
