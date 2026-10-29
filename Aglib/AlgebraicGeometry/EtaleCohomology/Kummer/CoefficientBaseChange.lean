/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.Coefficients
public import Aglib.AlgebraicGeometry.Group.RootsFiniteEtale
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.SchemeTorsorBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.MarkedCoefficients
public import Aglib.AlgebraicGeometry.Group.MultiplicativeBaseChange

/-!
Native migration from
`R5Lab.Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Kummer.CoefficientBaseChange` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`f27a777314607f14429e8985784cf2a146c429c4ec4fb8ef898bb2f231bed7bd`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleCohomology
/-!
Interface migration basis: `46f53465aaf3b0167049e9c8e9e2294111bb4281`.
Accepted object-owner map SHA-256:
`8a638d1a1d17381235478e81285ee940a20aedecb03e9d3ff1ae9878791e1868`.
Imports follow the current object owners; existing R5Lab declaration names and
all construction/proof bodies are preserved. Historical source and validation
receipts below retain their original basis. New-interface validation is pending.
-/
/-!
# Actual multiplicative and root coefficient base change

Manuscript locator: `K2-018#lem:k2018-geometric-exact-order`.
Mathematical source revision: `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Engineering source revision: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.

The literal scheme-group base-change isomorphisms induce actual maps from
Gm and mu_n into small-etale direct image, with their actual function-unit
coordinates. At positive globally invertible level, the proved etaleness
of the roots scheme makes the roots inverse-image comparison invertible.
It is exactly representedSheafBaseChangeIso followed by the represented
map of the actual roots group-scheme base-change isomorphism. Its adjunction
unit is proved to be the literal section pullback, fixing the coefficient
map consumed by actual torsor/Ext naturality. No Gm inverse-image
isomorphism is asserted.

The H1 map is the actual inverse-image H1 pullback followed by that actual
coefficient map. The displayed torsor-class identity follows from an
ordinary equivariant adjoint sheaf map via the existing proved canonical
extension construction. No torsor classification, new standard family,
Picard comparison or desired application square is assumed. This generic
coefficient module imports no Curves/Picard or KTheory.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory Opposite
namespace GroupCohomology.Kummer.CoefficientBaseChange
open AlgebraicGeometry.Scheme.Group
open AlgebraicGeometry.Scheme.EtaleCohomology Kummer.Coefficients
universe u
variable {X S : Scheme.{u}} (f : S ⟶ X) (n : ℕ)
/-- The commutative group-object structure on the scheme of `n`th roots of unity over `Y`. -/
local instance (Y : Scheme.{u}) : CommGrpObj (MultiplicativeGroup.rootsGroupScheme Y n).X :=
  MultiplicativeGroup.rootsCommGroup Y n
/-- The commutative group-object structure on the multiplicative group scheme over `Y`. -/
local instance (Y : Scheme.{u}) : CommGrpObj (MultiplicativeGroup.groupScheme Y).X :=
  MultiplicativeGroup.commGroup Y

/-- Literal roots pullback on small-etale sections, for every level. -/
def rootsUnit : mu X n ⟶ (directImage f).obj (mu S n) :=
  Scheme.EtaleCohomology.SchemeTorsorBaseChange.representedCoefficientUnit f
      (MultiplicativeGroup.rootsGroupScheme X n) ≫
    (directImage f).map (representedSheafMap (MultiplicativeBaseChange.rootsBaseChangeIso f n).hom)

/-- Literal units pullback; no claim that the Gm inverse-image map is invertible. -/
def gmUnit : gm X ⟶ (directImage f).obj (gm S) :=
  Scheme.EtaleCohomology.SchemeTorsorBaseChange.representedCoefficientUnit f
      (MultiplicativeGroup.groupScheme X) ≫
    (directImage f).map (representedSheafMap (MultiplicativeBaseChange.unitsBaseChangeIso f).hom)

/-- The canonical roots coefficient inverse-image isomorphism at positive invertible level. -/
def rootsPullbackIso (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :
    (inverseImage f).obj (mu X n) ≅ mu S n := by
  letI : Etale (MultiplicativeGroup.rootsGroupScheme X n).X.hom :=
    RootsFiniteEtale.rootsScheme_etale X n hn hinv
  exact representedSheafBaseChangeIso f (MultiplicativeGroup.rootsGroupScheme X n) ≪≫
    Scheme.EtaleCohomology.MarkedCoefficients.representedSheafIso
        (MultiplicativeBaseChange.rootsBaseChangeIso f n)

/-- This exact coefficient isomorphism is adjoint to the literal roots section map. -/
theorem rootsPullbackIso_unit (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :
    (inverseImageAdjunction f).unit.app (mu X n) ≫
      (directImage f).map (rootsPullbackIso f n hn hinv).hom = rootsUnit f n := by
  let : Etale (MultiplicativeGroup.rootsGroupScheme X n).X.hom :=
    RootsFiniteEtale.rootsScheme_etale X n hn hinv
  unfold rootsPullbackIso rootsUnit
  simp only [Iso.trans_hom, CategoryTheory.Functor.map_comp, ← Category.assoc]
  erw [Scheme.EtaleCohomology.SchemeTorsorBaseChange.representedSheafBaseChangeIso_unit f
    (MultiplicativeGroup.rootsGroupScheme X n)]
  rfl

/-- The actual adjoint coefficient map is the displayed roots isomorphism. -/
theorem rootsUnit_adjoint (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :
    torsorAdjunctionCoefficient f (q := rootsUnit f n) = (rootsPullbackIso f n hn hinv).hom := by
  let e := (inverseImageAdjunction f).homEquiv (mu X n) (mu S n)
  change e.symm (rootsUnit f n) = (rootsPullbackIso f n hn hinv).hom
  apply e.injective
  exact (e.apply_symm_apply (rootsUnit f n)).trans (rootsPullbackIso_unit f n hn hinv).symm

/-- Positive invertibility of the level is preserved by the actual structural ring map. -/
theorem levelInvertible (f : S ⟶ X) (n : ℕ) (hinv : IsUnit (n : Γ(X, ⊤))) : IsUnit (n : Γ(S,
    ⊤)) := by
  simpa only [map_natCast] using hinv.map f.appTop.hom

/-- Every root section pulls back by the actual first projection on functions. -/
theorem rootsUnit_sections (U : X.Etaleᵒᵖ) (ζ : (mu X n).obj.obj U) :
    ((rootsSections S n ((siteBaseChange f).op.obj U) ((rootsUnit f n).hom.app U ζ)).toMul :
      Γ(((siteBaseChange f).op.obj U).unop.left, ⊤)ˣ) =
    Units.map (Limits.pullback.fst U.unop.hom f).appTop.hom.toMonoidHom
      ((rootsSections X n U ζ).toMul : Γ(U.unop.left, ⊤)ˣ) := by
  exact MultiplicativeBaseChange.rootsBaseChangeIso_pullback f n
    ((Scheme.Etale.forget X).obj U.unop) ζ.down.toMul

/-- Every Gm section pulls back by the same actual first projection. -/
theorem gmUnit_sections (U : X.Etaleᵒᵖ) (a : (gm X).obj.obj U) :
    (unitsSections S ((siteBaseChange f).op.obj U) ((gmUnit f).hom.app U a)).toMul =
      Units.map (Limits.pullback.fst U.unop.hom f).appTop.hom.toMonoidHom
        (unitsSections X U a).toMul := by
  exact MultiplicativeBaseChange.unitsBaseChangeIso_pullback f
    ((Scheme.Etale.forget X).obj U.unop) a.down.toMul

universe w w'
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- Genuine small-etale H1 pullback with the canonical roots coefficient transport. -/
def h1Map (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) :
    H1Etale X (mu X n) →+ H1Etale S (mu S n) :=
  (coefficientMap (rootsPullbackIso f n hn hinv).hom).comp (h1Pullback f (mu X n))

/-- An actual equivariant adjoint torsor map proves this precise H1 pullback equation. -/
theorem h1Map_torsor (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    {P : Torsor (mu X n)} {Q : Torsor (mu S n)} (r :
        Scheme.EtaleCohomology.Torsor.AdjointHom f (rootsUnit f n) P Q) :
    h1Map f n hn hinv (torsorExtClass P) = torsorExtClass Q := by
  change coefficientMap (rootsPullbackIso f n hn hinv).hom
    (h1Pullback f (mu X n) (torsorExtClass P)) = _
  rw [← rootsUnit_adjoint f n hn hinv]
  exact torsorExtClass_adjunction f r
end GroupCohomology.Kummer.CoefficientBaseChange
