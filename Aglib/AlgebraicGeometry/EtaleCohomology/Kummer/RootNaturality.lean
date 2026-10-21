/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootCover
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.CoefficientBaseChange

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.EtaleH1.Kummer.RootNaturality` at
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`2f435031214b64fd53ecc1207a258cf4c21c9799817252d4c26e17d2aa1859d4`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.EtaleCohomology

/-!
# Pullback of actual positive Kummer root classes

For every actual scheme map, this leaf constructs the literal adjoint map
between the positive root torsors of a global unit and its pullback. The
existing canonical torsor-to-Ext construction then gives the native H1
pullback formula with the actual roots coefficient isomorphism.

The level is positive and globally invertible; Ext-size instances are explicit.
No local Kummer surjectivity, field comparison, primitive root, Bockstein or
specialization statement is an input here. This is the generic construction
used by the origin-trait slice of K2-018#prop:k2018-arithmetic-characters,
mathematical source revision e73d98b1b5c1e5abcdebf7d058e436d792b87982.
Exact-source compilation and axiom receipts are recorded separately.
-/

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.Scheme.EtaleCohomology

namespace GroupCohomology.Kummer.RootNaturality
open Coefficients CoefficientBaseChange
open GroupCohomology.Kummer.Torsor
universe u w w'
variable {X S : Scheme.{u}} (f : S ⟶ X) (n : ℕ)
  (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤))) (a : Γ(X, ⊤)ˣ)

/-- Literal pullback of the given global unit. -/
def pulledUnit : Γ(S, ⊤)ˣ := Units.map f.appTop.hom.toMonoidHom a

/-- The actual Gm adjunction map carries the root equation's constant section
to the constant section of the literal pulled-back unit. -/
theorem gmUnit_restrict_unit (U : X.Etaleᵒᵖ) :
    (gmUnit f).hom.app U (restrictSection (gm X) (unitSection X a) U) =
      restrictSection (gm S) (unitSection S (pulledUnit f a)) ((siteBaseChange f).op.obj U) := by
  apply (unitsSections S ((siteBaseChange f).op.obj U)).injective
  apply Additive.toMul.injective
  rw [gmUnit_sections, unitSection_restrict, unitSection_restrict]
  apply Units.ext
  have h := congrArg Scheme.Hom.appTop (pullback.condition (f := U.unop.hom) (g := f))
  change (pullback.fst U.unop.hom f).appTop.hom (U.unop.hom.appTop.hom (a : Γ(X, ⊤))) =
    (pullback.snd U.unop.hom f).appTop.hom (f.appTop.hom (a : Γ(X, ⊤)))
  have h' := congrArg (fun k => k.hom (a : Γ(X, ⊤))) h
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h'
  convert h' using 1

/-- The literal roots and Gm adjunction maps respect the native root inclusion. -/
theorem gmUnit_inclusion (U : X.Etaleᵒᵖ) (z : (mu X n).obj.obj U) :
    (gmUnit f).hom.app U ((inclusion X n).hom.app U z) =
      (inclusion S n).hom.app ((siteBaseChange f).op.obj U) ((rootsUnit f n).hom.app U z) := by
  apply (unitsSections S ((siteBaseChange f).op.obj U)).injective
  apply Additive.toMul.injective
  rw [gmUnit_sections, inclusion_apply, inclusion_apply, rootsUnit_sections]

/-- A morphism on the middle sheaves preserving a fibre condition induces
the literal map of actual fibre sheaves into direct image. -/
def fiberCarrierUnit
    (E : ShortComplex (AbelianSheaf.{u, u + 1} X))
    (D : ShortComplex (AbelianSheaf.{u, u + 1} S))
    (z : E.X₃.obj.obj (op (etaleTerminal X)))
    (w : D.X₃.obj.obj (op (etaleTerminal S)))
    (q : E.X₂ ⟶ (directImage f).obj D.X₂)
    (hq : ∀ (U : X.Etaleᵒᵖ) (t : E.X₂.obj.obj U),
      E.g.hom.app U t = restrictSection E.X₃ z U →
        D.g.hom.app ((siteBaseChange f).op.obj U) (q.hom.app U t) =
          restrictSection D.X₃ w ((siteBaseChange f).op.obj U)) :
    extensionFiberSheaf E z ⟶ (setDirectImage f).obj (extensionFiberSheaf D w) where
  hom := {
    app U := TypeCat.ofHom fun t => ⟨q.hom.app U t.val, hq U t.val t.property⟩
    naturality {U V} g := by
      apply ConcreteCategory.hom_ext
      intro t
      apply Subtype.ext
      exact ConcreteCategory.congr_hom (q.hom.naturality g) t.val }

/-- The actual root-torsor carrier map is restriction of the actual unit section. -/
def rootCarrierUnit :
    (rootTorsor GroupCohomology.Kummer.RootCover.etalePowerSurjectivity X n hn
        hinv a).carrier ⟶
      (setDirectImage f).obj
        (rootTorsor GroupCohomology.Kummer.RootCover.etalePowerSurjectivity S n hn
          (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible f n
              hinv) (pulledUnit f a)).carrier :=
  fiberCarrierUnit f (GroupCohomology.Kummer.Coefficients.sequence X n)
      (GroupCohomology.Kummer.Coefficients.sequence S n)
    (unitSection X a) (unitSection S (pulledUnit f a)) (gmUnit f) (by
      intro U t ht
      change n • (gmUnit f).hom.app U t = _
      rw [← map_nsmul]
      change (gmUnit f).hom.app U ((power X n).hom.app U t) = _
      change (power X n).hom.app U t = restrictSection (gm X) (unitSection X a) U at ht
      rw [ht]
      exact gmUnit_restrict_unit f a U)

/-- A genuine equivariant adjoint map between the positive root torsors. -/
def rootAdjointHom :
    Scheme.EtaleCohomology.Torsor.AdjointHom f (rootsUnit f n)
      (rootTorsor GroupCohomology.Kummer.RootCover.etalePowerSurjectivity X n
          hn hinv a)
      (rootTorsor GroupCohomology.Kummer.RootCover.etalePowerSurjectivity S n hn
        (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible f n
            hinv) (pulledUnit f a)) where
  map := rootCarrierUnit f n hn hinv a
  equivariant U z t := by
    apply Subtype.ext
    change (gmUnit f).hom.app U ((inclusion X n).hom.app U z + (show (gm X).obj.obj U from t.val)) =
      (inclusion S n).hom.app ((siteBaseChange f).op.obj U) ((rootsUnit f n).hom.app U z) +
        (show (gm S).obj.obj ((siteBaseChange f).op.obj U) from (gmUnit f).hom.app U t.val)
    rw [map_add, gmUnit_inclusion]

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- Native pullback of the actual positive root class is the root class of
the literal pulled-back unit. No comparison or beta identity is assumed. -/
theorem rootClass_pullback :
    GroupCohomology.Kummer.CoefficientBaseChange.h1Map f n hn hinv
      (rootClass GroupCohomology.Kummer.RootCover.etalePowerSurjectivity X n
          hn hinv a) =
      rootClass GroupCohomology.Kummer.RootCover.etalePowerSurjectivity S n hn
        (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible f n
            hinv) (pulledUnit f a) :=
  GroupCohomology.Kummer.CoefficientBaseChange.h1Map_torsor f n hn hinv
      (rootAdjointHom f n hn hinv a)

end GroupCohomology.Kummer.RootNaturality

