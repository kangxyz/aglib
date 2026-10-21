/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteRepresentedTransitions

/-! Actual representatives on open subschemes and their restriction. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)

namespace AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

universe u
variable {X : Scheme.{u}} (F : Scheme.EtaleCohomology.SetSheaf X)

/-- A finite etale cover of an open subscheme together with an isomorphism representing the
restriction of `F`. -/
structure FiniteSetOpenRepresentation (U : X.Opens) where
  /-- The finite etale cover over the open subscheme `U`. -/
  cover : Scheme.FiniteEtale U.toScheme
  /-- The isomorphism from the represented sheaf of `cover` to the restriction of `F` along
  `U.ι`. -/
  iso : Scheme.EtaleCohomology.finiteRepresentedSetSheaf cover ≅
    (Scheme.EtaleCohomology.setEtaleRestriction
    U.ι).obj F

namespace FiniteSetOpenRepresentation
variable {F} {U V : X.Opens}

/-- The representation over `V` obtained by pulling back the cover and its representing
isomorphism along `V ≤ U`. -/
def restrict (r : FiniteSetOpenRepresentation F U) (h : V ≤ U) :
    FiniteSetOpenRepresentation F V where
  cover := (baseChange (X.homOfLE h)).obj r.cover
  iso := finiteRepresentedCommonChartIso U.ι (X.homOfLE h) V.ι
    (X.homOfLE_ι h) r.cover r.iso

/-- Replace an arbitrary open immersion by its actual open range, transporting
both the cover and its represented-sheaf isomorphism. -/
def ofOpenImmersion {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (Y : Scheme.FiniteEtale U) (e : Scheme.EtaleCohomology.finiteRepresentedSetSheaf Y ≅
      (Scheme.EtaleCohomology.setEtaleRestriction j).obj F) :
    FiniteSetOpenRepresentation F j.opensRange := by
  let a : U ≅ j.opensRange.toScheme :=
    IsOpenImmersion.isoOfRangeEq j j.opensRange.ι Subtype.range_val.symm
  exact {
    cover := (baseChange a.inv).obj Y
    iso := finiteRepresentedCommonChartIso j a.inv j.opensRange.ι
      (IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _) Y e }

end FiniteSetOpenRepresentation

/-- The condition that `U` is affine and the restriction of `F` to `U` has a finite etale
representation. -/
def IsGoodAffineOpen (U : X.Opens) : Prop :=
  IsAffineOpen U ∧ Nonempty (FiniteSetOpenRepresentation F U)

theorem IsGoodAffineOpen.restrict {U V : X.Opens} (hU : IsGoodAffineOpen F U)
    (hVU : V ≤ U) (hV : IsAffineOpen V) : IsGoodAffineOpen F V := by
  obtain ⟨r⟩ := hU.2
  exact ⟨hV, ⟨r.restrict hVU⟩⟩

end AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 66ae67e36579df9e602d6575d19878e53dfef4ea88201dfa21bb21d133c8eeee.
Definitions, hypotheses and universes are retained modulo native names. -/
