/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Presheaf
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# The fppf Picard sheaf

For a morphism of schemes `p : X ⟶ S`, `fppfPicardSheaf p` is
`Pic_{X/S,(fppf)}`: Mathlib's sheafification `presheafToSheaf`, for the topology
`Scheme.fppfTopology.over S` on `Over S` induced by `Scheme.fppfTopology`, of the
relative Picard functor `relativePicardFunctor p` (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Def. 2.2, p. 17). Values lie in `AddCommGrpCat.{u + 1}`;
the sheafification instance is Mathlib's plus-plus construction
(`Mathlib.CategoryTheory.Sites.LeftExact`).

`toFppfPicardSheaf p` is the sheafification unit `P_{X/S} ⟶ Pic_{X/S,(fppf)}`, and
`fppfPicardSheafHomEquiv` is its universal property: morphisms from
`Pic_{X/S,(fppf)}` to an fppf sheaf of abelian groups correspond to morphisms from
`P_{X/S}` by precomposition with the unit.

Every Picard class of a scheme vanishes on a Zariski covering, hence on an fppf
covering (`vanishingSieve_mem_fppfTopology`). Therefore the quotient map
`familyPicardFunctor p ⟶ relativePicardFunctor p` is locally injective and locally
surjective, and it becomes an isomorphism after fppf sheafification:
`fppfFamilyPicardSheafIso p` identifies the fppf sheafification of Kleiman's absolute
functor `T ↦ Pic(X ×_S T)` with `Pic_{X/S,(fppf)}` (Kleiman, Def. 2.2, p. 17, and the
remark after it). [Stacks 0B9L](https://stacks.math.columbia.edu/tag/0B9L) defines the
Picard functor as the fppf sheafification of `T ↦ Pic(X_T)` with values in sets; here
sheafification is taken in `AddCommGrpCat.{u + 1}`. Kleiman forms the fppf functor on
locally Noetherian `S`-schemes, whereas the sheaf here is formed on the big site
`Over S`, as in Stacks 0B9L. Fppf coverings of a locally Noetherian scheme and their
fibre products are again locally Noetherian, so the two sheafifications agree on that
subcategory; this comparison is not formalized here.

Injectivity of the unit and its bijectivity with a section are not proved here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.RelativePicard

universe u

variable {S X : Scheme.{u}}

/-- `Pic_{X/S,(fppf)}`: the fppf sheafification on `Over S` of the relative Picard
functor `T ↦ Pic(X ×_S T) / Pic(T)` (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, Def. 2.2, p. 17). -/
def fppfPicardSheaf (p : X ⟶ S) : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1} :=
  (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).obj
    (relativePicardFunctor p)

/-- The sheafification unit `P_{X/S} ⟶ Pic_{X/S,(fppf)}`. -/
def toFppfPicardSheaf (p : X ⟶ S) : relativePicardFunctor p ⟶ (fppfPicardSheaf p).obj :=
  toSheafify (Scheme.fppfTopology.over S) (relativePicardFunctor p)

theorem fppfPicardSheaf_isSheaf (p : X ⟶ S) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) (fppfPicardSheaf p).obj :=
  (fppfPicardSheaf p).property

/-- The universal property of `Pic_{X/S,(fppf)}`: morphisms to an fppf sheaf `F` correspond
to morphisms `P_{X/S} ⟶ F`. -/
def fppfPicardSheafHomEquiv (p : X ⟶ S)
    (F : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}) :
    (fppfPicardSheaf p ⟶ F) ≃ (relativePicardFunctor p ⟶ F.obj) :=
  (sheafificationAdjunction (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).homEquiv _ _

theorem fppfPicardSheafHomEquiv_apply (p : X ⟶ S)
    (F : Sheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}) (g : fppfPicardSheaf p ⟶ F) :
    fppfPicardSheafHomEquiv p F g = toFppfPicardSheaf p ≫ g.hom := by
  exact (sheafificationAdjunction (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).homEquiv_unit
    _ _ g

open Scheme.Modules.Invertible in
/-- The sieve of morphisms along which a Picard class pulls back to zero. -/
def vanishingSieve {T : Scheme.{u}} (a : PicardGroup T) : Sieve T where
  arrows _ f := pullbackClass f a = 0
  downward_closed {Y Z f} hf g := by
    rw [pullbackClass_comp, show pullbackClass f a = 0 from hf, pullbackClass_zero]

open Scheme.Modules.Invertible in
/-- Every Picard class vanishes on a Zariski covering: line bundles are locally trivial. -/
theorem vanishingSieve_mem_zariskiTopology {T : Scheme.{u}} (a : PicardGroup T) :
    vanishingSieve a ∈ Scheme.zariskiTopology T := by
  induction a using Quotient.inductionOn with | h L =>
  have h := (isLocallyRankOne_iff_restrict_unit L.val).mp L.property
  choose U hxU e using h
  have hU : TopologicalSpace.IsOpenCover U :=
    eq_top_iff.mpr fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxU x⟩
  rw [Scheme.mem_grothendieckTopology_iff]
  refine ⟨T.openCoverOfIsOpenCover U hU, ?_⟩
  rintro _ _ ⟨x⟩
  exact Quotient.sound ⟨((Scheme.Modules.restrictFunctorIsoPullback (U x).ι).app L.val).symm ≪≫
    (e x).some ≪≫ (CategoryTheory.Limits.coproductUniqueIso
      (fun _ : PUnit.{u + 1} => SheafOfModules.unit (U x).toScheme.ringCatSheaf)).symm⟩

theorem vanishingSieve_mem_fppfTopology {T : Scheme.{u}}
    (a : Scheme.Modules.Invertible.PicardGroup T) :
    vanishingSieve a ∈ Scheme.fppfTopology T :=
  Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage T
    (vanishingSieve_mem_zariskiTopology a)

instance quotientProjection_isLocallySurjective (p : X ⟶ S) :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (quotientProjection p) :=
  Presheaf.isLocallySurjective_of_surjective _ _ (quotientProjection_app_surjective p)

instance quotientProjection_isLocallyInjective (p : X ⟶ S) :
    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) (quotientProjection p) where
  equalizerSieve_mem {T} x y h := by
    have h' : (QuotientAddGroup.mk x : (familyPicardFunctor p).obj T ⧸ baseImage p T) =
        QuotientAddGroup.mk y := h
    obtain ⟨a, ha⟩ := QuotientAddGroup.eq.mp h'
    rw [GrothendieckTopology.mem_over_iff]
    refine (Scheme.fppfTopology).superset_covering ?_ (vanishingSieve_mem_fppfTopology a)
    intro Z g hg
    rw [Sieve.overEquiv_iff]
    let f : (Over.mk (g ≫ T.unop.hom) ⟶ T.unop) := Over.homMk g
    have h0 : ((familyPicardFunctor p).map f.op).hom (-x + y) = 0 := by
      rw [← ha]
      change Scheme.Modules.Invertible.pullbackClass ((familyScheme p).map f)
        (Scheme.Modules.Invertible.pullbackClass (pullback.snd p T.unop.hom) a) = 0
      have hga : Scheme.Modules.Invertible.pullbackClass g a = 0 := hg
      exact (Scheme.Modules.Invertible.pullbackClass_comp _ _ a).symm.trans
        ((congrArg (fun φ => Scheme.Modules.Invertible.pullbackClass φ a)
          (familyScheme_map_snd p f)).trans
          ((Scheme.Modules.Invertible.pullbackClass_comp _ _ a).trans
            ((congrArg _ hga).trans (Scheme.Modules.Invertible.pullbackClass_zero _))))
    rw [map_add, map_neg, neg_add_eq_zero] at h0
    exact h0

/-- Fppf sheafification turns the quotient map `Pic_X ⟶ P_{X/S}` into an isomorphism. -/
instance isIso_presheafToSheaf_map_quotientProjection (p : X ⟶ S) :
    IsIso ((presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).map
      (quotientProjection p)) :=
  ((Scheme.fppfTopology.over S).W_iff (quotientProjection p)).mp
    ((Scheme.fppfTopology.over S).W_of_isLocallyBijective (quotientProjection p))

/-- `Pic_{X/S,(fppf)}` is the fppf sheafification of the absolute functor `T ↦ Pic(X ×_S T)`
(Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Def. 2.2, p. 17, and the remark after
it; compare the set-valued definition in [Stacks 0B9L](https://stacks.math.columbia.edu/tag/0B9L)). -/
def fppfFamilyPicardSheafIso (p : X ⟶ S) :
    (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).obj
        (familyPicardFunctor p) ≅ fppfPicardSheaf p :=
  @asIso _ _ _ _ ((presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).map
    (quotientProjection p)) (isIso_presheafToSheaf_map_quotientProjection p)

theorem fppfFamilyPicardSheafIso_hom (p : X ⟶ S) :
    (fppfFamilyPicardSheafIso p).hom =
      (presheafToSheaf (Scheme.fppfTopology.over S) AddCommGrpCat.{u + 1}).map
        (quotientProjection p) := rfl

end AlgebraicGeometry.Scheme.RelativePicard
