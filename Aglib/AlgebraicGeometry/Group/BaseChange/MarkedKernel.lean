/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.ScalarExtension
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.PointedCover
public import Aglib.AlgebraicGeometry.SchemeOverField
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Field
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Constants
public import Aglib.AlgebraicGeometry.Cohomology.Modules.StructureSheaf

/-!
# Base change of actual universal kernel markings

Source: `K2-018#prop:k2018-integrality-test` and
`K2-018#prop:k2018-arithmetic-characters`,
`research/exposes/K2/018/expose.tex` at mathematical revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, SHA256
`e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.
Engineering input: `5d33bf0f0c5466340593baedce4c2f7c2aa49a9b`,
Lean 4.34.1/mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

The general construction pulls back the actual group schemes, coefficient
object and universal kernel marking along an arbitrary scheme morphism.
It retains the original cartesian torsor action and its supplied rigidity data.
The resulting marking uses the canonical group-scheme base-change maps and
preserves the specified inclusion and kernel equations. Historical application
and engineering provenance is recorded above.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.Cohomology (ProperStructureCohomologyBaseChange)
open _root_.AlgebraicGeometry.Scheme.Group.BaseChange
  (groupSchemeBaseChange groupSchemeBaseChange_map_left_fst groupSchemeBaseChange_map_left_snd
    groupSchemeScalarExtension pullbackFiberMulEquiv pullbackFiberMulEquiv_naturality
    pullbackFiberMulEquiv_symm_apply_left scalarExtensionMap)
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Group.BaseChange

universe u
attribute [local instance] Over.cartesianMonoidalCategory

section General
variable {S T : Scheme.{u}} (f : S ⟶ T)

/-- The actual group pullback used throughout this module, on the module source basis.
Source: scalar-extension subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
abbrev baseChangedGroup (G : Grp (Over T)) : Grp (Over S) :=
  (groupSchemeBaseChange f).functor.obj G

/-- The actual pullback of an underlying over-category arrow is a Cartesian square.
Source: scalar-extension subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
theorem map_isPullback {G H : Grp (Over T)} (p : G ⟶ H) :
    IsPullback (pullback.fst G.X.hom f)
      ((groupSchemeBaseChange f).functor.map p).hom.hom.left
      p.hom.hom.left (pullback.fst H.X.hom f) := by
  apply IsPullback.flip
  apply IsPullback.of_right (h₁₂ := pullback.snd H.X.hom f)
    (h₂₂ := H.X.hom) (v₁₃ := f)
    _ (groupSchemeBaseChange_map_left_fst f p)
    (IsPullback.of_hasPullback H.X.hom f).flip
  simpa only [groupSchemeBaseChange_map_left_snd, Over.w] using
    (IsPullback.of_hasPullback G.X.hom f).flip

/-- Finiteness of the actual group arrow is preserved by pullback.
Source: scalar-extension subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
theorem map_finite {G H : Grp (Over T)} (p : G ⟶ H)
    (hp : IsFinite p.hom.hom.left) :
    IsFinite ((groupSchemeBaseChange f).functor.map p).hom.hom.left :=
  MorphismProperty.of_isPullback (map_isPullback f p) hp

/-- Étaleness of the actual group arrow is preserved by pullback.
Source: scalar-extension subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
theorem map_etale {G H : Grp (Over T)} (p : G ⟶ H)
    (hp : Etale p.hom.hom.left) :
    Etale ((groupSchemeBaseChange f).functor.map p).hom.hom.left :=
  MorphismProperty.of_isPullback (map_isPullback f p) hp

/-- Surjectivity of the actual group arrow is preserved by pullback.
Source: scalar-extension subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
theorem map_surjective {G H : Grp (Over T)} (p : G ⟶ H)
    (hp : Surjective p.hom.hom.left) :
    Surjective ((groupSchemeBaseChange f).functor.map p).hom.hom.left :=
  MorphismProperty.of_isPullback (map_isPullback f p) hp

/-- Sections of a pulled-back group, with their actual multiplicative structure.
Source: scalar-extension subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
def sectionsMulEquiv (U : Over S) (G : Grp (Over T)) :
    ((Over.map f).obj U ⟶ G.X) ≃* (U ⟶ (baseChangedGroup f G).X) :=
  pullbackFiberMulEquiv f U.hom G

/-- Naturality of the actual section equivalence in the group morphism.
Source: scalar-extension subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
theorem sectionsMulEquiv_naturality (U : Over S) {G H : Grp (Over T)}
    (p : G ⟶ H) (a : (Over.map f).obj U ⟶ G.X) :
    sectionsMulEquiv f U H (a ≫ p.hom.hom) =
      sectionsMulEquiv f U G a ≫ ((groupSchemeBaseChange f).functor.map p).hom.hom :=
  pullbackFiberMulEquiv_naturality f U.hom p a

/-- Naturality of the inverse section equivalence.
Source: scalar-extension subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
theorem sectionsMulEquiv_symm_naturality (U : Over S) {G H : Grp (Over T)}
    (p : G ⟶ H) (a : U ⟶ (baseChangedGroup f G).X) :
    (sectionsMulEquiv f U H).symm
        (a ≫ ((groupSchemeBaseChange f).functor.map p).hom.hom) =
      (sectionsMulEquiv f U G).symm a ≫ p.hom.hom := by
  apply (sectionsMulEquiv f U H).injective
  rw [MulEquiv.apply_symm_apply, sectionsMulEquiv_naturality, MulEquiv.apply_symm_apply]

/-- The universal kernel marking pulls back on all test schemes.
Source: scalar-extension subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
def kernelMarking {A G H : Grp (Over T)} {p : G ⟶ H}
    (m : KernelMarking A G H p) :
    KernelMarking (baseChangedGroup f A) (baseChangedGroup f G)
      (baseChangedGroup f H) ((groupSchemeBaseChange f).functor.map p) where
  inclusion := (groupSchemeBaseChange f).functor.map m.inclusion
  over := by
    let : GrpObj ((Over.pullback f).obj H.X) := ((Over.pullback f).mapGrp.obj H).grp
    change (Over.pullback f).map m.inclusion.hom.hom ≫
      (Over.pullback f).map p.hom.hom = 1
    rw [← Functor.map_comp, m.over, Functor.map_one]
  unique_lift {U} k hk := by
    have hk' : (sectionsMulEquiv f U G).symm k ≫ p.hom.hom = 1 := by
      rw [← sectionsMulEquiv_symm_naturality, hk, map_one]
    obtain ⟨a, ha, hu⟩ := m.unique_lift ((sectionsMulEquiv f U G).symm k) hk'
    refine ⟨sectionsMulEquiv f U A a, ?_, ?_⟩
    · change sectionsMulEquiv f U A a ≫
        ((groupSchemeBaseChange f).functor.map m.inclusion).hom.hom = k
      rw [← sectionsMulEquiv_naturality, ha, MulEquiv.apply_symm_apply]
    · intro b hb
      apply (sectionsMulEquiv f U A).symm.injective
      rw [MulEquiv.symm_apply_apply]
      apply hu
      rw [← sectionsMulEquiv_symm_naturality, hb]

/-- The actual origin of the pullback group has the original origin as its first projection.
Source: scalar-extension subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
@[reassoc (attr := simp)] theorem origin_fst (G : Grp (Over T)) :
    η[(baseChangedGroup f G).X].left ≫ pullback.fst G.X.hom f = f ≫ η[G.X].left := by
  have h := congrArg (fun a : Over.mk ((𝟙 S) ≫ f) ⟶ G.X => a.left)
    ((pullbackFiberMulEquiv f (𝟙 S) G).symm.map_one)
  rw [pullbackFiberMulEquiv_symm_apply_left] at h
  change (𝟙 S ≫ η[(baseChangedGroup f G).X].left) ≫ pullback.fst G.X.hom f =
    ((𝟙 S) ≫ f) ≫ η[G.X].left at h
  simpa only [Category.id_comp] using h

/-- The actual origin of the pullback group is a section of its structure map.
Source: scalar-extension subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
@[reassoc (attr := simp)] theorem origin_snd (G : Grp (Over T)) :
    η[(baseChangedGroup f G).X].left ≫ pullback.snd G.X.hom f = 𝟙 S :=
  Over.w η[(baseChangedGroup f G).X]

/-- Both origin projections identify it with the literal pullback lift.
Source: scalar-extension subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
theorem origin_eq_lift (G : Grp (Over T)) :
    η[(baseChangedGroup f G).X].left =
      pullback.lift (f ≫ η[G.X].left) (𝟙 S) (by
        rw [Category.assoc, Over.w, Over.tensorUnit_hom, Category.comp_id, Category.id_comp]) := by
  apply pullback.hom_ext
  · rw [origin_fst, pullback.lift_fst]
  · rw [origin_snd, pullback.lift_snd]

/-- Equality of a base-changed fibre with the fibre over its original point.
Source: scalar-extension subset of `K2-018#prop:k2018-integrality-test`, at the module snapshot. -/
def mapFiberEquiv {R : Scheme.{u}} (s : R ⟶ S) {G H : Grp (Over T)}
    (p : G ⟶ H) (y : Over.mk (s ≫ f) ⟶ H.X) :
    {x : Over.mk (s ≫ f) ⟶ G.X // x ≫ p.hom.hom = y} ≃
      {x : Over.mk s ⟶ (baseChangedGroup f G).X //
        x ≫ ((groupSchemeBaseChange f).functor.map p).hom.hom =
          pullbackFiberMulEquiv f s H y} where
  toFun x := ⟨pullbackFiberMulEquiv f s G x.1, by
    rw [← pullbackFiberMulEquiv_naturality, x.2]⟩
  invFun x := ⟨(pullbackFiberMulEquiv f s G).symm x.1, by
    apply (pullbackFiberMulEquiv f s H).injective
    rw [pullbackFiberMulEquiv_naturality, MulEquiv.apply_symm_apply, x.2]⟩
  left_inv x := by apply Subtype.ext; exact MulEquiv.symm_apply_apply _ _
  right_inv x := by apply Subtype.ext; exact MulEquiv.apply_symm_apply _ _

end General

end AlgebraicGeometry.Scheme.Group.BaseChange

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 3e5d7fe129a4cdd89462925fc6a1edb74826659d3c66a8972ddce6b82270d507.
Definitions, hypotheses and universes are retained modulo native names. -/
