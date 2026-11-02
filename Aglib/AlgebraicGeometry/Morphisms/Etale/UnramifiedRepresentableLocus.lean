/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Etale.PointwiseSource
public import Aglib.AlgebraicGeometry.Morphisms.Etale.FiniteStalkNeighborhood
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # The original small-etale representable of an unramified scheme

Every map from an etale test scheme into an unramified scheme factors uniquely
through its actual source etale locus. This concerns the restricted Yoneda
presheaf, not the geometric fibres of the original morphism. In particular it
makes no assertion that inverse image along a closed immersion is represented
by the corresponding base change of a non-etale scheme.

The Noetherian hypothesis is the explicit guard of the existing pointwise
source-descent theorem. No finiteness, flatness, or group structure of the
original unramified morphism is supplied or concluded.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {K S : Scheme.{u}} [IsLocallyNoetherian S]
  (f : K ⟶ S) [LocallyOfFinitePresentation f] [FormallyUnramified f]

/-- An etale test map into the original unramified scheme lands in its
actual etale locus. Source descent is applied at each original point. -/
theorem range_le_etaleSourceOpen_of_etale_comp {U : Scheme.{u}}
    (a : U ⟶ K) [Etale (a ≫ f)] :
    Set.range a ⊆ (f.etaleSourceOpen : Set K) := by
  let : Etale a := Etale.of_comp a f
  rintro _ ⟨u, rfl⟩
  exact etaleAt_of_etale_source_of_noetherian a f u

omit [IsLocallyNoetherian S] [LocallyOfFinitePresentation f] [FormallyUnramified f] in
/-- The actual restriction of the structural map to its source etale locus. -/
theorem etale_etaleSourceOpen : Etale (f.etaleSourceOpen.ι ≫ f) := by
  apply etale_of_forall_etaleAt
  intro x
  exact etaleAt.comp_openImmersion f f.etaleSourceOpen.ι x x.property

/-- The same etale locus, now as an object of the original small-etale site. -/
def etaleLocusObject : S.Etale :=
  letI := etale_etaleSourceOpen f
  Scheme.Etale.mk (f.etaleSourceOpen.ι ≫ f)

/-- The original open immersion as a morphism over the unchanged base. -/
def etaleLocusInclusion :
    (Scheme.Etale.forget S).obj (etaleLocusObject f) ⟶ Over.mk f :=
  Over.homMk f.etaleSourceOpen.ι rfl

/-- On every original etale test, postcomposition by the original locus
inclusion is a bijection. Its inverse is the actual open-immersion lift. -/
def etaleLocusHomEquiv (U : S.Etale) :
    ((Scheme.Etale.forget S).obj U ⟶
      (Scheme.Etale.forget S).obj (etaleLocusObject f)) ≃
    ((Scheme.Etale.forget S).obj U ⟶ Over.mk f) where
  toFun a := a ≫ etaleLocusInclusion f
  invFun a := by
    have ha : a.left ≫ f = U.hom := Over.w a
    have : Etale (a.left ≫ f) := by rw [ha]; infer_instance
    have hr : Set.range a.left ⊆ Set.range f.etaleSourceOpen.ι := by
      rw [Scheme.Opens.range_ι]
      exact range_le_etaleSourceOpen_of_etale_comp f a.left
    change Over.mk U.hom ⟶ Over.mk (f.etaleSourceOpen.ι ≫ f)
    refine Over.homMk (IsOpenImmersion.lift f.etaleSourceOpen.ι a.left hr) ?_
    change IsOpenImmersion.lift f.etaleSourceOpen.ι a.left hr ≫
      (f.etaleSourceOpen.ι ≫ f) = U.hom
    rw [← Category.assoc, IsOpenImmersion.lift_fac, ha]
  left_inv a := by
    apply Over.OverMorphism.ext
    apply (cancel_mono f.etaleSourceOpen.ι).mp
    change IsOpenImmersion.lift f.etaleSourceOpen.ι
      (a.left ≫ f.etaleSourceOpen.ι) _ ≫ f.etaleSourceOpen.ι =
        a.left ≫ f.etaleSourceOpen.ι
    exact IsOpenImmersion.lift_fac _ _ _
  right_inv a := by
    apply Over.OverMorphism.ext
    exact IsOpenImmersion.lift_fac _ _ _

/-- The ordinary restricted Yoneda presheaves are identified by the same
open inclusion, before any universe lift or sheafification. -/
def etaleLocusRestrictedYonedaIso :
    (Scheme.Etale.forget S).op ⋙
        yoneda.obj ((Scheme.Etale.forget S).obj (etaleLocusObject f)) ≅
      (Scheme.Etale.forget S).op ⋙ yoneda.obj (Over.mk f) :=
  NatIso.ofComponents (fun U => (etaleLocusHomEquiv f U.unop).toIso)
    (by
      intro U V a
      ext b
      change (((Scheme.Etale.forget S).map a.unop ≫ b) ≫ etaleLocusInclusion f) =
        (Scheme.Etale.forget S).map a.unop ≫ (b ≫ etaleLocusInclusion f)
      exact Category.assoc _ _ _)

/-- In the original coefficient universe, the original small-etale
representable of an unramified scheme is the lifted Yoneda presheaf of its
same etale locus. All maps remain postcomposition by the actual inclusion. -/
def etaleLocusUliftYonedaIso :
    uliftYoneda.{u + 1}.obj (etaleLocusObject f) ≅
      (Scheme.Etale.forget S).op ⋙ yoneda.obj (Over.mk f) ⋙ uliftFunctor.{u + 1} := by
  let e : uliftYoneda.{u + 1}.obj (etaleLocusObject f) ≅
      (Scheme.Etale.forget S).op ⋙
        yoneda.obj ((Scheme.Etale.forget S).obj (etaleLocusObject f)) ⋙
          uliftFunctor.{u + 1} :=
    NatIso.ofComponents
      (fun U => ((Equiv.ulift.trans
        ((Functor.FullyFaithful.ofFullyFaithful (Scheme.Etale.forget S)).homEquiv
          (X := U.unop) (Y := etaleLocusObject f))).trans Equiv.ulift.symm).toIso)
      (by
        intro U V a
        ext b
        exact congrArg ULift.up ((Scheme.Etale.forget S).map_comp a.unop b.down))
  exact e ≪≫ Functor.isoWhiskerRight (etaleLocusRestrictedYonedaIso f) uliftFunctor.{u + 1}

end AlgebraicGeometry.Scheme.Hom
