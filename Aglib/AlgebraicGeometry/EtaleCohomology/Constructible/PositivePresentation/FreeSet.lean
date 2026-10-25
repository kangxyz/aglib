/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.EtaleRestriction
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.LocalSplitting
public import Aglib.AlgebraicGeometry.Morphisms.Etale.QuasiFinite
public import Aglib.CategoryTheory.Sites.Torsion.FinitePresentation.Generators
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Genuine positive-modulus free sheaves on finite etale covers

The sheafified free-abelian functor is the actual left adjoint to the
underlying-set sheaf functor. Adjunction uniqueness proves its compatibility
with inverse image and constant values. Its scalar quotient therefore
carries actual finite local trivializations whenever the set sheaf does,
for every nonzero modulus. Finite etale represented set sheaves supply
these trivializations by the proved geometric splitting construction.

The resulting coefficient is identified with the original free mod-n
representable. No compactness-to-constructibility implication is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf.TorsionFinitePresentation

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation

universe u

attribute [local instance] hasSheafifyLarge

/-- The actual sheafified free-abelian functor on original set sheaves. -/
def freeAbelianOfSet (X : Scheme.{u}) : SetSheaf X ⥤ AbelianSheaf.{u, u + 1} X :=
  Sheaf.composeAndSheafify X.smallEtaleTopology AddCommGrpCat.free.{u + 1}

/-- Its original free-forgetful adjunction. -/
def freeAbelianOfSetAdj (X : Scheme.{u}) :
    freeAbelianOfSet X ⊣ underlyingSetFunctor X :=
  Sheaf.adjunction X.smallEtaleTopology AddCommGrpCat.adj.{u + 1}

/-- Free abelian sheaves commute with the actual scheme inverse image. -/
def freeAbelianOfSetInverseImageIso {X S : Scheme.{u}} (f : S ⟶ X) :
    freeAbelianOfSet X ⋙ inverseImage f ≅ setInverseImage f ⋙ freeAbelianOfSet S :=
  ((freeAbelianOfSetAdj X).comp (inverseImageAdjunction f)).leftAdjointUniq
    ((setInverseImageAdjunction f).comp (freeAbelianOfSetAdj S))

/-- The free sheaf on an actual constant set sheaf has its original constant
free-abelian value, by the native constant adjunctions. -/
def freeAbelianOfSetConstantIso (X : Scheme.{u}) :
    constantSheaf X.smallEtaleTopology (Type (u + 1)) ⋙ freeAbelianOfSet X ≅
      AddCommGrpCat.free.{u + 1} ⋙ constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ((constantSheafAdj X.smallEtaleTopology (Type (u + 1))
    (etaleTerminalIsTerminal X)).comp (freeAbelianOfSetAdj X)).leftAdjointUniq
      (AddCommGrpCat.adj.{u + 1}.comp (constantAdjunction X))

/-- The original scalar quotient of the free sheaf on a set sheaf. -/
def freeZModOfSet (X : Scheme.{u}) (n : ℕ) (F : SetSheaf X) :
    AbelianSheaf.{u, u + 1} X :=
  cokernel (n • 𝟙 ((freeAbelianOfSet X).obj F))

/-- Actual set-sheaf isomorphisms induce the same scalar-quotient isomorphism. -/
def freeZModOfSetIso (X : Scheme.{u}) (n : ℕ) {F G : SetSheaf X} (e : F ≅ G) :
    freeZModOfSet X n F ≅ freeZModOfSet X n G :=
  cokernel.mapIso _ _ ((freeAbelianOfSet X).mapIso e) ((freeAbelianOfSet X).mapIso e)
    (by simp)

/-- Scalar quotients of free sheaves commute with the original inverse image,
using preservation of the actual cokernel. This includes modulus zero. -/
def freeZModOfSetInverseImageIso {X S : Scheme.{u}} (f : S ⟶ X) (n : ℕ)
    (F : SetSheaf X) :
    (inverseImage f).obj (freeZModOfSet X n F) ≅
      freeZModOfSet S n ((setInverseImage f).obj F) := by
  let e := (freeAbelianOfSetInverseImageIso f).app F
  exact PreservesCokernel.iso (inverseImage f) _ ≪≫
    cokernel.mapIso _ _ e e (by simp)

/-- The actual free mod-n value on a type of labels. -/
def freeZModValue (n : ℕ) (A : Type (u + 1)) : AddCommGrpCat.{u + 1} :=
  cokernel (n • 𝟙 (AddCommGrpCat.free.obj A))

/-- Finite labels have a finite original free mod-n additive value for
nonzero modulus; no invertibility condition on a scheme is involved. -/
theorem freeZModValue_finite (n : ℕ) (hn : n ≠ 0) (A : Type (u + 1)) [Finite A] :
    Finite (freeZModValue n A) := by
  have hfree : AddGroup.FG (FreeAbelianGroup A) := by
    apply AddGroup.fg_iff.mpr
    refine ⟨Set.range FreeAbelianGroup.of, ?_, Set.finite_range _⟩
    have hgen (a : FreeAbelianGroup A) :
        a ∈ AddSubgroup.closure (Set.range (FreeAbelianGroup.of : A → FreeAbelianGroup A)) := by
      induction a using FreeAbelianGroup.induction_on with
      | zero => exact AddSubgroup.zero_mem _
      | of a => exact AddSubgroup.subset_closure ⟨a, rfl⟩
      | neg a ha => exact AddSubgroup.neg_mem _ ha
      | add a b ha hb => exact AddSubgroup.add_mem _ ha hb
    exact top_unique (fun a _ => hgen a)
  let G := AddCommGrpCat.free.obj A
  have : AddGroup.FG G := hfree
  let f : G ⟶ G := n • 𝟙 G
  have : (AddMonoidHom.range f.hom).FiniteIndex := by
    change (nsmulAddMonoidHom n : G →+ G).range.FiniteIndex
    exact AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg G hn
  exact Finite.of_equiv (G ⧸ AddMonoidHom.range f.hom)
    (Iso.addCommGroupIsoToAddEquiv (AddCommGrpCat.cokernelIsoQuotient f).symm).toEquiv

/-- The scalar quotient on a constant set sheaf is the actual constant sheaf
of the displayed scalar-quotient value. -/
def freeZModOfSetConstantIso (X : Scheme.{u}) (n : ℕ) (A : Type (u + 1)) :
    freeZModOfSet X n ((constantSheaf X.smallEtaleTopology (Type (u + 1))).obj A) ≅
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (freeZModValue n A) := by
  let C := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let : C.IsLeftAdjoint := (constantAdjunction X).isLeftAdjoint
  let e := (freeAbelianOfSetConstantIso X).app A
  exact cokernel.mapIso _ (C.map (n • 𝟙 (AddCommGrpCat.free.obj A))) e e (by simp) ≪≫
    (PreservesCokernel.iso C _).symm

/-- A positive-modulus free sheaf on an actual finite locally constant set
sheaf has actual finite local trivializations with original inverse images. -/
theorem freeZModOfSet_isFiniteLocallyConstant (X : Scheme.{u}) (n : ℕ) (hn : n ≠ 0)
    {F : SetSheaf X} (hF : IsFiniteLocallyConstantSet F) :
    IsFiniteLocallyConstant (freeZModOfSet X n F) := by
  obtain ⟨t⟩ := hF
  refine ⟨{
    index := t.index
    chart := t.chart
    covers := t.covers
    value := fun i => freeZModValue n (t.value i)
    finite_value := ?_
    trivialization := fun i =>
      freeZModOfSetInverseImageIso (t.chart i).hom n F ≪≫
        freeZModOfSetIso _ n (t.trivialization i) ≪≫
        freeZModOfSetConstantIso _ n (t.value i) }⟩
  intro i
  have := t.finite_value i
  exact freeZModValue_finite n hn (t.value i)

/-- The original representable sheaf, expressed by native set sheafification. -/
def sheafifiedEtaleRepresentable (X : Scheme.{u}) (U : X.Etale) : SetSheaf X :=
  (presheafToSheaf X.smallEtaleTopology (Type (u + 1))).obj (uliftYoneda.{u + 1}.obj U)

/-- The free-abelian sheafification comparison retains the original native
free representable, rather than replacing its coefficient object. -/
def freeAbelianOfSetRepresentableIso (X : Scheme.{u}) (U : X.Etale) :
    (freeAbelianOfSet X).obj (sheafifiedEtaleRepresentable X U) ≅
      Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1, u, u + 1} X.smallEtaleTopology U :=
  (presheafToSheafCompComposeAndSheafifyIso
    X.smallEtaleTopology AddCommGrpCat.free.{u + 1}).app
    (uliftYoneda.{u + 1}.obj U)

/-- The actual original scalar-quotient representable is identified with the
scalar quotient of the sheafified set representable, for every modulus. -/
def freeZModRepresentableOfSetIso (X : Scheme.{u}) (n : ℕ) (U : X.Etale) :
    freeZModRepresentable.{u + 1} X.smallEtaleTopology n U ≅
      freeZModOfSet X n (sheafifiedEtaleRepresentable X U) :=
  cokernel.mapIso _ _ (freeAbelianOfSetRepresentableIso X U).symm
    (freeAbelianOfSetRepresentableIso X U).symm (by simp)

/-- The original finite-etale represented section presheaf is the native
lifted Yoneda presheaf on that same small-etale object. -/
def finiteEtaleRepresentablePresheafIso {X : Scheme.{u}} (Y : Scheme.FiniteEtale X) :
    uliftYoneda.{u + 1}.obj ((Scheme.FiniteEtale.toEtale X).obj Y) ≅
      (finiteRepresentedSetSheaf Y).obj :=
  NatIso.ofComponents (fun U =>
    (Equiv.ulift.trans
      ((Functor.FullyFaithful.ofFullyFaithful (Scheme.Etale.forget X)).homEquiv.trans
        Equiv.ulift.symm)).toIso)
    (by
      intro U V f
      ext a
      apply ULift.ext
      exact (Scheme.Etale.forget X).map_comp f.unop a.down)

/-- Sheafification recovers the original finite-etale represented set sheaf. -/
def sheafifiedFiniteEtaleRepresentableIso {X : Scheme.{u}} (Y : Scheme.FiniteEtale X) :
    sheafifiedEtaleRepresentable X ((Scheme.FiniteEtale.toEtale X).obj Y) ≅
      finiteRepresentedSetSheaf Y :=
  (presheafToSheaf X.smallEtaleTopology (Type (u + 1))).mapIso
      (finiteEtaleRepresentablePresheafIso Y) ≪≫
    asIso ((sheafificationAdjunction X.smallEtaleTopology (Type (u + 1))).counit.app
      (finiteRepresentedSetSheaf Y))

/-- The actual free positive-modulus coefficient on a finite-etale object is
finite locally constant on every scheme, including empty bases and rank zero. -/
theorem finiteEtale_freeZModRepresentable_isFiniteLocallyConstant
    {X : Scheme.{u}} (Y : Scheme.FiniteEtale X) (n : ℕ) (hn : n ≠ 0) :
    IsFiniteLocallyConstant (freeZModRepresentable.{u + 1} X.smallEtaleTopology n
      ((Scheme.FiniteEtale.toEtale X).obj Y)) := by
  let e := freeZModRepresentableOfSetIso X n ((Scheme.FiniteEtale.toEtale X).obj Y) ≪≫
    freeZModOfSetIso X n (sheafifiedFiniteEtaleRepresentableIso Y)
  exact (isFiniteLocallyConstant_iff_of_iso e).mpr
    (freeZModOfSet_isFiniteLocallyConstant X n hn
      (Scheme.FiniteEtale.finiteRepresentedSetSheaf_isFiniteLocallyConstant Y))

/-- The original finite-etale free generators are geometrically constructible
at every positive modulus, with no scheme Noetherian or order-unit condition. -/
theorem finiteEtale_freeZModRepresentable_isConstructible
    {X : Scheme.{u}} (Y : Scheme.FiniteEtale X) (n : ℕ) (hn : n ≠ 0) :
    IsConstructible (freeZModRepresentable.{u + 1} X.smallEtaleTopology n
      ((Scheme.FiniteEtale.toEtale X).obj Y)) :=
  isConstructible_of_isFiniteLocallyConstant
    (finiteEtale_freeZModRepresentable_isFiniteLocallyConstant Y n hn)

/-- An isomorphism of original etale test objects transports the actual free
scalar-quotient generators. -/
def freeZModRepresentableIsoOfEtaleIso {X : Scheme.{u}} (n : ℕ) {U V : X.Etale}
    (e : U ≅ V) :
    freeZModRepresentable.{u + 1} X.smallEtaleTopology n U ≅
      freeZModRepresentable.{u + 1} X.smallEtaleTopology n V :=
  cokernel.mapIso _ _
    ((Sheaf.Hypercohomology.freeAbelianSheafFunctor.{u + 1, u, u + 1}
      X.smallEtaleTopology).mapIso e)
    ((Sheaf.Hypercohomology.freeAbelianSheafFunctor.{u + 1, u, u + 1}
      X.smallEtaleTopology).mapIso e)
    (by simp)

/-- Finiteness of an original etale structural map supplies the genuine
geometric free-generator theorem, without altering that original object. -/
theorem freeZModRepresentable_isFiniteLocallyConstant_of_isFinite
    {X : Scheme.{u}} (U : X.Etale) [IsFinite U.hom] (n : ℕ) (hn : n ≠ 0) :
    IsFiniteLocallyConstant (freeZModRepresentable.{u + 1} X.smallEtaleTopology n U) := by
  let Y : Scheme.FiniteEtale X := Scheme.FiniteEtale.mk U.hom
  let e : U ≅ (Scheme.FiniteEtale.toEtale X).obj Y :=
    MorphismProperty.Over.isoMk (Iso.refl U.left) (by
      change 𝟙 U.left ≫ U.hom = U.hom
      exact Category.id_comp _)
  exact (isFiniteLocallyConstant_iff_of_iso (freeZModRepresentableIsoOfEtaleIso n e)).mpr
    (finiteEtale_freeZModRepresentable_isFiniteLocallyConstant Y n hn)

/-- Over a locally Artinian quasi-separated base, every qc original etale
object is finite. Its positive-modulus free generator is therefore finite
locally constant. In particular this applies to all original affine-etale
generators on an Artinian qcqs scheme. -/
theorem locallyArtinian_freeZModRepresentable_isFiniteLocallyConstant
    {X : Scheme.{u}} [IsLocallyArtinian X] [QuasiSeparatedSpace X]
    (U : X.Etale) [CompactSpace U.left] (n : ℕ) (hn : n ≠ 0) :
    IsFiniteLocallyConstant (freeZModRepresentable.{u + 1} X.smallEtaleTopology n U) := by
  have : QuasiCompact U.hom :=
    quasiCompact_of_compactSpace (X := U.left) (Y := X) U.hom
  have : IsFinite U.hom :=
    IsFinite.of_locallyQuasiFinite (X := U.left) (Y := X) U.hom
  exact freeZModRepresentable_isFiniteLocallyConstant_of_isFinite U n hn

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
