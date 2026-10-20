/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Dimension.CodimensionTwoClosed
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Property
public import Aglib.AlgebraicGeometry.Modules.Exact
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeProperty
public import Aglib.CategoryTheory.SmallModel.Abelian
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Locality
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.FinitePresentation
public import Aglib.CategoryTheory.ExactCategory.MatrixDeflation
public import Aglib.CategoryTheory.ExactCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion
public import Aglib.AlgebraicGeometry.Modules.Coherent.AffineDetection
public import Aglib.AlgebraicGeometry.Modules.Pushforward.Isomorphism
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.FinitePushforward
public import Aglib.AlgebraicGeometry.Dimension.CodimensionTwo

public import
    Aglib.AlgebraicGeometry.Modules.Coherent.Pushforward.ClosedImmersion.GeneralPushforward

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Support.ClosedResidue` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`1e9f32d91ea2e673aa666d2c4a3fb33913a31556c5c450383ac76b179ab3f383`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules.Coherent.Support
open AlgebraicGeometry.Scheme.Modules.Coherent.Support
    AlgebraicGeometry.Scheme.Modules.Coherent.Support
open _root_.AlgebraicGeometry.Scheme.Modules (support)
open _root_.AlgebraicGeometry.Scheme.Modules.Coherent (coherentExactPullback coherentPullback)
open _root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent (FiniteTypeSheaves
    finiteTypeSheavesToModules)
attribute [local instance] Abelian.hasFiniteBiproducts Classical.decEq
attribute [local instance] Scheme.fromSpecStalk_flat
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Support
universe u
variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]

/-- Closedness is part of this exact index, not inferred from codimension. -/
instance closedResidueMap_isClosedImmersion (x : Scheme.CodimensionTwoClosedPoint X) :
    IsClosedImmersion (X.fromSpecResidueField x.1) :=
  isClosed_singleton_iff_isClosedImmersion.mp x.2.2

omit [IsIntegral X] in
/-- The actual residue closed pushforward has support in its original point. -/
theorem closedResiduePushforward_support (x : Scheme.CodimensionTwoClosedPoint X)
    (N : FiniteTypeSheaves (Spec (X.residueField x.1))) :
    support ((Scheme.Modules.QuasiCoherent.finiteTypePushforward
      (X.fromSpecResidueField x.1)).obj N).obj ⊆ {x.1} := by
  have hs := coherentPushforward_support_subset_image (X.fromSpecResidueField x.1) N
  intro y hy
  obtain ⟨z, _, hz⟩ := hs hy
  have hr : y ∈ Set.range (X.fromSpecResidueField x.1) := ⟨z, hz⟩
  rwa [Scheme.range_fromSpecResidueField] at hr

omit [IsIntegral X] in
/-- Actual closed-residue pushforward has zero coherent stalk-pullback at
every point to which the supporting closed point cannot specialize. -/
theorem closedResiduePushforward_stalkPullback_isZero (x : Scheme.CodimensionTwoClosedPoint X)
    (N : FiniteTypeSheaves (Spec (X.residueField x.1))) (y : X)
    (hxy : ¬ x.1 ⤳ y) :
    IsZero ((coherentPullback (X.fromSpecStalk y)).obj
      ((Scheme.Modules.QuasiCoherent.finiteTypePushforward
          (X.fromSpecResidueField x.1)).obj N)) := by
  apply IsZero.of_full_of_faithful_of_isZero (finiteTypeSheavesToModules _) _
  apply pullback_isZero_of_support
  intro z hz
  have heq : (X.fromSpecStalk y) z = x.1 := closedResiduePushforward_support X x N hz
  have hs : (X.fromSpecStalk y) z ⤳ y := by
    have hr : (X.fromSpecStalk y) z ∈ Set.range (X.fromSpecStalk y) := Set.mem_range_self z
    rwa [Scheme.range_fromSpecStalk] at hr
  exact hxy (heq ▸ hs)

omit [IsLocallyNoetherian X] in
/-- A closed point with local dimension two cannot specialize to the generic
point of an integral scheme. -/
theorem closedPoint_not_specializes_generic (x : Scheme.CodimensionTwoClosedPoint X) :
    ¬ x.1 ⤳ genericPoint X := by
  intro hs
  have heq : genericPoint X = x.1 := hs.mem_closed x.2.2 (Set.mem_singleton _)
  have hd : ringKrullDim (X.presheaf.stalk (genericPoint X)) = 0 := by
    change ringKrullDim X.functionField = 0
    simp
  have hx := x.2.1
  rw [← heq, hd] at hx
  norm_num at hx

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- A codimension-two closed point cannot specialize to a dimension-one
point; closedness forces equality and contradicts the two actual dimensions. -/
theorem closedPoint_not_specializes_heightOne (x : Scheme.CodimensionTwoClosedPoint X)
    (y : CodimensionOnePoint X) : ¬ x.1 ⤳ y.1 := by
  intro hs
  have heq : y.1 = x.1 := hs.mem_closed x.2.2 (Set.mem_singleton _)
  have hx := x.2.1
  rw [← heq, y.2] at hx
  norm_num at hx

/-- The original closed pushforward in the exact upper SmallModel used by
the support filtration and by the original public scheme G-groups. -/
def smallClosedResiduePushforward (x : Scheme.CodimensionTwoClosedPoint X) :
    _root_.CategoryTheory.ExactCategory.ExactFunctor
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (Coh (Spec (X.residueField x.1))))
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (Coh X)) :=
  _root_.CategoryTheory.SmallModel.mapAbelianExactFunctor
    (Scheme.Modules.Coherent.Pushforward.ClosedImmersion.coherentPushforwardExact
        (X.fromSpecResidueField x.1))

omit [IsIntegral X] in
/-- Original zero coherent pullback transfers by the canonical SmallModel
composition isomorphism, retaining the exact represented source object. -/
theorem smallClosedResidue_stalkPullback_isZero (x : Scheme.CodimensionTwoClosedPoint X)
    (N : Coh (Spec (X.residueField x.1))) (y : X) (hxy : ¬ x.1 ⤳ y) :
    (stalkPullback X y).toFunctor.kernel ((smallClosedResiduePushforward X x).toFunctor.obj N) := by
  have hz := closedResiduePushforward_stalkPullback_isZero X x
    ((equivSmallModel.{u + 1} (FiniteTypeSheaves (Spec (X.residueField x.1)))).inverse.obj N)
    y hxy
  have he := _root_.CategoryTheory.ExactCategory.ExactFunctor.smallModelCompIso.{u + 1}
    (Scheme.Modules.Coherent.Pushforward.ClosedImmersion.coherentPushforwardExact
        (X.fromSpecResidueField x.1))
    (coherentExactPullback (X.fromSpecStalk y))
  have hsmall : IsZero
      (((Scheme.Modules.Coherent.Pushforward.ClosedImmersion.coherentPushforwardExact
      (X.fromSpecResidueField x.1)).comp (coherentExactPullback (X.fromSpecStalk
          y))).smallModel.{u + 1}.toFunctor.obj N) :=
    (equivSmallModel.{u + 1} (FiniteTypeSheaves (Spec (X.presheaf.stalk y)))).functor.map_isZero hz
  exact hsmall.of_iso (he.app N).symm

/-- The original residue closed pushforward lands in actual positive support. -/
theorem closedResidue_lands_positive (x : Scheme.CodimensionTwoClosedPoint X)
    (N : Coh (Spec (X.residueField x.1))) :
    positiveSupport X ((smallClosedResiduePushforward X x).toFunctor.obj N) :=
  smallClosedResidue_stalkPullback_isZero X x N (genericPoint X)
    (closedPoint_not_specializes_generic X x)

/-- Exact residue closed pushforward with its proved first support landing. -/
def closedResidueToPositiveExact (x : Scheme.CodimensionTwoClosedPoint X) :
    _root_.CategoryTheory.ExactCategory.ExactFunctor
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (Coh (Spec (X.residueField x.1))))
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (CohOne X)) where
  toFunctor := (positiveSupport X).lift (smallClosedResiduePushforward X x).toFunctor
    (closedResidue_lands_positive X x)
  additive := {
    map_add := by
      intros
      apply ObjectProperty.hom_ext
      exact (smallClosedResiduePushforward X x).toFunctor.map_add }
  map_conflation S h := by
    have he := (smallClosedResiduePushforward X x).map_conflation S h
    exact { exact := Functor.reflects_exact_of_faithful (positiveSupport X).ι _ he.exact
            mono_f := (positiveSupport X).ι.mono_of_mono_map he.mono_f
            epi_g := (positiveSupport X).ι.epi_of_epi_map he.epi_g }

/-- The original residue closed pushforward also has the actual second
support property. No dimension bound or normality is required for this landing. -/
theorem closedResidue_lands_second (x : Scheme.CodimensionTwoClosedPoint X)
    (N : Coh (Spec (X.residueField x.1))) :
    secondSupport X ((closedResidueToPositiveExact X x).toFunctor.obj N) := by
  intro y
  exact smallClosedResidue_stalkPullback_isZero X x N y.1
    (closedPoint_not_specializes_heightOne X x y)

/-- Actual exact closed-residue pushforward into the actual second support
category, rather than an arbitrary map on its K-groups. -/
def closedResidueToSecondSupportExact (x : Scheme.CodimensionTwoClosedPoint X) :
    _root_.CategoryTheory.ExactCategory.ExactFunctor
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (Coh (Spec (X.residueField x.1))))
    (_root_.CategoryTheory.ObjectProperty.subcategoryExactStructure (secondSupport X)) where
  toFunctor := (secondSupport X).lift (closedResidueToPositiveExact X x).toFunctor
    (closedResidue_lands_second X x)
  additive := {
    map_add := by
      intros
      apply ObjectProperty.hom_ext
      exact (closedResidueToPositiveExact X x).toFunctor.map_add }
  map_conflation S h := by
    have he := (closedResidueToPositiveExact X x).map_conflation S h
    exact { exact := Functor.reflects_exact_of_faithful (secondSupport X).ι _ he.exact
            mono_f := (secondSupport X).ι.mono_of_mono_map he.mono_f
            epi_g := (secondSupport X).ι.epi_of_epi_map he.epi_g }

/-- The supported functor followed by its original two inclusions is exactly
the same upper-SmallModel closed pushforward. -/
theorem closedResidueToSecondSupport_comp_inclusions (x : Scheme.CodimensionTwoClosedPoint X) :
    (closedResidueToSecondSupportExact X x).toFunctor ⋙ (secondSupport X).ι ⋙
      (positiveSupport X).ι = (smallClosedResiduePushforward X x).toFunctor := rfl

/-- The first supported inclusion already recovers the same residue functor
into positive support, before the ambient coherent inclusion. -/
theorem closedResidueToSecondSupport_comp_firstInclusion (x : Scheme.CodimensionTwoClosedPoint X) :
    (closedResidueToSecondSupportExact X x).toFunctor ⋙ (secondSupport X).ι =
      (closedResidueToPositiveExact X x).toFunctor := rfl

end AlgebraicGeometry.Scheme.Modules.Coherent.Support
