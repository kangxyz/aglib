/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.DisjointSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleRestrictionUnit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # The original sheaf on a scheme coproduct

The original inverse-image units are the product projections. The proof uses
actual restrictions on disjoint pullback charts, not a cohomology or stalk model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

universe u

attribute [local instance] hasSheafifyLarge

variable {I : Type u} (Y : I → Scheme.{u})

/-- Each actual coproduct component is closed as well as open. -/
theorem sigmaComponent_isClosedImmersion (i : I) : IsClosedImmersion (Sigma.ι Y i) := by
  apply IsClosedImmersion.of_isPreimmersion
  have hcomp : (Set.range (Sigma.ι Y i))ᶜ =
      ⋃ j : {j : I // j ≠ i}, Set.range (Sigma.ι Y j.val) := by
    ext x
    constructor
    · intro hx
      obtain ⟨⟨j, y⟩, rfl⟩ := (sigmaMk Y).surjective x
      have hj : j ≠ i := by
        rintro rfl
        exact hx ⟨y, (sigmaMk_mk Y j y).symm⟩
      exact Set.mem_iUnion.mpr ⟨⟨j, hj⟩, y, (sigmaMk_mk Y j y).symm⟩
    · intro hx hi
      obtain ⟨j, y, hy⟩ := Set.mem_iUnion.mp hx
      obtain ⟨z, hz⟩ := hi
      have h := (sigmaι_eq_iff Y j.val i y z).mp (hy.trans hz.symm)
      exact j.property (congrArg Sigma.fst h)
  rw [← isOpen_compl_iff, hcomp]
  exact isOpen_iUnion (fun j => (Sigma.ι Y j.val).isOpenEmbedding.isOpen_range)

/-- The component map is finite; no finiteness of the index is needed. -/
theorem sigmaComponent_isFinite (i : I) : IsFinite (Sigma.ι Y i) := by
  let := sigmaComponent_isClosedImmersion Y i
  infer_instance

/-- The original pullback component as a test object over the coproduct. -/
abbrev componentTest (U : (∐ Y).Etale) (i : I) : (∐ Y).Etale :=
  (siteEtalePostcompose (Sigma.ι Y i)).obj ((siteBaseChange (Sigma.ι Y i)).obj U)

/-- Its original restriction arrow is the site-adjunction counit. -/
abbrev componentTestInclusion (U : (∐ Y).Etale) (i : I) :
    componentTest Y U i ⟶ U :=
  (siteEtalePostcomposeAdj (Sigma.ι Y i)).counit.app U

instance componentTestInclusion_mono (U : (∐ Y).Etale) (i : I) :
    Mono (componentTestInclusion Y U i) := by
  apply Functor.mono_of_mono_map (Etale.forget (∐ Y) ⋙ Over.forget (∐ Y))
  exact inferInstanceAs (Mono (pullback.fst U.hom (Sigma.ι Y i)))

/-- Base changing the actual component cover still covers every original test. -/
theorem componentTest_cover (U : (∐ Y).Etale) :
    Sieve.ofArrows (componentTest Y U) (componentTestInclusion Y U) ∈
      (∐ Y).smallEtaleTopology U := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  ext x
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  obtain ⟨⟨i, y⟩, hy⟩ := (sigmaMk Y).surjective (U.hom x)
  have hxy : U.hom x = Sigma.ι Y i y :=
    hy.symm.trans (sigmaMk_mk Y i y)
  obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback U.hom (Sigma.ι Y i)) x y hxy
  exact ⟨i, z, hz⟩

/-- Distinct pullback component charts remain disjoint. -/
theorem componentTest_disjoint (U : (∐ Y).Etale) (i j : I) (hij : i ≠ j)
    (Z : (∐ Y).Etale) (a : Z ⟶ componentTest Y U i)
    (b : Z ⟶ componentTest Y U j)
    (h : a ≫ componentTestInclusion Y U i = b ≫ componentTestInclusion Y U j) :
    IsEmpty Z.left := by
  apply isEmpty_of_commSq_sigmaι_of_ne (g := Y)
    (a := a.left ≫ pullback.snd U.hom (Sigma.ι Y i))
    (b := b.left ≫ pullback.snd U.hom (Sigma.ι Y j)) _ hij
  constructor
  have hab : a.left ≫ pullback.fst U.hom (Sigma.ι Y i) =
      b.left ≫ pullback.fst U.hom (Sigma.ι Y j) :=
    congrArg (fun k : Z ⟶ U => k.left) h
  calc
    (a.left ≫ pullback.snd U.hom (Sigma.ι Y i)) ≫ Sigma.ι Y i =
        (a.left ≫ pullback.fst U.hom (Sigma.ι Y i)) ≫ U.hom := by
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun z => a.left ≫ z)
          (pullback.condition (f := U.hom) (g := Sigma.ι Y i)).symm).trans
          (Category.assoc _ _ _).symm)
    _ = (b.left ≫ pullback.fst U.hom (Sigma.ι Y j)) ≫ U.hom := by rw [hab]
    _ = (b.left ≫ pullback.snd U.hom (Sigma.ι Y j)) ≫ Sigma.ι Y j := by
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun z => b.left ≫ z)
          (pullback.condition (f := U.hom) (g := Sigma.ι Y j))).trans
          (Category.assoc _ _ _).symm)

variable (F : AbelianSheaf.{u, u + 1} (∐ Y))

/-- The same inverse-image/direct-image objects, without replacing coefficients. -/
abbrev componentImage (i : I) : AbelianSheaf.{u, u + 1} (∐ Y) :=
  (directImage (Sigma.ι Y i)).obj ((inverseImage (Sigma.ι Y i)).obj F)

/-- The fan whose projections are precisely the original adjunction units. -/
def coproductUnitFan : Fan (componentImage Y F) :=
  Fan.mk F (fun i => (inverseImageAdjunction (Sigma.ι Y i)).unit.app F)

/-- The evaluated original unit fan is a limit on every actual etale test. -/
def coproductUnitSectionsIsLimit (U : (∐ Y).Etale) :
    IsLimit (Fan.mk (F.obj.obj (op U))
      (fun i => ((inverseImageAdjunction (Sigma.ι Y i)).unit.app F).hom.app (op U))) := by
  let D := disjointSectionsFanIsLimit F (componentTestInclusion Y U)
    (componentTest_cover Y U) (componentTest_disjoint Y U)
  let e (i : I) : (componentImage Y F i).obj.obj (op U) ≅
      F.obj.obj (op (componentTest Y U i)) :=
    ((CategoryTheory.evaluation _ _).obj
      (op ((siteBaseChange (Sigma.ι Y i)).obj U))).mapIso
        ((sheafToPresheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso
          ((inverseImageEtaleIso (Sigma.ι Y i)).app F))
  have hu (i : I) :
      ((inverseImageAdjunction (Sigma.ι Y i)).unit.app F).hom.app (op U) ≫
        (e i).hom = F.obj.map (componentTestInclusion Y U i).op :=
    inverseImageEtaleIso_unit_app (Sigma.ι Y i) F U
  refine Fan.IsLimit.mk _
    (fun s => D.lift (Fan.mk s.pt (fun i => s.proj i ≫ (e i).hom))) ?_ ?_
  · intro s i
    apply (cancel_mono (e i).hom).mp
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => D.lift (Fan.mk s.pt (fun i => s.proj i ≫ (e i).hom)) ≫ z)
        (hu i)).trans (D.fac (Fan.mk s.pt (fun i => s.proj i ≫ (e i).hom)) ⟨i⟩))
  · intro s m hm
    apply D.hom_ext
    intro i
    change m ≫ F.obj.map (componentTestInclusion Y U i.as).op = _
    exact (congrArg (fun z => m ≫ z) (hu i.as).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun z => z ≫ (e i.as).hom) (hm i.as)).trans
          (D.fac (Fan.mk s.pt (fun i => s.proj i ≫ (e i).hom)) i).symm))

/-- The actual sheaf is the product of its component direct images. -/
def coproductUnitFanIsLimit : IsLimit (coproductUnitFan Y F) := by
  apply isLimitOfReflects (sheafToPresheaf (∐ Y).smallEtaleTopology AddCommGrpCat.{u + 1})
  apply (Fan.isLimitMapConeEquiv
    (sheafToPresheaf (∐ Y).smallEtaleTopology AddCommGrpCat.{u + 1}) _ _).symm.toFun
  apply evaluationJointlyReflectsLimits
  intro U
  apply (Fan.isLimitMapConeEquiv ((CategoryTheory.evaluation _ _).obj U) _ _).symm.toFun
  exact coproductUnitSectionsIsLimit Y F U.unop

/-- Canonical product decomposition of the original sheaf, including empty index. -/
def coproductSheafIso : F ≅ ∏ᶜ componentImage Y F :=
  (coproductUnitFanIsLimit Y F).conePointUniqueUpToIso (productIsProduct _)

@[reassoc (attr := simp)]
theorem coproductSheafIso_hom_π (i : I) :
    (coproductSheafIso Y F).hom ≫ Pi.π (componentImage Y F) i =
      (inverseImageAdjunction (Sigma.ι Y i)).unit.app F :=
  (coproductUnitFanIsLimit Y F).conePointUniqueUpToIso_hom_comp (productIsProduct _) ⟨i⟩

/-- The canonical comparison is literally the product of the original units. -/
theorem coproductSheafIso_hom :
    (coproductSheafIso Y F).hom =
      Pi.lift (fun i => (inverseImageAdjunction (Sigma.ι Y i)).unit.app F) := by
  apply Pi.hom_ext
  intro i
  exact (coproductSheafIso_hom_π Y F i).trans
    (Pi.lift_comp_π (fun i => (inverseImageAdjunction (Sigma.ι Y i)).unit.app F) i).symm

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
