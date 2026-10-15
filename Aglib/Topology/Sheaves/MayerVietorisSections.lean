/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Topology.Sheaves.MayerVietoris
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
/-!
# Actual Mayer--Vietoris sequences of section complexes

For a complex of sheaves valued in an abelian category, the original
restriction square on two opens is a pullback of complexes. Its section-sum
and section-difference sequence is exact, and is short exact when every term
is flasque. Shrinking the two opens gives a morphism of these same sequences.

The final theorem gives the sharp two-open upper cohomological bound from
bounds on the two opens and their intersection. No exactness of global
sections on arbitrary sheaves is assumed. The coefficient category admits
sheafification; the space and complex may be arbitrary.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

namespace TopCat.Sheaf
variable {X : TopCat.{u}} {A : Type v} [Category.{u} A] [Abelian A]
  [HasSheafify (Opens.grothendieckTopology X) A]

/-- Actual evaluation of a sheaf on the indicated open. -/
def sectionsFunctor (U : Opens X) : TopCat.Sheaf A X ⥤ A :=
  sheafToPresheaf (Opens.grothendieckTopology X) A ⋙ (evaluation _ A).obj (op U)

instance (U : Opens X) : (sectionsFunctor (A := A) U).Additive where
  map_add := by intros; rfl

/-- The original restriction natural transformation between section functors. -/
def sectionsRestriction {U V : Opens X} (h : U ≤ V) :
    sectionsFunctor (A := A) V ⟶ sectionsFunctor U where
  app F := F.obj.map (homOfLE h).op
  naturality {_ _} f := (f.hom.naturality (homOfLE h).op).symm

/-- Sections of an original sheaf complex. -/
abbrev sectionsComplex (K : CochainComplex (TopCat.Sheaf A X) ℤ) (U : Opens X) :=
  ((sectionsFunctor U).mapHomologicalComplex (.up ℤ)).obj K

/-- Original restriction as a chain map on section complexes. -/
def sectionsComplexRestriction (K : CochainComplex (TopCat.Sheaf A X) ℤ)
    {U V : Opens X} (h : U ≤ V) : sectionsComplex K V ⟶ sectionsComplex K U :=
  (NatTrans.mapHomologicalComplex (sectionsRestriction h) (.up ℤ)).app K

@[simp]
lemma sectionsComplexRestriction_f (K : CochainComplex (TopCat.Sheaf A X) ℤ)
    {U V : Opens X} (h : U ≤ V) (n : ℤ) :
    (sectionsComplexRestriction K h).f n = (K.X n).obj.map (homOfLE h).op := rfl

@[reassoc (attr := simp)]
lemma sectionsComplexRestriction_comp (K : CochainComplex (TopCat.Sheaf A X) ℤ)
    {U V W : Opens X} (h : U ≤ V) (k : V ≤ W) :
    sectionsComplexRestriction K k ≫ sectionsComplexRestriction K h =
      sectionsComplexRestriction K (h.trans k) := by
  ext n
  simp only [HomologicalComplex.comp_f, sectionsComplexRestriction_f, ←
    CategoryTheory.Functor.map_comp]
  rfl

/-- The original two-open section square is a pullback of actual complexes. -/
lemma sectionsComplex_isPullback (K : CochainComplex (TopCat.Sheaf A X) ℤ)
    (U V : Opens X) :
    IsPullback (sectionsComplexRestriction K (le_sup_left : U ≤ U ⊔ V))
      (sectionsComplexRestriction K (le_sup_right : V ≤ U ⊔ V))
      (sectionsComplexRestriction K (inf_le_left : U ⊓ V ≤ U))
      (sectionsComplexRestriction K (inf_le_right : U ⊓ V ≤ V)) := by
  have hw : sectionsComplexRestriction K (le_sup_left : U ≤ U ⊔ V) ≫
      sectionsComplexRestriction K (inf_le_left : U ⊓ V ≤ U) =
      sectionsComplexRestriction K (le_sup_right : V ≤ U ⊔ V) ≫
      sectionsComplexRestriction K (inf_le_right : U ⊓ V ≤ V) := by simp
  refine ⟨⟨hw⟩, ⟨HomologicalComplex.isLimitOfEval _ _ (fun n => ?_)⟩⟩
  refine (isLimitMapConePullbackConeEquiv (HomologicalComplex.eval A (.up ℤ) n) hw).symm ?_
  exact ((Opens.mayerVietorisSquare U V).sheafCondition_of_sheaf (K.X n)).isLimit

/-- The actual Mayer--Vietoris short complex, with restriction sum and difference. -/
def sectionsMayerVietoris (K : CochainComplex (TopCat.Sheaf A X) ℤ) (U V : Opens X) :
    ShortComplex (CochainComplex A ℤ) := (sectionsComplex_isPullback K U V).shortComplex'

lemma sectionsMayerVietoris_exact (K : CochainComplex (TopCat.Sheaf A X) ℤ)
    (U V : Opens X) : (sectionsMayerVietoris K U V).Exact :=
  (sectionsComplex_isPullback K U V).exact_shortComplex'

/-- Flasque terms make the original difference map epic, hence the actual
Mayer--Vietoris sequence is short exact in complexes. -/
lemma sectionsMayerVietoris_shortExact (K : CochainComplex (TopCat.Sheaf A X) ℤ)
    (U V : Opens X) [∀ n, TopCat.Presheaf.IsFlasque (K.X n).obj] :
    (sectionsMayerVietoris K U V).ShortExact := by
  have : Epi (sectionsComplexRestriction K (inf_le_left : U ⊓ V ≤ U)) := by
    apply HomologicalComplex.epi_of_epi_f
    intro n
    change Epi ((K.X n).obj.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op)
    infer_instance
  have : Epi (sectionsMayerVietoris K U V).g :=
    epi_of_epi_fac (biprod.inl_desc (sectionsComplexRestriction K (inf_le_left : U ⊓ V ≤ U))
      (-sectionsComplexRestriction K (inf_le_right : U ⊓ V ≤ V)))
  have : Mono (sectionsMayerVietoris K U V).f :=
    (sectionsComplex_isPullback K U V).mono_shortComplex'_f
  exact { exact := sectionsMayerVietoris_exact K U V }

/-- Shrinking both opens gives a morphism of the original Mayer--Vietoris
short complexes, with literal restriction maps in all three positions. -/
def sectionsMayerVietorisRestriction (K : CochainComplex (TopCat.Sheaf A X) ℤ)
    {U V U' V' : Opens X} (hU : U' ≤ U) (hV : V' ≤ V) :
    sectionsMayerVietoris K U V ⟶ sectionsMayerVietoris K U' V' where
  τ₁ := sectionsComplexRestriction K (sup_le_sup hU hV)
  τ₂ := biprod.map (sectionsComplexRestriction K hU) (sectionsComplexRestriction K hV)
  τ₃ := sectionsComplexRestriction K (inf_le_inf hU hV)
  comm₁₂ := by
    dsimp [sectionsMayerVietoris, CommSq.shortComplex']
    apply biprod.hom_ext <;> simp
  comm₂₃ := by
    dsimp [sectionsMayerVietoris, CommSq.shortComplex']
    apply biprod.hom_ext' <;> simp

/-- The sharp two-open cohomological bound: the union is bounded by n if
both opens are bounded by n and their intersection is bounded by n-1. -/
lemma sectionsComplex_isLE_sup (K : CochainComplex (TopCat.Sheaf A X) ℤ)
    (U V : Opens X) [∀ i, TopCat.Presheaf.IsFlasque (K.X i).obj] (n : ℤ)
    [CochainComplex.IsLE (sectionsComplex K U) n]
    [CochainComplex.IsLE (sectionsComplex K V) n]
    [CochainComplex.IsLE (sectionsComplex K (U ⊓ V)) (n - 1)] :
    CochainComplex.IsLE (sectionsComplex K (U ⊔ V)) n := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  rw [exactAt_iff_isZero_homology]
  let S := sectionsMayerVietoris K U V
  have hS := sectionsMayerVietoris_shortExact K U V
  apply (hS.homology_exact₁ (i-1) i (by dsimp; omega)).isZero_X₂
  · exact (CochainComplex.isZero_of_isLE (sectionsComplex K (U ⊓ V))
      (n - 1) (i-1) (by omega)).eq_of_src _ _
  · have hz : IsZero (S.X₂.homology i) := by
      let H := homologyFunctor A (.up ℤ) i
      exact ((biprod_isZero_iff _ _).mpr
        ⟨CochainComplex.isZero_of_isLE (sectionsComplex K U) n i hi,
          CochainComplex.isZero_of_isLE (sectionsComplex K V) n i hi⟩).of_iso
        (H.mapBiprod (sectionsComplex K U) (sectionsComplex K V))
    exact hz.eq_of_tgt _ _

end TopCat.Sheaf
