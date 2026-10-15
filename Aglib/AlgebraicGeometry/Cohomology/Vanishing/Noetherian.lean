/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Support.Finite
public import Mathlib.AlgebraicGeometry.Artinian
public import Aglib.Topology.Sheaves.ClosedSupport
public import Aglib.Topology.Sheaves.Godement
public import Aglib.Topology.Sheaves.SupportedAway
public import Aglib.Topology.KrullDimension.ClosedSubspace
public import Aglib.AlgebraicGeometry.Cohomology.Affine.SheafCohomology
public import Mathlib.Topology.Sober
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Aglib.AlgebraicGeometry.Cohomology.Vanishing.Basic
/-!
# Cohomological dimension of Noetherian schemes

Every abelian sheaf on a Noetherian scheme of topological Krull dimension at
most `d` has zero actual Ext-defined cohomology in degrees greater than `d`.
The endpoint proves the original `NoetherianSheafCohomologyVanishing` family
from `Vanishing.Basic`, for every universe and without any quasicoherence,
properness, finite-generation, irreducibility, or reducedness assumption.

The dimension-zero base case uses the native Artinian/discrete-space results.
The induction maps a sheaf to the finite sum of skyscrapers at all component
generic points. Its kernel and cokernel have zero generic stalks. Each is the
filtered union of subsheaves supported on closed subsets avoiding all those
generic points. Closed support lowers dimension; exact closed pushforward and
filtered-colimit stability of positive cohomological vanishing finish the
induction using the original long exact sequence.

The general vanishing statement is Stacks 02UZ (Proposition 20.20.7), inspected
2026-10-14. The filtered-colimit input follows the finite-cover argument of
Stacks 009F. All load-bearing support and comparison statements are proved in
this file and `R5Lab.CategoryTheory.Sheaves.NoetherianCohomology`, using Mathlib
revision `d13f23b723b8a846827a245b89c10fc7d3f11612` and project snapshot
`3397a339b6a52fbba586dae127aa729d873b771d`.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.NoetherianDimension` at R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

/-- Any abelian sheaf on a scheme with finitely many points, all closed, has
vanishing actual cohomology in every positive degree. -/
theorem sheafCohomology_positive_of_finite_points
    (X : Scheme.{u}) [Finite X] [T1Space X]
    (M : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Subsingleton (Sheaf.H M (n + 1)) := by
  classical
  let := Fintype.ofFinite X
  let e : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm
  exact finiteClosedSupportCohomology_positive X e e.injective
    (fun _ => isClosed_singleton) M
    (fun x hx => False.elim (hx (e.surjective x))) n

/-- The dimension-zero case of Noetherian vanishing, for arbitrary abelian
coefficients and the original Ext-defined `Sheaf.H`. -/
theorem noetherianSheafCohomology_vanishing_of_dim_le_zero
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hdim : topologicalKrullDim X ≤ 0) (n : ℕ) (hn : 0 < n) :
    Subsingleton (Sheaf.H M n) := by
  let := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  let : Finite X := NoetherianSpace.finite
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact sheafCohomology_positive_of_finite_points X M m

end AlgebraicGeometry.Scheme.Cohomology

/-! ## Cohomological vanishing under filtered colimits

The scheme-specialized filtered-colimit theorem uses flasque acyclicity for
the actual `Sheaf.H` from `Affine.SheafCohomology`. It supplies the colimit
step in the Noetherian dimension induction below.
-/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Cohomology
open TopCat.Sheaf
universe u
variable {X : AlgebraicGeometry.Scheme.{u}}

lemma subsingleton_sheafH_third_of_shortExact
    {S : ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (CategoryTheory.Sheaf.H.{u + 1} S.X₂ n)]
    [Subsingleton (CategoryTheory.Sheaf.H.{u + 1} S.X₁ (n + 1))] :
    Subsingleton (CategoryTheory.Sheaf.H.{u + 1} S.X₃ n) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨y, hy⟩ := CategoryTheory.Sheaf.H.longSequence_exact₃ hS x rfl
    (Subsingleton.elim _ _)
  exact hy.symm.trans (by rw [Subsingleton.elim y 0, map_zero])

theorem sheafH_colimit_subsingleton [AlgebraicGeometry.IsNoetherian X]
    (n : ℕ) {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hD : ∀ i, Subsingleton (CategoryTheory.Sheaf.H.{u + 1} (D.obj i) (n + 1))) :
    Subsingleton (CategoryTheory.Sheaf.H.{u + 1} (colimit D) (n + 1)) := by
  induction n generalizing D with
  | zero =>
    let S := godementDiagramSequence D
    have hS := godementDiagramSequence_shortExact D
    let T := S.map colim
    have hT : T.ShortExact := hS.map_of_exact colim
    have hfl : ∀ i, TopCat.Presheaf.IsFlasque (X := X.toTopCat) (S.X₂.obj i).obj :=
      fun i => godementFunctor_isFlasque (D.obj i)
    have : TopCat.Presheaf.IsFlasque (X := X.toTopCat) T.X₂.obj :=
      filtered_colimit_isFlasque S.X₂
    have : Subsingleton (CategoryTheory.Sheaf.H.{u + 1} T.X₂ 1) :=
      subsingleton_sheafH_of_isFlasque T.X₂ 0
    apply subsingleton_sheafH_one_of_shortExact hT
    have hsections : ∀ i, Epi ((S.g.app i).hom.app (op ⊤)) := by
      intro i
      let Si := S.map ((CategoryTheory.evaluation I _).obj i)
      have hSi : Si.ShortExact := hS.map_of_exact _
      have : Subsingleton (CategoryTheory.Sheaf.H.{u + 1} Si.X₁ 1) := hD i
      apply (AddCommGrpCat.epi_iff_surjective _).mpr
      intro x
      exact CategoryTheory.Sheaf.H.longSequence_equiv₀_exact₃ hSi isTerminalTop x
        (Subsingleton.elim _ _)
    exact (AddCommGrpCat.epi_iff_surjective _).mp (colimit_map_sections_epi S.g ⊤)
  | succ n ih =>
    let S := godementDiagramSequence D
    have hS := godementDiagramSequence_shortExact D
    let T := S.map colim
    have hT : T.ShortExact := hS.map_of_exact colim
    have hfl : ∀ i, TopCat.Presheaf.IsFlasque (X := X.toTopCat) (S.X₂.obj i).obj :=
      fun i => godementFunctor_isFlasque (D.obj i)
    have : TopCat.Presheaf.IsFlasque (X := X.toTopCat) T.X₂.obj :=
      filtered_colimit_isFlasque S.X₂
    have : Subsingleton (CategoryTheory.Sheaf.H.{u + 1} T.X₂ (n + 1 + 1)) :=
      subsingleton_sheafH_of_isFlasque T.X₂ (n + 1)
    have hQ : ∀ i, Subsingleton (CategoryTheory.Sheaf.H.{u + 1} (S.X₃.obj i) (n + 1)) := by
      intro i
      let Si := S.map ((CategoryTheory.evaluation I _).obj i)
      have hSi : Si.ShortExact := hS.map_of_exact _
      have : TopCat.Presheaf.IsFlasque (X := X.toTopCat) Si.X₂.obj := hfl i
      have : Subsingleton (CategoryTheory.Sheaf.H.{u + 1} Si.X₂ (n + 1)) :=
        subsingleton_sheafH_of_isFlasque Si.X₂ n
      have : Subsingleton (CategoryTheory.Sheaf.H.{u + 1} Si.X₁ (n + 1 + 1)) := hD i
      exact subsingleton_sheafH_third_of_shortExact hSi (n + 1)
    have : Subsingleton (CategoryTheory.Sheaf.H.{u + 1} T.X₃ (n + 1)) := ih S.X₃ hQ
    exact subsingleton_sheafH_succ_of_shortExact hT (n + 1)

end AlgebraicGeometry.Scheme.Cohomology

/-! ## Generic-point reduction and dimension induction -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Cohomology
universe u
variable (X : Scheme.{u}) {ι : Type} [Finite ι]
local instance : HasFiniteBiproducts (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  Abelian.hasFiniteBiproducts
/-- Classical decidability of point membership in an open for the finite-stalk argument. -/
local instance decidablePointMemSchemeOpen (p : X) : ∀ U : Opens X, Decidable (p ∈ U) :=
  fun _ => Classical.propDecidable _

lemma genericPoints_eq_of_specializes {x y : X}
    (hx : x ∈ genericPoints X) (hy : y ∈ genericPoints X) (h : x ⤳ y) : x = y := by
  have hh : closure ({x} : Set X) ⊆ closure {y} := hy.2 hx.1 h.closure_subset
  exact (h.antisymm (specializes_iff_closure_subset.mpr hh)).eq

lemma finiteStalkSkyscraperMap_stalk_isIso
    (p : ι → X) (hp : ∀ i j, j ≠ i → ¬ p j ⤳ p i)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (i : ι) :
    IsIso ((additiveStalkFunctor X (p i)).map (finiteStalkSkyscraperMap X p F)) := by
  classical
  let C := fun j => additiveSkyscraper X (p j) ((additiveStalkFunctor X (p j)).obj F)
  let S := additiveStalkFunctor X (p i)
  let e := S.mapBiproduct C
  have hz : ∀ j, j ≠ i → IsZero ((S.obj ∘ C) j) := by
    intro j hj
    exact (terminalAdditiveGroupIsZero.{u}).of_iso
      (skyscraperPresheafStalkOfNotSpecializes (p j) _ (hp i j hj))
  have hπ : IsIso (biproduct.π (S.obj ∘ C) i) :=
    biproductProjection_isIso_of_other_isZero _ i hz
  have hπeq : S.map (biproduct.π C i) = e.hom ≫ biproduct.π (S.obj ∘ C) i := by
    dsimp only [e, Functor.mapBiproduct_hom]
    exact (biproduct.lift_π (fun j => S.map (biproduct.π C j)) i).symm
  have : IsIso (S.map (biproduct.π C i)) := by rw [hπeq]; infer_instance
  have hu : IsIso (S.map ((additiveStalkSkyscraperAdjunction X (p i)).unit.app F)) :=
    stalkSkyscraperUnit_isIso X (p i) F
  have hcomp : S.map (finiteStalkSkyscraperMap X p F) ≫ S.map (biproduct.π C i) =
      S.map ((additiveStalkSkyscraperAdjunction X (p i)).unit.app F) := by
    rw [← S.map_comp]
    congr 1
    exact biproduct.lift_π (fun j => (additiveStalkSkyscraperAdjunction X (p j)).unit.app F) i
  have heq : S.map (finiteStalkSkyscraperMap X p F) =
      S.map ((additiveStalkSkyscraperAdjunction X (p i)).unit.app F) ≫
        inv (S.map (biproduct.π C i)) := by
    rw [← hcomp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

lemma finiteGenericSkyscraperMap_stalk_isIso
    (p : ι → X) (hp : Function.Injective p)
    (hg : ∀ i, p i ∈ genericPoints X)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (i : ι) :
    IsIso ((additiveStalkFunctor X (p i)).map (finiteStalkSkyscraperMap X p F)) :=
  finiteStalkSkyscraperMap_stalk_isIso X p
    (fun i j hji h => hji (hp (genericPoints_eq_of_specializes X (hg j) (hg i) h))) F i

lemma stalk_kernel_isZero_of_stalk_isIso
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : F ⟶ G) (x : X) [IsIso ((additiveStalkFunctor X x).map f)] :
    IsZero ((additiveStalkFunctor X x).obj (kernel f)) :=
  (isZero_kernel_of_mono ((additiveStalkFunctor X x).map f)).of_iso
    (PreservesKernel.iso (additiveStalkFunctor X x) f)

lemma stalk_cokernel_isZero_of_stalk_isIso
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : F ⟶ G) (x : X) [IsIso ((additiveStalkFunctor X x).map f)] :
    IsZero ((additiveStalkFunctor X x).obj (cokernel f)) :=
  (isZero_cokernel_of_epi ((additiveStalkFunctor X x).map f)).of_iso
    (PreservesCokernel.iso (additiveStalkFunctor X x) f)

lemma subsingleton_sheafH_of_kernel_cokernel
    {F B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f : F ⟶ B) (n : ℕ)
    [Subsingleton (Sheaf.H.{u + 1} B (n + 2))]
    [Subsingleton (Sheaf.H.{u + 1} (kernel f) (n + 2))]
    [Subsingleton (Sheaf.H.{u + 1} (cokernel f) (n + 1))] :
    Subsingleton (Sheaf.H.{u + 1} F (n + 2)) := by
  let S₂ := ShortComplex.mk (kernel.ι (cokernel.π f)) (cokernel.π f) (kernel.condition _)
  have hS₂ : S₂.ShortExact := { exact := ShortComplex.exact_kernel (cokernel.π f) }
  have hIm : Subsingleton (Sheaf.H.{u + 1} S₂.X₁ (n + 2)) :=
    subsingleton_sheafH_succ_of_shortExact hS₂ (n + 1)
  have : Subsingleton (Sheaf.H.{u + 1} (Abelian.coimage f) (n + 2)) :=
    (sheafCohomologyAddEquiv X (Abelian.coimageIsoImage f) (n + 2)).injective.subsingleton
  let S₁ := ShortComplex.mk (kernel.ι f) (cokernel.π (kernel.ι f)) (cokernel.condition _)
  have hS₁ : S₁.ShortExact := { exact := ShortComplex.exact_cokernel (kernel.ι f) }
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨y, hy⟩ := Sheaf.H.longSequence_exact₂ hS₁ x (Subsingleton.elim _ _)
  exact hy.symm.trans (by rw [Subsingleton.elim y 0, map_zero])

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology
open TopCat.Sheaf
universe u

instance noetherian_closedSubscheme (X : Scheme.{u}) [IsNoetherian X] (Z : Closeds X) :
    IsNoetherian (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let : IsLocallyNoetherian I.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  let : NoetherianSpace I.subscheme :=
    I.subschemeι.isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
  exact ⟨⟩

lemma closedSubscheme_topologicalKrullDim (X : Scheme.{u}) (Z : Closeds X) :
    topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme =
      topologicalKrullDim Z := by
  change topologicalKrullDim ↥((Scheme.IdealSheafData.vanishingIdeal Z).support : Set X) = _
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

lemma subsingleton_sheafH_of_closed_support
    (X : Scheme.{u}) (Z : Closeds X)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hf : ∀ x : X, x ∉ Z → IsZero (TopCat.Presheaf.stalk F.obj x)) (n : ℕ)
    (hvan : ∀ M : Sheaf
      (Opens.grothendieckTopology (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)
      AddCommGrpCat.{u}, Subsingleton (Sheaf.H.{u + 1} M n)) :
    Subsingleton (Sheaf.H.{u + 1} F n) := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let i := I.subschemeι.base
  have hi : Topology.IsClosedEmbedding i := I.subschemeι.isClosedEmbedding
  have hF : ∀ x : X, x ∉ Set.range i → IsZero (TopCat.Presheaf.stalk F.obj x) := by
    intro x hx
    apply hf x
    change x ∉ (Z : Set X)
    change x ∉ Set.range I.subschemeι at hx
    simpa only [Scheme.IdealSheafData.range_subschemeι,
      I, Scheme.IdealSheafData.coe_support_vanishingIdeal] using hx
  have := hvan ((TopCat.Sheaf.pullback AddCommGrpCat.{u} i).obj F)
  exact (closedSupportCohomologyEquiv i hi F hF n).injective.subsingleton

lemma subsingleton_sheafH_of_generic_stalks_zero
    (d : ℕ)
    (ih : ∀ (Y : Scheme.{u}) [IsNoetherian Y], topologicalKrullDim Y ≤ d →
      ∀ (M : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) (n : ℕ),
        d ≤ n → Subsingleton (Sheaf.H.{u + 1} M (n + 1)))
    (X : Scheme.{u}) [IsNoetherian X] (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hzero : ∀ x ∈ genericPoints X, IsZero (TopCat.Presheaf.stalk F.obj x))
    (n : ℕ) (hn : d ≤ n) : Subsingleton (Sheaf.H.{u + 1} F (n + 1)) := by
  let D := supportedAwayDiagram F (genericPoints X)
  have hD : ∀ U, Subsingleton (Sheaf.H.{u + 1} (D.obj U) (n + 1)) := by
    intro U
    let Z : Closeds X := ⟨(U.unop.val : Set X)ᶜ, U.unop.val.isOpen.isClosed_compl⟩
    have hZ : Disjoint (Z : Set X) (genericPoints X) :=
      Set.disjoint_left.mpr (fun x hx hxg => hx (U.unop.property hxg))
    have hzdim : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≤ d := by
      rw [closedSubscheme_topologicalKrullDim]
      exact topologicalKrullDim_closed_le_of_avoids_genericPoints
        (Z : Set X) Z.isClosed hZ d hdim
    refine subsingleton_sheafH_of_closed_support X Z (D.obj U) ?_ (n + 1) ?_
    · intro x hx
      exact supportedAway_stalk_isZero F U.unop.val x (Classical.not_not.mp hx)
    · intro M
      exact ih _ hzdim M n hn
  have : Subsingleton (Sheaf.H.{u + 1} (colimit D) (n + 1)) :=
    sheafH_colimit_subsingleton n D hD
  have : IsIso (supportedAwayColimitMap F (genericPoints X)) :=
    supportedAwayColimitMap_isIso_of_stalks_zero F (genericPoints X) hzero
      (fun x hx U hxU => genericPoint_exists_open_disjoint x hx U hxU)
  exact (sheafCohomologyAddEquiv X
    (asIso (supportedAwayColimitMap F (genericPoints X))) (n + 1)).symm.injective.subsingleton

theorem noetherianSheafCohomology_vanishing_induction (d : ℕ) :
    ∀ (X : Scheme.{u}) [IsNoetherian X], topologicalKrullDim X ≤ d →
      ∀ (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ),
        d ≤ n → Subsingleton (Sheaf.H.{u + 1} F (n + 1)) := by
  induction d with
  | zero =>
    intro X _ hdim F n _
    exact noetherianSheafCohomology_vanishing_of_dim_le_zero X F hdim (n + 1) (by omega)
  | succ d ih =>
    intro X _ hdim F n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    let : Fintype (genericPoints X) :=
      (genericPoints.finite (NoetherianSpace.finite_irreducibleComponents (α := X))).fintype
    let e : Fin (Fintype.card (genericPoints X)) ≃ genericPoints X :=
      (Fintype.equivFin (genericPoints X)).symm
    let p : Fin (Fintype.card (genericPoints X)) → X := fun i => (e i).val
    have hp : Function.Injective p := Subtype.val_injective.comp e.injective
    have hg : ∀ i, p i ∈ genericPoints X := fun i => (e i).property
    let : HasFiniteBiproducts (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
      Abelian.hasFiniteBiproducts
    let f := finiteStalkSkyscraperMap X p F
    have hgen : ∀ x ∈ genericPoints X, IsIso ((additiveStalkFunctor X x).map f) := by
      intro x hx
      obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      have hpi : p i = x := congrArg Subtype.val hi
      rw [← hpi]
      exact finiteGenericSkyscraperMap_stalk_isIso X p hp hg F i
    have hK : ∀ x ∈ genericPoints X,
        IsZero (TopCat.Presheaf.stalk (kernel f).obj x) := by
      intro x hx
      have := hgen x hx
      exact stalk_kernel_isZero_of_stalk_isIso X f x
    have hQ : ∀ x ∈ genericPoints X,
        IsZero (TopCat.Presheaf.stalk (cokernel f).obj x) := by
      intro x hx
      have := hgen x hx
      exact stalk_cokernel_isZero_of_stalk_isIso X f x
    have : Subsingleton (Sheaf.H.{u + 1} (kernel f) (k + 2)) :=
      subsingleton_sheafH_of_generic_stalks_zero d ih X hdim (kernel f) hK (k + 1) (by omega)
    have : Subsingleton (Sheaf.H.{u + 1} (cokernel f) (k + 1)) :=
      subsingleton_sheafH_of_generic_stalks_zero d ih X hdim (cokernel f) hQ k (by omega)
    have : Subsingleton (Sheaf.H.{u + 1}
        (finiteSkyscraperSheaf X p (fun i => (additiveStalkFunctor X (p i)).obj F)) (k + 2)) :=
      finiteSkyscraperCohomology_positive X p _ (k + 1)
    exact subsingleton_sheafH_of_kernel_cokernel X f k

/-- Grothendieck vanishing for all abelian sheaves on all Noetherian schemes. -/
theorem noetherianSheafCohomology_vanishing
    (X : Scheme.{u}) [IsNoetherian X]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (d n : ℕ)
    (hdim : topologicalKrullDim X ≤ d) (hn : d < n) :
    Subsingleton (Sheaf.H.{u + 1} F n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact noetherianSheafCohomology_vanishing_induction d X hdim F m (by omega)

/-- The original all-universe, all-scheme, all-abelian-sheaf vanishing family. -/
theorem noetherianSheafCohomologyVanishing : NoetherianSheafCohomologyVanishing.{u} := by
  intro X _ M d n hdim hn
  exact noetherianSheafCohomology_vanishing X M d n hdim hn

end AlgebraicGeometry.Scheme.Cohomology
