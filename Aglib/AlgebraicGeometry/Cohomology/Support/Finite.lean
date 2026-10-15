/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Support.Skyscraper
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
/-!
# Actual cohomology of sheaves with finite closed support

The actual `Sheaf.H` of a finite biproduct of additive skyscraper sheaves is the
product of their actual cohomology groups, with the native biproduct projection
maps. Its positive degrees vanish and its degree zero is the product of the
coefficient groups, naturally in the coefficient maps.

For an arbitrary additive sheaf whose stalks vanish outside finitely many
distinct closed points, the canonical finite map formed from the native
stalk/skyscraper adjunction units is an isomorphism. Thus the finite-support
vanishing result does not assume a skyscraper decomposition. The support
condition is a statement about the original sheaf's actual additive stalks.

For a scheme module sheaf, the field action on these additive stalks is induced
by the pre-existing `moduleScalar` maps. The degree-zero comparison is linear
for precisely that action, and finite-dimensional supported stalks give the
sum-of-stalk-dimensions formula for actual `moduleCohomology`. The final Euler
expression uses actual H⁰ and H¹. No coherent-cohomology finiteness theorem,
proper Euler argument, module-quotient support dictionary or line-bundle-degree
identity is supplied or assumed implicitly.

The native inputs are Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`,
`Topology/Sheaves/Skyscraper`, `Topology/Sheaves/Stalks`, the finite-biproduct
identities and the standard finite-dimensional product formula. This file
imports the actual cohomology object and scalar owners through `Skyscraper`.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.FiniteSupport` at R5Lab revision
`95a3772b895fbc19a81684be4ffd519d0fdcd6b3`; all declarations are retained.
-/

@[expose] public section

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

/-- The finite biproduct of additive skyscrapers with the specified coefficients. -/
abbrev finiteSkyscraperSheaf (p : ι → X) (A : ι → AddCommGrpCat.{u}) :=
  ⨁ fun i => additiveSkyscraper X (p i) (A i)

/-- Cohomology of a finite skyscraper biproduct as the product of its cohomologies. -/
def finiteSkyscraperCohomologyEquiv (p : ι → X) (A : ι → AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{u + 1} (finiteSkyscraperSheaf X p A) n ≃+
      ∀ i, Sheaf.H.{u + 1} (additiveSkyscraper X (p i) (A i)) n := by
  classical
  letI := Fintype.ofFinite ι
  let C := fun i => additiveSkyscraper X (p i) (A i)
  have hzero : ∀ {P Q : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
      (x : Sheaf.H.{u + 1} P n), Sheaf.H.map (0 : P ⟶ Q) n x = 0 := by
    intro P Q x
    simp [Sheaf.H.map_apply]
  refine {
    toFun := fun x i => Sheaf.H.map (biproduct.π C i) n x
    invFun := fun x => ∑ i, Sheaf.H.map (biproduct.ι C i) n (x i)
    left_inv := ?_
    right_inv := ?_
    map_add' := ?_ }
  · intro x
    have hsum : ∀ s : Finset ι,
        Sheaf.H.map (∑ i ∈ s, biproduct.π C i ≫ biproduct.ι C i) n x =
          ∑ i ∈ s, Sheaf.H.map (biproduct.π C i ≫ biproduct.ι C i) n x := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [hzero]
      | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, Sheaf.H.map_add_apply, ih]
    have h := hsum Finset.univ
    rw [biproduct.total, Sheaf.H.map_id_apply] at h
    simpa only [Sheaf.H.map_comp_apply] using h.symm
  · intro x
    funext i
    simp only [map_sum, ← Sheaf.H.map_comp_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [biproduct.ι_π_ne _ hj]
      exact hzero _
    · simp
  · intro x y
    funext i
    exact map_add _ _ _

@[simp] theorem finiteSkyscraperCohomologyEquiv_apply (p : ι → X)
    (A : ι → AddCommGrpCat.{u}) (n : ℕ)
    (x : Sheaf.H.{u + 1} (finiteSkyscraperSheaf X p A) n) (i : ι) :
    finiteSkyscraperCohomologyEquiv X p A n x i =
      Sheaf.H.map (biproduct.π (fun i => additiveSkyscraper X (p i) (A i)) i) n x := rfl

theorem finiteSkyscraperCohomology_positive (p : ι → X)
    (A : ι → AddCommGrpCat.{u}) (n : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} (finiteSkyscraperSheaf X p A) (n + 1)) := by
  have : ∀ i, Subsingleton (Sheaf.H.{u + 1} (additiveSkyscraper X (p i) (A i)) (n + 1)) :=
    fun i => skyscraperCohomology_positive X (p i) (A i) n
  exact (finiteSkyscraperCohomologyEquiv X p A (n + 1)).injective.subsingleton

/-- Degree-zero cohomology of a finite skyscraper family as its coefficient groups. -/
def finiteSkyscraperH0Equiv (p : ι → X) (A : ι → AddCommGrpCat.{u}) :
    Sheaf.H.{u + 1} (finiteSkyscraperSheaf X p A) 0 ≃+ ∀ i, A i :=
  (finiteSkyscraperCohomologyEquiv X p A 0).trans
    (AddEquiv.piCongrRight fun i => skyscraperH0Equiv X (p i) (A i))

/-- The morphism of finite skyscraper biproducts induced by coefficient maps. -/
def finiteSkyscraperMap {p : ι → X} {A B : ι → AddCommGrpCat.{u}}
    (f : ∀ i, A i ⟶ B i) : finiteSkyscraperSheaf X p A ⟶ finiteSkyscraperSheaf X p B :=
  biproduct.map fun i => (additiveSkyscraperFunctor X (p i)).map (f i)

theorem finiteSkyscraperH0Equiv_naturality {p : ι → X} {A B : ι → AddCommGrpCat.{u}}
    (f : ∀ i, A i ⟶ B i) (x : Sheaf.H.{u + 1} (finiteSkyscraperSheaf X p A) 0) (i : ι) :
    finiteSkyscraperH0Equiv X p B (Sheaf.H.map (finiteSkyscraperMap X f) 0 x) i =
      f i (finiteSkyscraperH0Equiv X p A x i) := by
  change skyscraperH0Equiv X (p i) (B i)
      (finiteSkyscraperCohomologyEquiv X p B 0
        (Sheaf.H.map (finiteSkyscraperMap X f) 0 x) i) = _
  rw [finiteSkyscraperCohomologyEquiv_apply, ← Sheaf.H.map_comp_apply]
  simp only [finiteSkyscraperMap, biproduct.map_π]
  rw [Sheaf.H.map_comp_apply, skyscraperH0Equiv_naturality]
  rw [← finiteSkyscraperCohomologyEquiv_apply]
  rfl

/-- Local classical decidability of membership in an open, for stalk adjunctions. -/
local instance decidablePointMemOpen (p : X) : ∀ U : Opens X, Decidable (p ∈ U) :=
  fun _ => Classical.propDecidable _

theorem skyscraperCounit_isIso (p : X) (A : AddCommGrpCat.{u}) :
    IsIso ((additiveStalkSkyscraperAdjunction X p).counit.app A) := by
  change IsIso (skyscraperPresheafStalkOfSpecializes p A specializes_rfl).hom
  infer_instance

theorem stalkSkyscraperUnit_isIso (p : X) (A : Sheaf (Opens.grothendieckTopology X)
  AddCommGrpCat.{u}) :
    IsIso ((additiveStalkFunctor X p).map
      ((additiveStalkSkyscraperAdjunction X p).unit.app A)) := by
  have : IsIso ((additiveStalkSkyscraperAdjunction X p).counit.app
      ((additiveStalkFunctor X p).obj A)) := by
    change IsIso (skyscraperPresheafStalkOfSpecializes p _ specializes_rfl).hom
    infer_instance
  exact isIso_of_comp_hom_eq_id _
    ((additiveStalkSkyscraperAdjunction X p).left_triangle_components A)

theorem biproductProjection_isIso_of_other_isZero {ι : Type} [Finite ι]
    (A : ι → AddCommGrpCat.{u}) (i : ι)
    (h : ∀ j, j ≠ i → IsZero (A j)) : IsIso (biproduct.π A i) := by
  classical
  refine ⟨⟨biproduct.ι A i, ?_, by simp⟩⟩
  apply biproduct.hom_ext
  intro j
  by_cases hj : j = i
  · subst j
    simp
  · exact (h j hj).eq_of_tgt _ _

theorem biproduct_isZero_of_isZero {ι : Type} [Finite ι] (A : ι → AddCommGrpCat.{u})
    (h : ∀ j, IsZero (A j)) : IsZero (⨁ A) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply biproduct.hom_ext
  intro j
  exact (h j).eq_of_tgt _ _

theorem terminalAdditiveGroupIsZero : IsZero (terminal AddCommGrpCat.{u}) :=
  (isZero_zero AddCommGrpCat.{u}).of_iso
    (terminalIsTerminal.uniqueUpToIso (isZero_zero AddCommGrpCat.{u}).isTerminal)

theorem skyscraperStalk_isZero_of_closed (p x : X) (A : AddCommGrpCat.{u})
    (hp : IsClosed ({p} : Set X)) (hx : p ≠ x) :
    IsZero ((additiveStalkFunctor X x).obj (additiveSkyscraper X p A)) := by
  have hn : ¬ p ⤳ x := by
    intro h
    exact hx (Set.mem_singleton_iff.mp (h.mem_closed hp (Set.mem_singleton p))).symm
  exact terminalAdditiveGroupIsZero.of_iso
    (skyscraperPresheafStalkOfNotSpecializes p A hn)

/-- The map to a finite family of stalk skyscrapers induced by adjunction units. -/
def finiteStalkSkyscraperMap (p : ι → X)
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    A ⟶ ⨁ fun i => additiveSkyscraper X (p i) ((additiveStalkFunctor X (p i)).obj A) :=
  biproduct.lift fun i => (additiveStalkSkyscraperAdjunction X (p i)).unit.app A

theorem finiteStalkSkyscraperMap_isIso (p : ι → X) (hp : Function.Injective p)
    (hclosed : ∀ i, IsClosed ({p i} : Set X))
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hA : ∀ x, x ∉ Set.range p → IsZero ((additiveStalkFunctor X x).obj A)) :
    IsIso (finiteStalkSkyscraperMap X p A) := by
  classical
  have hstalk : ∀ x : X,
      IsIso ((additiveStalkFunctor X x).map (finiteStalkSkyscraperMap X p A)) := by
    intro x
    let C := fun i => additiveSkyscraper X (p i) ((additiveStalkFunctor X (p i)).obj A)
    let S := additiveStalkFunctor X x
    let e := S.mapBiproduct C
    by_cases hx : x ∈ Set.range p
    · obtain ⟨i, rfl⟩ := hx
      have hz : ∀ j, j ≠ i → IsZero ((S.obj ∘ C) j) := by
        intro j hj
        exact skyscraperStalk_isZero_of_closed X (p j) (p i) _ (hclosed j)
          (fun h => hj (hp h))
      have hπ : IsIso (biproduct.π (S.obj ∘ C) i) :=
        biproductProjection_isIso_of_other_isZero _ i hz
      have hπeq : S.map (biproduct.π C i) = e.hom ≫ biproduct.π (S.obj ∘ C) i := by
        dsimp only [e, Functor.mapBiproduct_hom]
        exact (biproduct.lift_π (fun j => S.map (biproduct.π C j)) i).symm
      have : IsIso (S.map (biproduct.π C i)) := by
        rw [hπeq]
        infer_instance
      have hu : IsIso (S.map ((additiveStalkSkyscraperAdjunction X (p i)).unit.app A)) :=
        stalkSkyscraperUnit_isIso X (p i) A
      have hcomp : S.map (finiteStalkSkyscraperMap X p A) ≫ S.map (biproduct.π C i) =
          S.map ((additiveStalkSkyscraperAdjunction X (p i)).unit.app A) := by
        rw [← S.map_comp]
        congr 1
        exact biproduct.lift_π (fun j => (additiveStalkSkyscraperAdjunction X (p j)).unit.app A) i
      have heq : S.map (finiteStalkSkyscraperMap X p A) =
          S.map ((additiveStalkSkyscraperAdjunction X (p i)).unit.app A) ≫
            inv (S.map (biproduct.π C i)) := by
        rw [← hcomp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      rw [heq]
      infer_instance
    · have hz : ∀ j, IsZero ((S.obj ∘ C) j) := by
        intro j
        exact skyscraperStalk_isZero_of_closed X (p j) x _ (hclosed j)
          (fun h => hx ⟨j, h⟩)
      have ht : IsZero (S.obj (⨁ C)) := (biproduct_isZero_of_isZero _ hz).of_iso e
      exact isIso_of_source_target_iso_zero _ (hA x hx).isoZero ht.isoZero
  have : ∀ x : X,
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (finiteStalkSkyscraperMap X p A).hom) := hstalk
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso (finiteStalkSkyscraperMap X p A)

open AlgebraicGeometry.Scheme.OverField
variable {k : Type u} [Field k]

/-- The underlying additive stalk of a module sheaf on a field scheme. -/
abbrev moduleAdditiveStalk (X : FScheme k) (M : X.left.Modules) (p : X.left) :=
  (additiveStalkFunctor X.left p).obj (moduleAddSheaf X.left M)

/-- The structural base-field action as endomorphisms of the additive stalk. -/
def moduleAdditiveStalkScalars (X : FScheme k) (M : X.left.Modules) (p : X.left) :
    k →+* AddMonoid.End (moduleAdditiveStalk X M p) where
  toFun a := ((additiveStalkFunctor X.left p).map (moduleScalar X M a)).hom
  map_zero' := by
    ext x
    change ((additiveStalkFunctor X.left p).map (moduleScalar X M 0)) x = 0
    rw [moduleScalar_zero, Functor.map_zero]
    rfl
  map_one' := by
    ext x
    change ((additiveStalkFunctor X.left p).map (moduleScalar X M 1)) x = x
    rw [moduleScalar_one, (additiveStalkFunctor X.left p).map_id]
    rfl
  map_add' a b := by
    ext x
    change ((additiveStalkFunctor X.left p).map (moduleScalar X M (a + b))) x =
      ((additiveStalkFunctor X.left p).map (moduleScalar X M a)) x +
        ((additiveStalkFunctor X.left p).map (moduleScalar X M b)) x
    rw [moduleScalar_add, Functor.map_add]
    rfl
  map_mul' a b := by
    ext x
    change ((additiveStalkFunctor X.left p).map (moduleScalar X M (a * b))) x =
      ((additiveStalkFunctor X.left p).map (moduleScalar X M a))
        (((additiveStalkFunctor X.left p).map (moduleScalar X M b)) x)
    rw [moduleScalar_mul, Functor.map_comp]
    rfl

instance moduleAdditiveStalkModule (X : FScheme k) (M : X.left.Modules) (p : X.left) :
    Module k (moduleAdditiveStalk X M p) :=
  Module.compHom _ (moduleAdditiveStalkScalars X M p)

theorem moduleAdditiveStalk_smul (X : FScheme k) (M : X.left.Modules) (p : X.left)
    (a : k) (x : moduleAdditiveStalk X M p) :
    a • x = ((additiveStalkFunctor X.left p).map (moduleScalar X M a)) x := rfl

/-- The stalk map, linear for the actual structural base-field actions. -/
def moduleAdditiveStalkMap (X : FScheme k) {M N : X.left.Modules} (f : M ⟶ N) (p : X.left) :
    moduleAdditiveStalk X M p →ₗ[k] moduleAdditiveStalk X N p where
  toAddHom := ((additiveStalkFunctor X.left p).map (coefficientSheafMap X f)).hom
  map_smul' a x := by
    change ((additiveStalkFunctor X.left p).map (coefficientSheafMap X f))
      (((additiveStalkFunctor X.left p).map (moduleScalar X M a)) x) =
        ((additiveStalkFunctor X.left p).map (moduleScalar X N a))
          (((additiveStalkFunctor X.left p).map (coefficientSheafMap X f)) x)
    have h := congrArg (fun g => ((additiveStalkFunctor X.left p).map g) x)
      (moduleScalar_naturality X f a)
    simpa only [Functor.map_comp, AddCommGrpCat.comp_apply] using h

/-- Reconstruction from stalks at distinct closed points supporting the sheaf. -/
def finiteClosedSupportIso (p : ι → X) (hp : Function.Injective p)
    (hclosed : ∀ i, IsClosed ({p i} : Set X))
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hA : ∀ x, x ∉ Set.range p → IsZero ((additiveStalkFunctor X x).obj A)) :
    A ≅ finiteSkyscraperSheaf X p (fun i => (additiveStalkFunctor X (p i)).obj A) := by
  have := finiteStalkSkyscraperMap_isIso X p hp hclosed A hA
  exact asIso (finiteStalkSkyscraperMap X p A)

/-- The additive cohomology equivalence induced by an isomorphism of coefficients. -/
def sheafCohomologyAddEquiv
    {A B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (e : A ≅ B) (n : ℕ) : Sheaf.H.{u + 1} A n ≃+ Sheaf.H.{u + 1} B n where
  toFun := Sheaf.H.map e.hom n
  invFun := Sheaf.H.map e.inv n
  left_inv x := by
    simpa only [e.hom_inv_id, Sheaf.H.map_id_apply] using
      (Sheaf.H.map_comp_apply (f := e.hom) (g := e.inv) (n := n) x).symm
  right_inv x := by
    simpa only [e.inv_hom_id, Sheaf.H.map_id_apply] using
      (Sheaf.H.map_comp_apply (f := e.inv) (g := e.hom) (n := n) x).symm
  map_add' := map_add (Sheaf.H.map e.hom n)

theorem finiteClosedSupportCohomology_positive (p : ι → X) (hp : Function.Injective p)
    (hclosed : ∀ i, IsClosed ({p i} : Set X))
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hA : ∀ x, x ∉ Set.range p → IsZero ((additiveStalkFunctor X x).obj A)) (n : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} A (n + 1)) := by
  have := finiteSkyscraperCohomology_positive X p
    (fun i => (additiveStalkFunctor X (p i)).obj A) n
  exact (sheafCohomologyAddEquiv X (finiteClosedSupportIso X p hp hclosed A hA)
    (n + 1)).injective.subsingleton

/-- Global sections of a sheaf with finite closed support as its supporting stalks. -/
def finiteClosedSupportH0Equiv (p : ι → X) (hp : Function.Injective p)
    (hclosed : ∀ i, IsClosed ({p i} : Set X))
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hA : ∀ x, x ∉ Set.range p → IsZero ((additiveStalkFunctor X x).obj A)) :
    Sheaf.H.{u + 1} A 0 ≃+ ∀ i, (additiveStalkFunctor X (p i)).obj A :=
  (sheafCohomologyAddEquiv X (finiteClosedSupportIso X p hp hclosed A hA) 0).trans
    (finiteSkyscraperH0Equiv X p (fun i => (additiveStalkFunctor X (p i)).obj A))

set_option maxHeartbeats 800000 in
-- Comparing the chosen sheaf biproduct with the original H⁰ map requires
-- extra definitional-equality normalization; the increase is local and finite.
theorem finiteClosedSupportH0Equiv_apply (p : ι → X) (hp : Function.Injective p)
    (hclosed : ∀ i, IsClosed ({p i} : Set X))
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hA : ∀ x, x ∉ Set.range p → IsZero ((additiveStalkFunctor X x).obj A))
    (x : Sheaf.H.{u + 1} A 0) (i : ι) :
    finiteClosedSupportH0Equiv X p hp hclosed A hA x i =
      skyscraperH0Equiv X (p i) ((additiveStalkFunctor X (p i)).obj A)
        (Sheaf.H.map ((additiveStalkSkyscraperAdjunction X (p i)).unit.app A) 0 x) := by
  change skyscraperH0Equiv X (p i) ((additiveStalkFunctor X (p i)).obj A)
    (finiteSkyscraperCohomologyEquiv X p _ 0
      (Sheaf.H.map (finiteStalkSkyscraperMap X p A) 0 x) i) = _
  rw [finiteSkyscraperCohomologyEquiv_apply, ← Sheaf.H.map_comp_apply]
  exact congrArg (fun g : A ⟶ additiveSkyscraper X (p i) ((additiveStalkFunctor X (p i)).obj A) =>
    skyscraperH0Equiv X (p i) ((additiveStalkFunctor X (p i)).obj A) (Sheaf.H.map g 0 x))
      (biproduct.lift_π (fun j => (additiveStalkSkyscraperAdjunction X (p j)).unit.app A) i)

theorem finiteClosedSupportH0Equiv_naturality (p : ι → X) (hp : Function.Injective p)
    (hclosed : ∀ i, IsClosed ({p i} : Set X))
    {A B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (hA : ∀ x, x ∉ Set.range p → IsZero ((additiveStalkFunctor X x).obj A))
    (hB : ∀ x, x ∉ Set.range p → IsZero ((additiveStalkFunctor X x).obj B))
    (f : A ⟶ B) (x : Sheaf.H.{u + 1} A 0) (i : ι) :
    finiteClosedSupportH0Equiv X p hp hclosed B hB (Sheaf.H.map f 0 x) i =
      ((additiveStalkFunctor X (p i)).map f)
        (finiteClosedSupportH0Equiv X p hp hclosed A hA x i) := by
  have hnat : f ≫ (additiveStalkSkyscraperAdjunction X (p i)).unit.app B =
      (additiveStalkSkyscraperAdjunction X (p i)).unit.app A ≫
        (additiveSkyscraperFunctor X (p i)).map ((additiveStalkFunctor X (p i)).map f) := by
    simpa only [Functor.id_map, Functor.comp_map] using
      (additiveStalkSkyscraperAdjunction X (p i)).unit.naturality f
  have h₁ := Sheaf.H.map_comp_apply (f := f)
    (g := (additiveStalkSkyscraperAdjunction X (p i)).unit.app B) (n := 0) x
  have h₂ := Sheaf.H.map_comp_apply
    (f := (additiveStalkSkyscraperAdjunction X (p i)).unit.app A)
    (g := (additiveSkyscraperFunctor X (p i)).map ((additiveStalkFunctor X (p i)).map f))
    (n := 0) x
  have h := h₁.symm.trans ((congrArg (fun g => Sheaf.H.map g 0 x) hnat).trans h₂)
  have hh := congrArg (skyscraperH0Equiv X (p i) ((additiveStalkFunctor X (p i)).obj B)) h
  calc
    finiteClosedSupportH0Equiv X p hp hclosed B hB (Sheaf.H.map f 0 x) i =
        skyscraperH0Equiv X (p i) ((additiveStalkFunctor X (p i)).obj B)
          (Sheaf.H.map ((additiveStalkSkyscraperAdjunction X (p i)).unit.app B) 0
            (Sheaf.H.map f 0 x)) :=
      finiteClosedSupportH0Equiv_apply X p hp hclosed B hB (Sheaf.H.map f 0 x) i
    _ = skyscraperH0Equiv X (p i) ((additiveStalkFunctor X (p i)).obj B)
        (Sheaf.H.map ((additiveSkyscraperFunctor X (p i)).map ((additiveStalkFunctor X (p
          i)).map f)) 0
          (Sheaf.H.map ((additiveStalkSkyscraperAdjunction X (p i)).unit.app A) 0 x)) := hh
    _ = ((additiveStalkFunctor X (p i)).map f)
        (skyscraperH0Equiv X (p i) ((additiveStalkFunctor X (p i)).obj A)
          (Sheaf.H.map ((additiveStalkSkyscraperAdjunction X (p i)).unit.app A) 0 x)) :=
      skyscraperH0Equiv_naturality X (p i) ((additiveStalkFunctor X (p i)).map f) _
    _ = ((additiveStalkFunctor X (p i)).map f)
        (finiteClosedSupportH0Equiv X p hp hclosed A hA x i) :=
      congrArg (fun y => ((additiveStalkFunctor X (p i)).map f) y)
        (finiteClosedSupportH0Equiv_apply X p hp hclosed A hA x i).symm

/-- The field-linear global-section comparison for a module with finite closed support. -/
def finiteClosedSupportModuleH0Equiv (X : FScheme k) (M : X.left.Modules)
    (p : ι → X.left) (hp : Function.Injective p)
    (hclosed : ∀ i, IsClosed ({p i} : Set X.left))
    (hM : ∀ x, x ∉ Set.range p → IsZero (moduleAdditiveStalk X M x)) :
    moduleCohomology k X M 0 ≃ₗ[k] ∀ i, moduleAdditiveStalk X M (p i) where
  __ := finiteClosedSupportH0Equiv X.left p hp hclosed (moduleAddSheaf X.left M) hM
  map_smul' a x := by
    funext i
    change finiteClosedSupportH0Equiv X.left p hp hclosed (moduleAddSheaf X.left M) hM
      (Sheaf.H.map (moduleScalar X M a) 0 x) i =
        ((additiveStalkFunctor X.left (p i)).map (moduleScalar X M a))
          (finiteClosedSupportH0Equiv X.left p hp hclosed (moduleAddSheaf X.left M) hM x i)
    exact finiteClosedSupportH0Equiv_naturality X.left p hp hclosed hM hM
      (moduleScalar X M a) x i

theorem finiteClosedSupportModuleCohomology_positive (X : FScheme k) (M : X.left.Modules)
    (p : ι → X.left) (hp : Function.Injective p)
    (hclosed : ∀ i, IsClosed ({p i} : Set X.left))
    (hM : ∀ x, x ∉ Set.range p → IsZero (moduleAdditiveStalk X M x)) (n : ℕ) :
    Subsingleton (moduleCohomology k X M (n + 1)) :=
  finiteClosedSupportCohomology_positive X.left p hp hclosed (moduleAddSheaf X.left M) hM n

theorem finiteClosedSupportModuleH0_finite (X : FScheme k) (M : X.left.Modules)
    (p : ι → X.left) (hp : Function.Injective p)
    (hclosed : ∀ i, IsClosed ({p i} : Set X.left))
    (hM : ∀ x, x ∉ Set.range p → IsZero (moduleAdditiveStalk X M x))
    [∀ i, FiniteDimensional k (moduleAdditiveStalk X M (p i))] :
    FiniteDimensional k (moduleCohomology k X M 0) :=
  (finiteClosedSupportModuleH0Equiv X M p hp hclosed hM).symm.finiteDimensional

theorem finiteClosedSupportModuleH0_finrank (X : FScheme k) (M : X.left.Modules)
    [Fintype ι] (p : ι → X.left) (hp : Function.Injective p)
    (hclosed : ∀ i, IsClosed ({p i} : Set X.left))
    (hM : ∀ x, x ∉ Set.range p → IsZero (moduleAdditiveStalk X M x))
    [∀ i, FiniteDimensional k (moduleAdditiveStalk X M (p i))] :
    Module.finrank k (moduleCohomology k X M 0) =
      ∑ i, Module.finrank k (moduleAdditiveStalk X M (p i)) := by
  rw [(finiteClosedSupportModuleH0Equiv X M p hp hclosed hM).finrank_eq,
    Module.finrank_pi_fintype]

theorem finiteClosedSupportModuleCohomology_finrank_positive (X : FScheme k)
    (M : X.left.Modules) (p : ι → X.left) (hp : Function.Injective p)
    (hclosed : ∀ i, IsClosed ({p i} : Set X.left))
    (hM : ∀ x, x ∉ Set.range p → IsZero (moduleAdditiveStalk X M x)) (n : ℕ) :
    Module.finrank k (moduleCohomology k X M (n + 1)) = 0 := by
  have := finiteClosedSupportModuleCohomology_positive X M p hp hclosed hM n
  exact Module.finrank_zero_of_subsingleton

/-- The Euler expression uses the original actual module cohomology groups. -/
theorem finiteClosedSupportModuleEuler (X : FScheme k) (M : X.left.Modules)
    [Fintype ι] (p : ι → X.left) (hp : Function.Injective p)
    (hclosed : ∀ i, IsClosed ({p i} : Set X.left))
    (hM : ∀ x, x ∉ Set.range p → IsZero (moduleAdditiveStalk X M x))
    [∀ i, FiniteDimensional k (moduleAdditiveStalk X M (p i))] :
    (Module.finrank k (moduleCohomology k X M 0) : ℤ) -
        (Module.finrank k (moduleCohomology k X M 1) : ℤ) =
      ∑ i, (Module.finrank k (moduleAdditiveStalk X M (p i)) : ℤ) := by
  rw [finiteClosedSupportModuleH0_finrank X M p hp hclosed hM,
    finiteClosedSupportModuleCohomology_finrank_positive X M p hp hclosed hM 0]
  simp

end AlgebraicGeometry.Scheme.Cohomology
