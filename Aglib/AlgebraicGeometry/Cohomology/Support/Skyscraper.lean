/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Injective.SectionCycles
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.Algebra.Category.Grp.EnoughInjectives
/-!
# Actual cohomology of additive skyscraper sheaves

For every scheme, point and abelian coefficient group, the native topological
skyscraper sheaf has zero actual `Sheaf.H` in every positive degree and has
`H⁰` naturally equivalent to the coefficient group. The point need not be closed.

The proof uses the native stalk/skyscraper adjunction. Stalks are exact, and the
skyscraper functor is exact because its maps are epimorphisms on every open set.
The exact adjunction compares the original Ext definition of `Sheaf.H` with
Ext from the stalk of the actual constant integer sheaf. This stalk is projective:
its maps to any group are naturally equivalent to elements of that group.
No assumption about a module forgetful functor preserving injectives is used.

The native adjunction, exactness and Ext comparison are from Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`, in `Topology/Sheaves/Skyscraper`,
`Topology/Sheaves/Abelian` and `Algebra/Homology/DerivedCategory/Ext/MapAdjunction`.
The global-section Hom comparison is the existing `AffineAcyclicity` owner.
This is a component for B04 product-formula and Cartier-degree arguments; it
makes no proper Euler-characteristic or line-bundle-degree assertion.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Cohomology.Skyscraper` at R5Lab revision
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
variable (X : Scheme.{u}) (p : X)
/-- Classical decidability of membership of `p` in an open, used by the skyscraper construction. -/
local instance skyscraperMemDecidable : ∀ U : Opens X, Decidable (p ∈ U) :=
  fun _ => Classical.propDecidable _

/-- The functor assigning to an abelian group its skyscraper sheaf at `p` on `X`. -/
abbrev additiveSkyscraperFunctor : AddCommGrpCat.{u} ⥤
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  _root_.skyscraperSheafFunctor (X := X.carrier) p

/-- The skyscraper sheaf on `X` with value `A` at `p`. -/
abbrev additiveSkyscraper (A : AddCommGrpCat.{u}) :=
  (additiveSkyscraperFunctor X p).obj A

/-- The stalk at `p` of a Zariski sheaf of abelian groups on `X`. -/
abbrev additiveStalkFunctor : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
    AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p

/-- The adjunction between the stalk functor at `p` and the skyscraper functor at `p`. -/
def additiveStalkSkyscraperAdjunction :
    additiveStalkFunctor X p ⊣ additiveSkyscraperFunctor X p :=
  _root_.stalkSkyscraperSheafAdjunction (X := X.carrier) p

local instance : HasExt.{u + 1} AddCommGrpCat.{u} := hasExt_of_enoughInjectives _

instance : (additiveStalkFunctor X p).Additive :=
  inferInstanceAs ((TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p).Additive)

instance : (additiveStalkFunctor X p).PreservesMonomorphisms :=
  inferInstanceAs ((TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p).PreservesMonomorphisms)

instance : PreservesFiniteLimits (additiveSkyscraperFunctor X p) :=
  inferInstanceAs (PreservesFiniteLimits (skyscraperSheafFunctor (X := X.carrier) p :
    AddCommGrpCat.{u} ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))

instance : PreservesFiniteLimits (additiveStalkFunctor X p) :=
  inferInstanceAs (PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p))

instance : PreservesFiniteColimits (additiveStalkFunctor X p) :=
  inferInstanceAs (PreservesFiniteColimits (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} p))

instance : (additiveSkyscraperFunctor X p).Additive :=
  (additiveStalkSkyscraperAdjunction X p).right_adjoint_additive

instance : (additiveSkyscraperFunctor X p).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (additiveStalkSkyscraperAdjunction X p)

instance : (additiveSkyscraperFunctor X p).PreservesEpimorphisms where
  preserves {A B} f _ := by
    apply (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier).epi_of_epi_map
    change Epi ((skyscraperPresheafFunctor (X := X.carrier) p).map f)
    have : ∀ U, Epi (((skyscraperPresheafFunctor (X := X.carrier) p).map f).app U) := by
      intro U
      change Epi ((SkyscraperPresheafFunctor.map' p f).app U)
      rw [SkyscraperPresheafFunctor.map'_app]
      by_cases h : p ∈ U.unop
      · rw [dite_eq_left h]
        infer_instance
      · rw [dite_eq_right h]
        apply (AddCommGrpCat.epi_iff_surjective _).mpr
        intro t
        refine ⟨0, ?_⟩
        rw [map_zero]
        have : Subsingleton ((skyscraperPresheaf p B).obj U) := by
          dsimp only [skyscraperPresheaf_obj]
          rw [ite_eq_right h]
          apply AddCommGrpCat.subsingleton_of_isZero
          exact (isZero_zero AddCommGrpCat.{u}).of_iso
            (terminalIsTerminal.uniqueUpToIso (isZero_zero AddCommGrpCat.{u}).isTerminal)
        exact Subsingleton.elim _ _
    exact NatTrans.epi_of_epi_app _

instance : (additiveSkyscraperFunctor X p).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

instance : PreservesFiniteColimits (additiveSkyscraperFunctor X p) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- Global sections of the skyscraper sheaf at `p`, identified additively with `A`. -/
def skyscraperGlobalSectionsEquiv (A : AddCommGrpCat.{u}) :
    (additiveSkyscraper X p A).obj.obj (op ⊤) ≃+ A :=
  (eqToIso (by simp [additiveSkyscraper, additiveSkyscraperFunctor,
    _root_.skyscraperSheafFunctor, _root_.skyscraperSheaf,
    _root_.skyscraperPresheaf_obj])).addCommGroupIsoToAddEquiv

theorem skyscraperGlobalSectionsEquiv_naturality {A B : AddCommGrpCat.{u}}
    (f : A ⟶ B) (s : (additiveSkyscraper X p A).obj.obj (op ⊤)) :
    skyscraperGlobalSectionsEquiv X p B
      (((additiveSkyscraperFunctor X p).map f).hom.app (op ⊤) s) =
      f (skyscraperGlobalSectionsEquiv X p A s) := by
  change (((additiveSkyscraperFunctor X p).map f).hom.app (op ⊤) ≫
    (eqToIso (by simp [additiveSkyscraperFunctor,
      _root_.skyscraperSheafFunctor, _root_.skyscraperSheaf,
      _root_.skyscraperPresheaf_obj])).hom) s = _
  have hcomp : ((additiveSkyscraperFunctor X p).map f).hom.app (op ⊤) ≫
      (eqToIso (by simp [additiveSkyscraperFunctor,
        _root_.skyscraperSheafFunctor, _root_.skyscraperSheaf,
        _root_.skyscraperPresheaf_obj])).hom =
      (eqToIso (by simp [additiveSkyscraperFunctor,
        _root_.skyscraperSheafFunctor, _root_.skyscraperSheaf,
        _root_.skyscraperPresheaf_obj])).hom ≫ f := by
    simp [_root_.skyscraperSheafFunctor,
    _root_.skyscraperPresheafFunctor, _root_.SkyscraperPresheafFunctor.map', Category.assoc]
  exact congrArg (fun k => k s) hcomp

/-- The stalk at `p` of the constant sheaf with value `ULift ℤ`. -/
abbrev integerSheafStalk := (additiveStalkFunctor X p).obj
  ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ)))

/-- Morphisms from the integer-sheaf stalk to `A`, identified additively with elements of `A`. -/
def integerSheafStalkHomEquiv (A : AddCommGrpCat.{u}) :
    (integerSheafStalk X p ⟶ A) ≃+ A :=
  ((additiveStalkSkyscraperAdjunction X p).homAddEquiv _ A).trans
    ((integerSheafHomEquiv (additiveSkyscraper X p A)).trans
      (skyscraperGlobalSectionsEquiv X p A))

theorem integerSheafStalkHomEquiv_comp {A B : AddCommGrpCat.{u}}
    (f : integerSheafStalk X p ⟶ A) (g : A ⟶ B) :
    integerSheafStalkHomEquiv X p B (f ≫ g) =
      g (integerSheafStalkHomEquiv X p A f) := by
  unfold integerSheafStalkHomEquiv
  simp only [AddEquiv.trans_apply, Adjunction.homAddEquiv_apply,
    Adjunction.homEquiv_naturality_right, integerSheafHomEquiv_comp,
    skyscraperGlobalSectionsEquiv_naturality]

instance : Projective (integerSheafStalk X p) where
  factors f e _ := by
    obtain ⟨s, hs⟩ := (AddCommGrpCat.epi_iff_surjective e).mp inferInstance
      (integerSheafStalkHomEquiv X p _ f)
    refine ⟨(integerSheafStalkHomEquiv X p _).symm s, ?_⟩
    apply (integerSheafStalkHomEquiv X p _).injective
    rw [integerSheafStalkHomEquiv_comp, AddEquiv.apply_symm_apply]
    exact hs

/-- Degree-`n` skyscraper cohomology, identified with degree-`n` Ext from the integer-sheaf stalk
to `A`. -/
def skyscraperCohomologyExtEquiv (A : AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H.{u + 1} (additiveSkyscraper X p A) n ≃+
      Abelian.Ext.{u + 1} (integerSheafStalk X p) A n :=
  (additiveStalkSkyscraperAdjunction X p).extEquiv.symm

theorem skyscraperCohomology_positive (A : AddCommGrpCat.{u}) (n : ℕ) :
    Subsingleton (Sheaf.H.{u + 1} (additiveSkyscraper X p A) (n + 1)) := by
  have := Abelian.Ext.subsingleton_of_projective (integerSheafStalk X p) A n
  exact (skyscraperCohomologyExtEquiv X p A (n + 1)).injective.subsingleton

/-- Degree-zero cohomology of the skyscraper sheaf at `p`, identified additively with `A`. -/
def skyscraperH0Equiv (A : AddCommGrpCat.{u}) :
    Sheaf.H.{u + 1} (additiveSkyscraper X p A) 0 ≃+ A :=
  (Sheaf.H.equiv₀ _ isTerminalTop).trans (skyscraperGlobalSectionsEquiv X p A)

theorem skyscraperH0Equiv_naturality {A B : AddCommGrpCat.{u}} (f : A ⟶ B)
    (x : Sheaf.H.{u + 1} (additiveSkyscraper X p A) 0) :
    skyscraperH0Equiv X p B (Sheaf.H.map ((additiveSkyscraperFunctor X p).map f) 0 x) =
      f (skyscraperH0Equiv X p A x) := by
  unfold skyscraperH0Equiv
  rw [AddEquiv.trans_apply, ← Sheaf.H.equiv₀_naturality,
    skyscraperGlobalSectionsEquiv_naturality]
  rfl

end AlgebraicGeometry.Scheme.Cohomology
