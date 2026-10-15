/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.FrameIndependence
public import Aglib.AlgebraicGeometry.Cohomology.Projective.TwistingCech
public import Aglib.Algebra.Homology.Simplex.Relative.Weights.Laurent
public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.ExactSequences

/-!
# The actual projective twist complex and its Laurent coefficients

The original full-tuple Cech complex of `O(d)` identifies with the native Laurent tuple
complex. Every tuple intersection is the actual coordinate-product open, and every face map
is its original section restriction followed by the proved degree-preserving Laurent map.
The comparison retains the projective structural-ring action and the actual `Sheaf.H` target.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Cech Opposite MvPolynomial
open AlgebraicGeometry.ProjectiveSpace

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The unchanged section presheaf of a projective twist over the actual structural ring. -/
abbrev twistingStructuralSections (d : ℤ) :
    (ProjectiveSpace R ι).Opensᵒᵖ ⥤ ModuleCat.{u} R :=
  moduleSectionsPresheaf (ProjectiveSpace R ι)
    ((toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom) (twistingSheaf R ι d)

/-- The original categorical tuple intersection is its actual coordinate-product basic open. -/
theorem coordinateTupleOpen_eq (n : ℕ) (a : Fin (n + 1) → ι) :
    tupleOpen (coordinateOpen R ι) n a =
      Proj.basicOpen (homogeneousSubmodule ι R) (coordinateProduct R ι (coordinateTupleSet a)) := by
  rw [basicOpen_coordinateProduct]
  apply le_antisymm
  · refine le_iInf fun i => le_iInf fun hi => ?_
    obtain ⟨k, rfl⟩ := (mem_coordinateTupleSet a i).mp hi
    exact tupleOpen_le (coordinateOpen R ι) n a k
  · exact leOfHom (Pi.lift fun k => homOfLE
      (iInf_le_of_le (a k) (iInf_le_of_le ((mem_coordinateTupleSet a (a k)).mpr ⟨k, rfl⟩)
        le_rfl)))

/-- The original section module on a categorical tuple intersection, expressed in its
homogeneous Laurent coordinates. The chosen zeroth coordinate does not affect this map. -/
def twistingTupleSectionsLinearEquiv (d : ℤ) (n : ℕ) (a : Fin (n + 1) → ι) :
    (twistingStructuralSections R ι d).obj (op (tupleOpen (coordinateOpen R ι) n a)) ≃ₗ[R]
      coordinateGrading R (coordinateTupleSet a) d :=
  ((twistingStructuralSections R ι d).mapIso
    (eqToIso (coordinateTupleOpen_eq R ι n a).symm).op).toLinearEquiv.trans
      (twistingSectionsLaurentLinearEquiv R ι (coordinateTupleSet a) (a 0)
        ((mem_coordinateTupleSet a (a 0)).mpr ⟨0, rfl⟩) d)

/-- Every actual tuple-position restriction becomes the original Laurent restriction on
its finite coordinate image. This includes all cofaces and codegeneracies. -/
theorem twistingTupleSectionsLinearEquiv_restrict (d : ℤ) {m n : ℕ}
    (a : Fin (n + 1) → ι) (θ : Fin (m + 1) → Fin (n + 1))
    (x : (twistingStructuralSections R ι d).obj
      (op (tupleOpen (coordinateOpen R ι) m (a ∘ θ)))) :
    twistingTupleSectionsLinearEquiv R ι d n a
        (sectionRes (twistingStructuralSections R ι d)
          (leOfHom (Pi.lift (fun k => Pi.π (fun l => coordinateOpen R ι (a l)) (θ k)))) x) =
      coordinateLaurentDegreeMap R (coordinateTupleSet_comp_subset a θ) d
        (twistingTupleSectionsLinearEquiv R ι d m (a ∘ θ) x) := by
  let P := twistingStructuralSections R ι d
  let s := coordinateTupleSet (a ∘ θ)
  let t := coordinateTupleSet a
  let h : s ⊆ t := coordinateTupleSet_comp_subset a θ
  let es := eqToIso (coordinateTupleOpen_eq R ι m (a ∘ θ)).symm
  let et := eqToIso (coordinateTupleOpen_eq R ι n a).symm
  let f := homOfLE (leOfHom
    (Pi.lift (fun k => Pi.π (fun l => coordinateOpen R ι (a l)) (θ k))))
  have hsquare : P.map et.hom.op (P.map f.op x) =
      P.map (homOfLE (coordinateProductOpen_le R ι h)).op (P.map es.hom.op x) := by
    change (P.map f.op ≫ P.map et.hom.op) x =
      (P.map es.hom.op ≫ P.map (homOfLE (coordinateProductOpen_le R ι h)).op) x
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun k => P.map k x) (Subsingleton.elim _ _)
  change twistingSectionsLaurentLinearEquiv R ι t (a 0)
      ((mem_coordinateTupleSet a (a 0)).mpr ⟨0, rfl⟩) d (P.map et.hom.op (P.map f.op x)) =
    coordinateLaurentDegreeMap R h d
      (twistingSectionsLaurentLinearEquiv R ι s ((a ∘ θ) 0)
        ((mem_coordinateTupleSet (a ∘ θ) ((a ∘ θ) 0)).mpr ⟨0, rfl⟩) d (P.map es.hom.op x))
  rw [hsquare]
  exact twistingSectionsLaurentLinearEquiv_restrict R ι h ((a ∘ θ) 0) (a 0)
    ((mem_coordinateTupleSet (a ∘ θ) ((a ∘ θ) 0)).mpr ⟨0, rfl⟩)
    ((mem_coordinateTupleSet a (a 0)).mpr ⟨0, rfl⟩) d (P.map es.hom.op x)

/-- The original categorical product of twist sections has exactly the tuple Laurent
coordinates, without imposing an ordering or removing repeated indices. -/
def twistingCechLaurentTermIso (d : ℤ) (n : ℕ) :
    ((cechComplexFunctor (coordinateOpen R ι)).obj (twistingStructuralSections R ι d)).X n ≅
      (coordinateLaurentTupleComplex (ι := ι) R d).X n :=
  ModuleCat.piIsoPi (fun a : Fin (n + 1) → ι =>
    (twistingStructuralSections R ι d).obj (op (tupleOpen (coordinateOpen R ι) n a))) ≪≫
      (LinearEquiv.piCongrRight (twistingTupleSectionsLinearEquiv R ι d n)).toModuleIso

/-- Each component of the Cech term isomorphism is the original local Laurent section map. -/
theorem twistingCechLaurentTermIso_hom_apply (d : ℤ) (n : ℕ)
    (x : ((cechComplexFunctor (coordinateOpen R ι)).obj
      (twistingStructuralSections R ι d)).X n) (a : Fin (n + 1) → ι) :
    (twistingCechLaurentTermIso R ι d n).hom x a =
      twistingTupleSectionsLinearEquiv R ι d n a
        (Pi.π (fun b : Fin (n + 1) → ι => (twistingStructuralSections R ι d).obj
          (op (tupleOpen (coordinateOpen R ι) n b))) a x) := by
  change twistingTupleSectionsLinearEquiv R ι d n a
    ((ModuleCat.piIsoPi (fun b : Fin (n + 1) → ι => (twistingStructuralSections R ι d).obj
      (op (tupleOpen (coordinateOpen R ι) n b)))).hom x a) = _
  exact congrArg (twistingTupleSectionsLinearEquiv R ι d n a)
    (ConcreteCategory.congr_hom (ModuleCat.piIsoPi_hom_ker_subtype _ a) x)

/-- The actual full-tuple Cech complex of every integer twist is isomorphic to the native
Laurent tuple complex, with its original alternating deletion differential. -/
def twistingCechLaurentIso (d : ℤ) :
    (cechComplexFunctor (coordinateOpen R ι)).obj (twistingStructuralSections R ι d) ≅
      coordinateLaurentTupleComplex (ι := ι) R d := by
  refine HomologicalComplex.Hom.isoOfComponents (twistingCechLaurentTermIso R ι d) ?_
  intro n m hnm
  obtain rfl : n + 1 = m := hnm
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext a
  symm
  change (twistingCechLaurentTermIso R ι d (n + 1)).hom
      (((cechComplexFunctor (coordinateOpen R ι)).obj (twistingStructuralSections R ι d)).d
        n (n + 1) x) a =
    (coordinateLaurentTupleComplex (ι := ι) R d).d n (n + 1)
      ((twistingCechLaurentTermIso R ι d n).hom x) a
  rw [twistingCechLaurentTermIso_hom_apply, coordinateLaurentTupleComplex_d_apply,
    cech_d_apply_component, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_zsmul, twistingCechLaurentTermIso_hom_apply]
  congr 1
  exact twistingTupleSectionsLinearEquiv_restrict R ι d a j.succAbove
    (Pi.π (fun b : Fin (n + 1) → ι => (twistingStructuralSections R ι d).obj
      (op (tupleOpen (coordinateOpen R ι) n b))) (a ∘ j.succAbove) x)

/-- The native Laurent tuple complex computes the unchanged `Sheaf.H` of the actual twist
in every degree, linearly over the original projective structural ring. -/
def twistingLaurentCohomologyLinearEquiv (d : ℤ) (n : ℕ) :
    let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
      (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α (twistingSheaf R ι d) n
    (coordinateLaurentTupleComplex (ι := ι) R d).homology n ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) (twistingSheaf R ι d)) n := by
  let α : R →+* Γ(ProjectiveSpace R ι, ⊤) :=
    (toSpec R ι).appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  letI := moduleCohomologyModuleOfHom (ProjectiveSpace R ι) α (twistingSheaf R ι d) n
  exact (((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) n).mapIso
    (twistingCechLaurentIso R ι d)).symm.toLinearEquiv).trans
      (twistingCechCohomologyLinearEquivAll R ι d n)

end AlgebraicGeometry.Scheme.Cohomology
