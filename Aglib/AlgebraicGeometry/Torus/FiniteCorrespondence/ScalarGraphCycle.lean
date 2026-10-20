/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Module.Automorphism.ScalarGraphLengths
public import Aglib.AlgebraicGeometry.Torus.FiniteCorrespondence.ModuleCycle

/-!
# ScalarGraphCycle for finite correspondences on the two-dimensional torus

Native migration from `lean/R5Lab/Aglib/AlgebraicGeometry/Torus/FiniteCorrespondence/`
leaf `ScalarGraphCycle.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`27347c1cf3d211322bc227971bdd2591ae72537abb6b225403d486a7dd40a9d4`.

The Laurent object is `MonoidAlgebra R (Multiplicative (ℤ × ℤ))` in its original
coordinate order. Statements retain their displayed finiteness, normality,
Noetherianity, flatness, regularity and scalar-map hypotheses.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace AlgebraicGeometry.Torus.FiniteCorrespondence.ScalarGraph
open _root_.Module.CommutingAutomorphisms
open _root_.Module.CommutingAutomorphisms.LaurentSupport
open MonoidAlgebra (FiniteDominantPrime)
open _root_.Module.Automorphism.ScalarGraph
universe u
variable {R : Type u} [CommRing R]

/-- Finite prime labels contracting to zero on the literal one-dimensional torus. -/
def OnePoint (R : Type u) [CommRing R] :=
  {q : Ideal (OneLaurent R) // q.IsPrime ∧ Module.Finite R (OneLaurent R ⧸ q) ∧ q.under R = ⊥}
/-- The ideal underlying a one-torus point label is prime. -/
instance onePointPrime (q : OnePoint R) : q.val.IsPrime := q.property.1
/-- The quotient associated to a one-torus point label is finite over the coefficient ring. -/
instance onePointFinite (q : OnePoint R) : Module.Finite R (OneLaurent R ⧸ q.val) := q.property.2.1

/-- Scalar-graph substitution followed by the quotient onto the one-variable Laurent algebra
modulo `q`. -/
def graphQuotientMap (f : Rˣ) (q : Ideal (OneLaurent R)) : Laurent R →ₐ[R] OneLaurent R ⧸ q :=
  (Ideal.Quotient.mkₐ R q).comp (graphMap f)

theorem graphQuotientMap_kernel (f : Rˣ) (q : Ideal (OneLaurent R)) :
    RingHom.ker (graphQuotientMap f q) = q.comap (graphMap f).toRingHom := by
  ext p
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The original residue algebra on every graph prime is the source residue
algebra itself; the graph introduces no residue degree or nilpotent thickening. -/
def graphQuotientEquiv (f : Rˣ) (q : Ideal (OneLaurent R)) :
    (Laurent R ⧸ (q.comap (graphMap f).toRingHom)) ≃ₐ[R] (OneLaurent R ⧸ q) :=
  (Ideal.quotientEquivAlgOfEq R (graphQuotientMap_kernel f q).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (Ideal.Quotient.mk_surjective.comp (graphMap_surjective f)))

theorem graphPrime_under_base (f : Rˣ) (q : Ideal (OneLaurent R)) :
    (q.comap (graphMap f).toRingHom).under R = q.under R := by
  ext r
  change graphMap f (algebraMap R (Laurent R) r) ∈ q ↔ algebraMap R (OneLaurent R) r ∈ q
  rw [(graphMap f).commutes]

/-- Actual graph pushforward x↦(x,f), on the existing two-torus prime labels. -/
def graphPoint (f : Rˣ) (q : OnePoint R) : MonoidAlgebra.FiniteDominantPrime R := by
  refine ⟨q.val.comap (graphMap f).toRingHom, inferInstance, ?_, ?_⟩
  · exact Module.Finite.of_surjective (graphQuotientEquiv f q.val).symm.toLinearMap
      (graphQuotientEquiv f q.val).symm.surjective
  · exact (graphPrime_under_base f q.val).trans q.property.2.2

theorem graphPoint_injective (f : Rˣ) : Function.Injective (graphPoint f) := by
  intro q r h
  apply Subtype.ext
  exact Ideal.comap_injective_of_surjective (graphMap f).toRingHom (graphMap_surjective f)
    (congrArg Subtype.val h)

/-- The natural-number interpretation of the extended local length of `X` at the one-torus prime
`q`. -/
def oneCoefficient (X : Module.Automorphism.Object R) (q : OnePoint R) : ℕ :=
  (oneAmbientLength X q.val).toNat

theorem coefficient_graph (X : Module.Automorphism.Object R) (f : Rˣ) (q : OnePoint R) :
    Module.CommutingAutomorphisms.coefficient (graphObject X f) (graphPoint f q) = oneCoefficient
      X q := by
  exact congrArg ENat.toNat (ambientLength_graph_eq_one X f q.val)

theorem coefficient_tensor_graph (X : Module.Automorphism.Object R) (f : Rˣ) (q : OnePoint R) :
    Module.CommutingAutomorphisms.coefficient (X.tensor (Module.Automorphism.Object.unit f))
      (graphPoint f q) =
      oneCoefficient X q := by
  exact congrArg ENat.toNat (ambientLength_tensor_eq_one X f q.val)

theorem oneCoefficient_length [IsNoetherianRing R] (X : Module.Automorphism.Object R) (q :
    OnePoint R) :
    (oneCoefficient X q : ℕ∞) = oneAmbientLength X q.val := by
  apply ENat.natCast_toNat
  rw [← ambientLength_graph_eq_one X (1 : Rˣ) q.val]
  exact Module.CommutingAutomorphisms.pointLength_ne_top (graphObject X 1) (graphPoint 1 q)

theorem oneCoefficient_finiteSupport [IsNoetherianRing R] (X : Module.Automorphism.Object R) :
    (Function.support (oneCoefficient X)).Finite := by
  have h : Function.support (oneCoefficient X) =
      graphPoint (1 : Rˣ) ⁻¹' Function.support (Module.CommutingAutomorphisms.coefficient
        (graphObject X 1)) := by
    ext q
    simp only [Function.mem_support, Set.mem_preimage, coefficient_graph]
  rw [h]
  exact (Module.CommutingAutomorphisms.coefficient_finiteSupport (graphObject X 1)).preimage
    (graphPoint_injective (1 : Rˣ)).injOn

/-- The finitely supported integer local-length coefficients of the one-automorphism object `X`. -/
def oneCoefficients [IsNoetherianRing R] (X : Module.Automorphism.Object R) : OnePoint R →₀ ℤ :=
  Finsupp.ofSupportFinite (fun q => (oneCoefficient X q : ℤ)) (by
    have h : Function.support (fun q => (oneCoefficient X q : ℤ)) =
        Function.support (oneCoefficient X) := by ext q; simp
    rw [h]
    exact oneCoefficient_finiteSupport X)

/-- The actual one-torus cycle, from original module lengths. -/
def oneObjectCycle [IsNoetherianRing R] (X : Module.Automorphism.Object R) : FreeAbelianGroup
    (OnePoint R) :=
  Finsupp.toFreeAbelianGroup (oneCoefficients X)

@[simp] theorem oneObjectCycle_coeff [IsNoetherianRing R] (X : Module.Automorphism.Object R) (q :
    OnePoint R) :
    FreeAbelianGroup.coeff q (oneObjectCycle X) = (oneCoefficient X q : ℤ) := by
  simp [FreeAbelianGroup.coeff, oneObjectCycle, oneCoefficients]

/-- The additive pushforward of one-torus cycles along the scalar graph `x ↦ (x, f)`. -/
def graphCycles (f : Rˣ) : FreeAbelianGroup (OnePoint R) →+ FreeAbelianGroup
    (MonoidAlgebra.FiniteDominantPrime R) :=
  FreeAbelianGroup.map (graphPoint f)

theorem graphCycles_coeff (f : Rˣ) (q : OnePoint R) (c : FreeAbelianGroup (OnePoint R)) :
    FreeAbelianGroup.coeff (graphPoint f q) (graphCycles f c) = FreeAbelianGroup.coeff q c := by
  classical
  have h : (FreeAbelianGroup.coeff (graphPoint f q)).comp (graphCycles f) =
      FreeAbelianGroup.coeff q := by
    apply FreeAbelianGroup.lift_ext
    intro r
    simp [graphCycles, FreeAbelianGroup.coeff, Finsupp.single_apply,
      (graphPoint_injective f).eq_iff]
  exact DFunLike.congr_fun h c

theorem graphCycles_coeff_off (f : Rˣ) (p : MonoidAlgebra.FiniteDominantPrime R)
    (hp : ¬ ∃ q : OnePoint R, graphPoint f q = p) (c : FreeAbelianGroup (OnePoint R)) :
    FreeAbelianGroup.coeff p (graphCycles f c) = 0 := by
  have h : (FreeAbelianGroup.coeff p).comp (graphCycles f) = 0 := by
    apply FreeAbelianGroup.lift_ext
    intro q
    have hq : graphPoint f q ≠ p := fun h => hp ⟨q, h⟩
    simp [graphCycles, FreeAbelianGroup.coeff, hq.symm]
  exact DFunLike.congr_fun h c

/-- Every nonzero target coefficient lies on a literal scalar graph point.
The inverse label is derived by the surjective ideal correspondence. -/
theorem exists_graphPoint_of_coefficient_ne_zero [IsNoetherianRing R]
    (X : Module.Automorphism.Object R) (f : Rˣ) (p : MonoidAlgebra.FiniteDominantPrime R)
    (hp : Module.CommutingAutomorphisms.coefficient (X.tensor (Module.Automorphism.Object.unit
      f)) p ≠ 0) :
    ∃ q : OnePoint R, graphPoint f q = p := by
  have hlen : Module.CommutingAutomorphisms.ambientLength (X.tensor
    (Module.Automorphism.Object.unit f)) p.val ≠ 0 := by
    intro h
    exact hp (by simp [Module.CommutingAutomorphisms.coefficient, h])
  have hI : supportIdeal (X.tensor (Module.Automorphism.Object.unit f)) ≤ p.val :=
    (Module.CommutingAutomorphisms.pointLength_support _ p hlen).le
  have hk : RingHom.ker (graphMap f).toRingHom ≤ p.val := by
    apply le_trans ?_ hI
    rw [supportIdeal_tensor_graph]
    intro a ha
    change oneRepresentation X (graphMap f a) = 0
    have hz : graphMap f a = 0 := RingHom.mem_ker.mp ha
    rw [hz, map_zero]
  let q : Ideal (OneLaurent R) := p.val.map (graphMap f).toRingHom
  let : q.IsPrime := Ideal.map_isPrime_of_surjective (graphMap_surjective f) hk
  have hq : q.comap (graphMap f).toRingHom = p.val := by
    rw [Ideal.comap_map_of_surjective (graphMap f).toRingHom (graphMap_surjective f)]
    change p.val ⊔ RingHom.ker (graphMap f).toRingHom = p.val
    exact sup_eq_left.mpr hk
  let : Module.Finite R (Laurent R ⧸ (q.comap (graphMap f).toRingHom)) := by
    rw [hq]
    infer_instance
  have hfin : Module.Finite R (OneLaurent R ⧸ q) :=
    Module.Finite.of_injective (graphQuotientEquiv f q).symm.toLinearMap
      (graphQuotientEquiv f q).symm.injective
  have hdom : q.under R = ⊥ := by
    rw [← graphPrime_under_base f q, hq]
    exact MonoidAlgebra.FiniteDominantPrime.under_eq_bot p
  refine ⟨⟨q, inferInstance, hfin, hdom⟩, ?_⟩
  exact Subtype.ext hq

theorem coefficient_tensor_off_graph [IsNoetherianRing R]
    (X : Module.Automorphism.Object R) (f : Rˣ) (p : MonoidAlgebra.FiniteDominantPrime R)
    (hp : ¬ ∃ q : OnePoint R, graphPoint f q = p) :
    Module.CommutingAutomorphisms.coefficient (X.tensor (Module.Automorphism.Object.unit f)) p =
      0 := by
  by_contra h
  exact hp (exists_graphPoint_of_coefficient_ne_zero X f p h)

/-- LITERAL original-cycle equality: tensoring on the right by the scalar
pushes the actual one-torus cycle along x↦(x,f), with no sign or degree factor. -/
theorem objectCycle_tensor_graph [IsNoetherianRing R] (X : Module.Automorphism.Object R) (f : Rˣ) :
    AlgebraicGeometry.Torus.FiniteCorrespondence.objectCycle (X.tensor
      (Module.Automorphism.Object.unit f)) =
      graphCycles f (oneObjectCycle X) := by
  classical
  apply (FreeAbelianGroup.equivFinsupp (MonoidAlgebra.FiniteDominantPrime R)).injective
  ext p
  change FreeAbelianGroup.coeff p (AlgebraicGeometry.Torus.FiniteCorrespondence.objectCycle _) =
    FreeAbelianGroup.coeff p (graphCycles f (oneObjectCycle X))
  by_cases hp : ∃ q : OnePoint R, graphPoint f q = p
  · obtain ⟨q, rfl⟩ := hp
    rw [AlgebraicGeometry.Torus.FiniteCorrespondence.objectCycle_coeff, coefficient_tensor_graph,
      graphCycles_coeff, oneObjectCycle_coeff]
  · rw [AlgebraicGeometry.Torus.FiniteCorrespondence.objectCycle_coeff,
    coefficient_tensor_off_graph X f p hp,
      graphCycles_coeff_off f p hp]
    rfl

/-- The isomorphism of scalar-graph objects induced by an isomorphism of one-automorphism
objects. -/
def graphIso {X Y : Module.Automorphism.Object R} (e : Module.Automorphism.Object.Iso X Y) (f :
    Rˣ) :
    Object.Iso (graphObject X f) (graphObject Y f) where
  linearEquiv := e.linearEquiv
  commute_a := e.commute_a
  commute_b x := e.linearEquiv.map_smul (f : R) x

/-- The scalar graph of a direct sum identified with the direct sum of the scalar graphs. -/
def graphSumIso (X Y : Module.Automorphism.Object R) (f : Rˣ) :
    Object.Iso (graphObject (X.sum Y) f) ((graphObject X f).sum (graphObject Y f)) where
  linearEquiv := LinearEquiv.refl R (X.carrier × Y.carrier)
  commute_a _ := rfl
  commute_b _ := rfl

theorem oneCoefficient_iso {X Y : Module.Automorphism.Object R} (e :
    Module.Automorphism.Object.Iso X Y)
    (q : OnePoint R) : oneCoefficient X q = oneCoefficient Y q := by
  rw [← coefficient_graph X (1 : Rˣ) q, Module.CommutingAutomorphisms.coefficient_iso (graphIso e
    1),
    coefficient_graph]

theorem oneCoefficient_sum [IsNoetherianRing R] (X Y : Module.Automorphism.Object R) (q :
    OnePoint R) :
    oneCoefficient (X.sum Y) q = oneCoefficient X q + oneCoefficient Y q := by
  rw [← coefficient_graph (X.sum Y) (1 : Rˣ) q,
    Module.CommutingAutomorphisms.coefficient_iso (graphSumIso X Y 1),
      Module.CommutingAutomorphisms.coefficient_sum,
    coefficient_graph, coefficient_graph]

theorem oneObjectCycle_iso [IsNoetherianRing R] {X Y : Module.Automorphism.Object R}
    (e : Module.Automorphism.Object.Iso X Y) : oneObjectCycle X = oneObjectCycle Y := by
  apply congrArg Finsupp.toFreeAbelianGroup
  ext q
  exact congrArg (fun n : ℕ => (n : ℤ)) (oneCoefficient_iso e q)

theorem oneObjectCycle_sum [IsNoetherianRing R] (X Y : Module.Automorphism.Object R) :
    oneObjectCycle (X.sum Y) = oneObjectCycle X + oneObjectCycle Y := by
  unfold oneObjectCycle
  rw [← map_add]
  apply congrArg Finsupp.toFreeAbelianGroup
  ext q
  change (oneCoefficient (X.sum Y) q : ℤ) = (oneCoefficient X q : ℤ) + (oneCoefficient Y q : ℤ)
  rw [oneCoefficient_sum, Nat.cast_add]

/-- The distinguished Laurent coordinate of the one-dimensional torus. -/
def oneCoordinate (R : Type u) [CommRing R] : OneLaurent R :=
  MonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) 1

/-- The condition that the one-torus prime contains the equation `t - 1` of the identity point. -/
def OneOnIdentityAxis (q : OnePoint R) : Prop := oneCoordinate R - 1 ∈ q.val

theorem graphPoint_first_axis (f : Rˣ) (q : OnePoint R) (hq : OneOnIdentityAxis q) :
    AlgebraicGeometry.Torus.FiniteCorrespondence.OnIdentityAxis (graphPoint f q) := by
  apply Or.inl
  change graphMap f (firstCoordinate R - 1) ∈ q.val
  simpa only [map_sub, map_one, graphMap_first, OneOnIdentityAxis, oneCoordinate] using hq

theorem oneAxis_of_degenerate_coefficient [IsNoetherianRing R] (X : Module.Automorphism.Object R)
    (ha : X.a = LinearEquiv.refl R X.carrier) (q : OnePoint R)
    (hq : oneCoefficient X q ≠ 0) : OneOnIdentityAxis q := by
  have hcoef : Module.CommutingAutomorphisms.coefficient (graphObject X 1) (graphPoint 1 q) ≠ 0
    := by
    rwa [coefficient_graph]
  have hlen : Module.CommutingAutomorphisms.ambientLength (graphObject X 1) (graphPoint 1 q).val
    ≠ 0 := by
    intro h
    exact hcoef (by simp [Module.CommutingAutomorphisms.coefficient, h])
  have hI := (Module.CommutingAutomorphisms.pointLength_support (graphObject X 1) (graphPoint 1
    q) hlen).le
  have hg := hI (first_identity_relation (graphObject X 1) ha)
  change graphMap (1 : Rˣ) (firstCoordinate R - 1) ∈ q.val at hg
  simpa only [map_sub, map_one, graphMap_first, OneOnIdentityAxis, oneCoordinate] using hg

end AlgebraicGeometry.Torus.FiniteCorrespondence.ScalarGraph
