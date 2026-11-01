/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.GenericStalk
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Support
public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Hyperplane
public import Aglib.AlgebraicGeometry.Modules.Tensor.Restriction
public import Aglib.Topology.KrullDimension.ClosedSubspace
public import Mathlib.RingTheory.Artinian.Module

/-!
# Support dimension drops under monic tensor twisting

A monomorphism between coherent modules with isomorphic actual stalks is
an isomorphism at every generic point of their support: those stalks have
finite length. Its cokernel therefore avoids the support component generic
points. The existing closed-subspace dimension theorem gives the strict
dimension drop. Tensoring by the original projective twisting sheaf has
the required stalk isomorphisms, constructed from its actual standard
frames and restriction comparisons.

This supplies the geometric dimension-drop step for the native hyperplane
finite-difference argument. It does not yet identify Hilbert polynomial
degree with support dimension or assert finite-map rank scaling.
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A map between modules with isomorphic actual stalks has cokernel
supported on their common support. No coherence is needed here. -/
theorem support_cokernel_subset_of_stalkIso {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N)
    (he : ∀ x : X, Nonempty ((moduleStalk X x).obj N ≅ (moduleStalk X x).obj M)) :
    support (cokernel f) ⊆ support M := by
  intro x hx
  by_contra hM
  have hzM : IsZero ((moduleStalk X x).obj M) :=
    (Coherent.Support.moduleStalk_isZero_iff X M x).mpr (not_not.mp hM)
  obtain ⟨e⟩ := he x
  have hzN : IsZero ((moduleStalk X x).obj N) := hzM.of_iso e
  let : Epi ((moduleStalk X x).map f) := hzN.epi _
  have hz : IsZero ((moduleStalk X x).obj (cokernel f)) :=
    (isZero_cokernel_of_epi ((moduleStalk X x).map f)).of_iso
      (PreservesCokernel.iso (moduleStalk X x) f)
  exact hx ((Coherent.Support.moduleStalk_isZero_iff X (cokernel f) x).mp hz)

/-- A monomorphism between stalk-isomorphic coherent modules is an
isomorphism at a generic point of the actual support. Consequently its
original cokernel stalk is zero there. -/
theorem isZero_stalk_cokernel_of_genericPoint_support
    {X : Scheme.{u}} [IsLocallyNoetherian X] {M N : X.Modules}
    (f : M ⟶ N) [Mono f] (hM : affineLocallyFiniteType X M)
    (he : ∀ x : X, Nonempty ((moduleStalk X x).obj N ≅ (moduleStalk X x).obj M))
    (x : support M) (hx : x ∈ genericPoints (support M)) :
    IsZero ((moduleStalk X x.1).obj (cokernel f)) := by
  have hlen := Stalk.finiteLength_stalk_of_genericPoint_support M hM x hx
  let : IsArtinian (X.presheaf.stalk x.1) ((moduleStalk X x.1).obj M) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hlen).2
  obtain ⟨e⟩ := he x.1
  let g := (moduleStalk X x.1).map f ≫ e.hom
  have hgi : Function.Injective g.hom := (ModuleCat.mono_iff_injective g).mp inferInstance
  have hgs : Function.Surjective g.hom := IsArtinian.surjective_of_injective_endomorphism g.hom hgi
  let : Epi g := (ModuleCat.epi_iff_surjective g).mpr hgs
  have hg : (moduleStalk X x.1).map f = g ≫ e.inv := by simp [g]
  let : Epi ((moduleStalk X x.1).map f) := by
    rw [hg]
    infer_instance
  exact (isZero_cokernel_of_epi ((moduleStalk X x.1).map f)).of_iso
    (PreservesCokernel.iso (moduleStalk X x.1) f)

/-- The cokernel of a monomorphism between coherent modules with
isomorphic stalks has support dimension at most `d` when their original
support has dimension at most `d + 1`. Empty support is included. -/
theorem topologicalKrullDim_support_cokernel_le_of_stalkIso
    {X : Scheme.{u}} [IsLocallyNoetherian X] {M N : X.Modules}
    (f : M ⟶ N) [Mono f] (hM : affineLocallyFiniteType X M)
    (hN : affineLocallyFiniteType X N)
    (he : ∀ x : X, Nonempty ((moduleStalk X x).obj N ≅ (moduleStalk X x).obj M))
    (d : ℕ) (hd : topologicalKrullDim (support M) ≤ (d + 1 : ℕ)) :
    topologicalKrullDim (support (cokernel f)) ≤ (d : ℕ) := by
  have hC := (affineLocallyFiniteType X).prop_cokernel f hM hN
  have hMclosed := isClosed_support_of_affineLocallyFiniteType hM
  have hCclosed := isClosed_support_of_affineLocallyFiniteType hC
  have hsub := support_cokernel_subset_of_stalkIso f he
  let : QuasiSober (support M) := hMclosed.isClosedEmbedding_subtypeVal.quasiSober
  let Z : Set (support M) := Subtype.val ⁻¹' support (cokernel f)
  have hZclosed : IsClosed Z := hCclosed.preimage continuous_subtype_val
  have hZgeneric : Disjoint Z (genericPoints (support M)) := by
    rw [Set.disjoint_left]
    intro x hx hxg
    have hz := isZero_stalk_cokernel_of_genericPoint_support f hM he x hxg
    exact hx ((Coherent.Support.moduleStalk_isZero_iff X (cokernel f) x.1).mp hz)
  have hZdim := topologicalKrullDim_closed_le_of_avoids_genericPoints Z hZclosed hZgeneric d hd
  let e : Z ≃ₜ support (cokernel f) :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun x => ⟨⟨x.1, hsub x.2⟩, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk
        (fun x => x.2)
      continuous_invFun := (continuous_subtype_val.subtype_mk (fun x => hsub x.2)).subtype_mk
        (fun x => x.2) }
  rw [← IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph]
  exact hZdim

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- An original standard frame gives an actual stalk isomorphism from a
tensor twist to the original coefficient. Only existence is asserted. -/
theorem nonempty_twistingTensor_stalkIso (M : (ProjectiveSpace R ι).Modules)
    (a : ℤ) (x : ProjectiveSpace R ι) :
    Nonempty ((moduleStalk (ProjectiveSpace R ι) x).obj
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj M) ≅
      (moduleStalk (ProjectiveSpace R ι) x).obj M) := by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, coordinateOpen R ι i by
    rw [iSup_coordinateOpen_eq_top]
    trivial)
  let U := coordinateOpen R ι i
  let x' : U.toScheme := ⟨x, hi⟩
  let N := (moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι a)).obj M
  let e : N.restrict U.ι ≅ M.restrict U.ι :=
    (tensorRestrictionIso U.ι (twistingSheaf R ι a) M).symm ≪≫
      ((SheafOfModulesOfCommRing.tensorFunctor U.toScheme.sheaf).mapIso
        (twistingRestrictUnitIso R ι a i)).app (M.restrict U.ι) ≪≫
      (SheafOfModulesOfCommRing.tensorLeftUnitIso U.toScheme.sheaf).app (M.restrict U.ι)
  exact ⟨((restrictModuleStalkIso U.ι x').app N).symm ≪≫
    (ModuleCat.restrictScalars (U.ι.stalkMap x').hom).mapIso
      ((moduleStalk U.toScheme x').mapIso e) ≪≫
    (restrictModuleStalkIso U.ι x').app M⟩

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.Cohomology

open AlgebraicGeometry.ProjectiveSpace

/-- The original cokernel of a monomorphism into a projective tensor twist
has strictly smaller support dimension. The native frame construction
discharges every stalk-isomorphism condition. -/
theorem topologicalKrullDim_support_cokernel_mono_twist_le
    (k : Type u) [Field k] (ι : Type u) [Finite ι]
    (M : (ProjectiveSpace k ι).Modules) (hM : affineLocallyFiniteType _ M) (a : ℤ)
    (f : M ⟶ (moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι a)).obj M)
    [Mono f] (d : ℕ) (hd : topologicalKrullDim (support M) ≤ (d + 1 : ℕ)) :
    topologicalKrullDim (support (cokernel f)) ≤ (d : ℕ) :=
  topologicalKrullDim_support_cokernel_le_of_stalkIso f hM
    (twistingTensor_affineLocallyFiniteType k ι a M hM)
    (nonempty_twistingTensor_stalkIso k ι M a) d hd

end AlgebraicGeometry.Scheme.Cohomology
