/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Etale.MilnorPatching
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.LocalRing.Pullback
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Finite-free clutching over literal Milnor squares

The quotient comparison preserves the actual boundary map. Finite-free
clutching is proved finite and flat by an explicit stable retraction; finite
presentation follows over a Noetherian fibre base. The universal proposition
`EtalePatching` remains conditional: formal unramifiedness is not proved here.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace RingHom.Etale.MilnorPatching

universe u v w z

section Boundary

variable {R : Type u} {C : Type v} {T : Type w} {U : Type z}
  [CommRing R] [CommRing C] [CommRing T] [CommRing U]
  [Algebra R C] [Algebra R T] [Algebra T U]

/-- A surjective base boundary and the actual tensor equivalence identify the
quotient by the extended kernel with the displayed boundary algebra. -/
def quotientBoundaryEquiv
    (hf : Function.Surjective (algebraMap R T))
    (e : T ⊗[R] C ≃ₐ[T] U) :
    (C ⧸ (RingHom.ker (algebraMap R T)).map (algebraMap R C)) ≃+* U := by
  let eR : (R ⧸ RingHom.ker (algebraMap R T)) ≃ₐ[R] T :=
    { __ := RingHom.quotientKerEquivOfSurjective hf
      commutes' := fun _ => rfl }
  exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C
    (RingHom.ker (algebraMap R T))).toRingEquiv.trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl : C ≃ₐ[C] C) eR).toRingEquiv.trans <|
    (Algebra.TensorProduct.comm R C T).toRingEquiv.trans e.toRingEquiv

@[simp]
theorem quotientBoundaryEquiv_mk
    (hf : Function.Surjective (algebraMap R T))
    (e : T ⊗[R] C ≃ₐ[T] U) (c : C) :
    quotientBoundaryEquiv hf e (Ideal.Quotient.mk _ c) = e (1 ⊗ₜ[R] c) := by
  simp [quotientBoundaryEquiv,
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]

/-- The specified boundary map is surjective, rather than merely having an
isomorphic codomain. No flatness or Noetherian hypothesis is needed. -/
theorem surjective_boundary_of_tensorEquiv
    (hf : Function.Surjective (algebraMap R T))
    (b : C →+* U) (e : T ⊗[R] C ≃ₐ[T] U)
    (he : ∀ c, e (1 ⊗ₜ[R] c) = b c) : Function.Surjective b := by
  intro x
  obtain ⟨y, hy⟩ := (quotientBoundaryEquiv hf e).surjective x
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨c, (he c).symm.trans ((quotientBoundaryEquiv_mk hf e c).symm.trans hy)⟩

/-- The kernel of the specified boundary map is the extension of the actual
base-boundary kernel. -/
theorem ker_boundary_of_tensorEquiv
    (hf : Function.Surjective (algebraMap R T))
    (b : C →+* U) (e : T ⊗[R] C ≃ₐ[T] U)
    (he : ∀ c, e (1 ⊗ₜ[R] c) = b c) :
    RingHom.ker b = (RingHom.ker (algebraMap R T)).map (algebraMap R C) := by
  ext c
  rw [RingHom.mem_ker, ← he c, ← quotientBoundaryEquiv_mk hf e c,
    (quotientBoundaryEquiv hf e).map_eq_zero_iff,
    Ideal.Quotient.eq_zero_iff_mem]

end Boundary

section Generation

variable {R S T C D U : Type u}
  [CommRing R] [CommRing S] [CommRing T] [CommRing C] [CommRing D] [CommRing U]
  [Algebra R C] [Algebra R T] [Algebra T U] [Algebra S T] [Algebra S D]

/-- The first components of the literal fibre ring generate the normalization
side as a module over its original base. This is the surjectivity part of the
normalization-side reconstruction, with the specified tensor maps. -/
theorem span_fst_fiberRing_eq_top
    (hf : Function.Surjective (algebraMap R T))
    (b : C →+* U) (v : D →+* U)
    (hb : b.comp (algebraMap R C) =
      (algebraMap T U).comp (algebraMap R T))
    (eC : T ⊗[R] C ≃ₐ[T] U) (eD : T ⊗[S] D ≃ₐ[T] U)
    (heC : ∀ c, eC (1 ⊗ₜ[R] c) = b c)
    (heD : ∀ d, eD (1 ⊗ₜ[S] d) = v d) :
    Submodule.span R (Set.range (fun x : fiberRing b v => x.val.1)) = ⊤ := by
  let N := Submodule.span R (Set.range (fun x : fiberRing b v => x.val.1))
  have hu : Function.Surjective b := surjective_boundary_of_tensorEquiv hf b eC heC
  have hker (c : C) (hc : b c = 0) : c ∈ N := by
    apply Submodule.subset_span
    exact ⟨⟨(c, 0), by change b c = v 0; simpa using hc⟩, rfl⟩
  have hlift (z : T ⊗[S] D) : ∃ c ∈ N, b c = eD z := by
    induction z using TensorProduct.inductionOn with
    | tmul t d =>
      obtain ⟨a, rfl⟩ := hf t
      obtain ⟨c, hc⟩ := hu (v d)
      have hcN : c ∈ N := Submodule.subset_span ⟨⟨(c, d), hc⟩, rfl⟩
      refine ⟨a • c, N.smul_mem a hcN, ?_⟩
      calc
        b (a • c) = algebraMap T U (algebraMap R T a) * v d := by
          rw [Algebra.smul_def, map_mul, hc]
          exact congrArg (· * v d) (show b (algebraMap R C a) =
            algebraMap T U (algebraMap R T a) from RingHom.congr_fun hb a)
        _ = eD ((algebraMap R T a) • (1 ⊗ₜ[S] d)) := by
          rw [map_smul, heD, Algebra.smul_def]
        _ = eD (algebraMap R T a ⊗ₜ[S] d) := by simp [Algebra.smul_def]
    | add x y hx hy =>
      obtain ⟨c, hc, hcx⟩ := hx
      obtain ⟨d, hd, hdy⟩ := hy
      exact ⟨c + d, N.add_mem hc hd, by rw [map_add, hcx, hdy, map_add]⟩
  apply top_unique
  intro c _
  obtain ⟨z, hz⟩ := eD.surjective (b c)
  obtain ⟨d, hd, hbd⟩ := hlift z
  have hdiff : c - d ∈ N := hker (c - d) (by rw [map_sub, hbd, hz, sub_self])
  simpa using N.add_mem hdiff hd

end Generation


namespace FiniteFree

section Modules

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  {ι : Type v} (f : R →+* T) (g : S →+* T)

local notation "P" => fiberRing f g

local instance fstAlgebra : Algebra P R := (RingHom.pullbackFst f g).toAlgebra
local instance sndAlgebra : Algebra P S := (RingHom.pullbackSnd f g).toAlgebra

private theorem coefficients_smul (h : R →+* T) (a : R) (x : ι → R) :
    h.compLeft ι (a • x) = h a • h.compLeft ι x := by
  ext i
  exact map_mul h a (x i)

/-- The module of pairs with the specified finite-free clutching relation. -/
def clutch (e : (ι → T) ≃ₗ[T] (ι → T)) :
    Submodule P ((ι → R) × (ι → S)) where
  carrier := {x | f.compLeft ι x.1 = e (g.compLeft ι x.2)}
  zero_mem' := by
    change f.compLeft ι 0 = e (g.compLeft ι 0)
    simp
  add_mem' {x y} hx hy := by
    change f.compLeft ι (x.1 + y.1) = e (g.compLeft ι (x.2 + y.2))
    rw [map_add, map_add, hx, hy, map_add]
  smul_mem' a x hx := by
    change f.compLeft ι (a.val.1 • x.1) = e (g.compLeft ι (a.val.2 • x.2))
    have ha : f a.val.1 = g a.val.2 := a.property
    rw [coefficients_smul, coefficients_smul, map_smul, ← ha, hx]

/-- Identity clutching is the actual free module over the literal fibre ring. -/
def trivialEquiv : clutch f g (LinearEquiv.refl T (ι → T)) ≃ₗ[P] (ι → P) where
  toFun x i := ⟨(x.val.1 i, x.val.2 i), congrFun x.property i⟩
  invFun x := ⟨((fun i => (x i).val.1), fun i => (x i).val.2), by
    funext i
    exact (x i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (e : (ι → T) ≃ₗ[T] (ι → T))
  (A B : (ι → R) →ₗ[R] (ι → R))
  (hA : ∀ x, f.compLeft ι (A x) = e (f.compLeft ι x))
  (hB : ∀ x, f.compLeft ι (B x) = e.symm (f.compLeft ι x))

local notation "Aₚ" => A.restrictScalars P
local notation "Bₚ" => B.restrictScalars P
local notation "Q" => clutch f g e
local notation "W" => clutch f g (LinearEquiv.refl T (ι → T))

/-- The stable clutching embedding uses separate coefficient lifts of the
transition and its inverse; neither coefficient lift is required invertible. -/
def embed : Q →ₗ[P] W × W where
  toFun q :=
    (⟨(Bₚ q.val.1, q.val.2), by
      change f.compLeft ι (B q.val.1) = g.compLeft ι q.val.2
      rw [hB, q.property, e.symm_apply_apply]⟩,
     ⟨(Aₚ (Bₚ q.val.1) - q.val.1, 0), by
      change f.compLeft ι (A (B q.val.1) - q.val.1) = g.compLeft ι 0
      rw [map_sub, hA, hB, e.apply_symm_apply, sub_self, map_zero]⟩)
  map_add' x y := by
    ext i <;> simp [map_add]
    abel
  map_smul' a x := by
    ext i <;> simp [map_smul, smul_sub]

/-- The stable clutching retraction is given by elementary shears. -/
def retract : W × W →ₗ[P] Q where
  toFun xy :=
    ⟨(Aₚ xy.1.val.1 - xy.2.val.1 +
      Aₚ (xy.1.val.1 - Bₚ (Aₚ xy.1.val.1 - xy.2.val.1)), xy.1.val.2), by
      change f.compLeft ι (A xy.1.val.1 - xy.2.val.1 +
        A (xy.1.val.1 - B (A xy.1.val.1 - xy.2.val.1))) =
          e (g.compLeft ι xy.1.val.2)
      simp only [map_add, map_sub, hA, hB, e.apply_symm_apply]
      rw [← (show f.compLeft ι xy.1.val.1 = g.compLeft ι xy.1.val.2 from xy.1.property)]
      abel⟩
  map_add' x y := by
    ext i <;> simp [map_add, map_sub]
    abel
  map_smul' a x := by
    ext i <;> simp [map_smul, smul_sub, smul_add]

/-- The displayed maps exhibit the clutched module as an actual retract. -/
theorem retract_comp_embed :
    (retract f g e A B hA hB).comp (embed f g e A B hA hB) = LinearMap.id := by
  apply LinearMap.ext
  intro q
  apply Subtype.ext
  apply Prod.ext
  · change A (B q.val.1) - (A (B q.val.1) - q.val.1) +
      A (B q.val.1 - B (A (B q.val.1) - (A (B q.val.1) - q.val.1))) = q.val.1
    have h : A (B q.val.1) - (A (B q.val.1) - q.val.1) = q.val.1 := by abel
    rw [h, sub_self, map_zero, add_zero]
  · rfl

include A B hA hB in
/-- Finite-free clutching is flat over the actual fibre base. -/
theorem flat [_root_.Finite ι] : Module.Flat P Q := by
  let : Module.Flat P (W × W) := Module.Flat.of_linearEquiv
    ((trivialEquiv f g).prodCongr (trivialEquiv f g))
  exact Module.Flat.of_retract (embed f g e A B hA hB) (retract f g e A B hA hB)
    (retract_comp_embed f g e A B hA hB)

include A B hA hB in
/-- Finite-free clutching is finite over the actual fibre base. -/
theorem finite [_root_.Finite ι] : Module.Finite P Q := by
  let : Module.Finite P (W × W) := Module.Finite.equiv
    ((trivialEquiv f g).prodCongr (trivialEquiv f g)).symm
  apply Module.Finite.of_surjective (retract f g e A B hA hB)
  intro q
  exact ⟨embed f g e A B hA hB q,
    LinearMap.congr_fun (retract_comp_embed f g e A B hA hB) q⟩

/-- Every linear map on the finite split boundary module has a coefficient
lift through the specified surjective ring map. The lift need not be invertible. -/
theorem exists_coefficient_lift [_root_.Finite ι]
    (hf : Function.Surjective f) (L : (ι → T) →ₗ[T] (ι → T)) :
    ∃ A : (ι → R) →ₗ[R] (ι → R),
      ∀ x, f.compLeft ι (A x) = L (f.compLeft ι x) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let m : Matrix ι ι R := fun i j => Classical.choose (hf (LinearMap.toMatrix' L i j))
  have hm (i j : ι) : f (m i j) = LinearMap.toMatrix' L i j :=
    Classical.choose_spec (hf (LinearMap.toMatrix' L i j))
  refine ⟨m.mulVecLin, ?_⟩
  intro x
  funext i
  rw [← LinearMap.toMatrix'_mulVec L (f.compLeft ι x)]
  change f (∑ j, m i j * x j) = ∑ j, LinearMap.toMatrix' L i j * f (x j)
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_mul, hm]

/-- The surjective boundary itself supplies both coefficient lifts. Hence
finite-free clutching is finite and flat without an assumed lift certificate. -/
theorem finite_flat_of_surjective [_root_.Finite ι]
    (hf : Function.Surjective f) (e : (ι → T) ≃ₗ[T] (ι → T)) :
    Module.Finite P (clutch f g e) ∧ Module.Flat P (clutch f g e) := by
  obtain ⟨A, hA⟩ := exists_coefficient_lift f hf e.toLinearMap
  obtain ⟨B, hB⟩ := exists_coefficient_lift f hf e.symm.toLinearMap
  exact ⟨finite f g e A B hA hB, flat f g e A B hA hB⟩

end Modules

section RingMaps

variable {R S T : Type (max u v)} [CommRing R] [CommRing S] [CommRing T]
  {ι : Type v} (f : R →+* T) (g : S →+* T)

local notation "P" => fiberRing f g

attribute [local instance] fstAlgebra sndAlgebra

/-- The literal map used when both component algebras are finite split powers
and the displayed boundary gluing is a boundary-algebra automorphism. -/
def map (e : (ι → T) ≃ₐ[T] (ι → T)) :
    P →+* fiberRing (f.compLeft ι) (e.toRingHom.comp (g.compLeft ι)) :=
  fiberMap f g (algebraMap R (ι → R)) (algebraMap S (ι → S))
    (algebraMap T (ι → T)) (f.compLeft ι) (e.toRingHom.comp (g.compLeft ι))
    (by ext a i; rfl) (by ext a i; exact congrFun (e.commutes (g a)) i)

/-- The module of the actual algebra map is the clutched module, with the same
coordinate pairs and the same scalar action. -/
def mapClutchEquiv (e : (ι → T) ≃ₐ[T] (ι → T)) :
    letI : Algebra P (fiberRing (f.compLeft ι) (e.toRingHom.comp (g.compLeft ι))) :=
      (map f g e).toAlgebra
    fiberRing (f.compLeft ι) (e.toRingHom.comp (g.compLeft ι)) ≃ₗ[P]
      clutch f g e.toLinearEquiv := by
  let : Algebra P (fiberRing (f.compLeft ι) (e.toRingHom.comp (g.compLeft ι))) :=
    (map f g e).toAlgebra
  exact
    { toFun := fun q => ⟨q.val, q.property⟩
      invFun := fun q => ⟨q.val, q.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- A genuine finite-flat supplier for the displayed split-power fibre map.
The transition automorphism may twist the two conductor branches differently. -/
theorem finite_flat_map [_root_.Finite ι]
    (hf : Function.Surjective f) (e : (ι → T) ≃ₐ[T] (ι → T)) :
    (map f g e).Finite ∧ (map f g e).Flat := by
  let : Algebra P (fiberRing (f.compLeft ι) (e.toRingHom.comp (g.compLeft ι))) :=
    (map f g e).toAlgebra
  obtain ⟨hfinite, hflat⟩ := finite_flat_of_surjective f g hf e.toLinearEquiv
  let := hfinite
  let := hflat
  exact ⟨Module.Finite.equiv (mapClutchEquiv f g e).symm,
    Module.Flat.of_linearEquiv (mapClutchEquiv f g e)⟩

/-- Finite presentation follows when the actual fibre base is Noetherian.
No Noetherian hypothesis on the three component rings is used as a substitute. -/
theorem finitePresentation_map [_root_.Finite ι] [IsNoetherianRing P]
    (hf : Function.Surjective f) (e : (ι → T) ≃ₐ[T] (ι → T)) :
    (map f g e).FinitePresentation := by
  let : Algebra P (fiberRing (f.compLeft ι) (e.toRingHom.comp (g.compLeft ι))) :=
    (map f g e).toAlgebra
  let : Module.Finite P (fiberRing (f.compLeft ι) (e.toRingHom.comp (g.compLeft ι))) :=
    (finite_flat_map f g hf e).1
  exact Algebra.FinitePresentation.of_finiteType.mp inferInstance

end RingMaps

end FiniteFree

end RingHom.Etale.MilnorPatching
