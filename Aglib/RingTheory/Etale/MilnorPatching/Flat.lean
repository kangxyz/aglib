/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Flat.KernelCriterion
public import Aglib.RingTheory.Etale.MilnorPatching.General

/-!
# Flatness descent for the actual Milnor fibre map

The conductor identifies the first boundary kernel with the second-projection
kernel. Its two component base changes detect flatness of the original module.
The lower quotient-kernel tensor criterion keeps its original restricted scope.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace RingHom.Etale.MilnorPatching

universe u v

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  (f : R →+* T) (g : S →+* T)

local notation "P" => fiberRing f g
attribute [local instance] FiniteFree.fstAlgebra FiniteFree.sndAlgebra

/-- The actual conductor of the second projection is the original first
boundary kernel, with the same first-coordinate scalar action. -/
def conductorEquiv :
    LinearMap.ker (Algebra.linearMap P S) ≃ₗ[P] (RingHom.ker f).restrictScalars P where
  toFun j := ⟨j.val.val.1, by
    change f j.val.val.1 = 0
    have hj : j.val.val.2 = 0 := j.property
    have hfg : f j.val.val.1 = g j.val.val.2 := j.val.property
    rw [hj, map_zero] at hfg
    exact hfg⟩
  invFun i := ⟨⟨(i.val, 0), by
    change f i.val = g 0
    have hi : f i.val = 0 := i.property
    simpa only [map_zero] using hi⟩, rfl⟩
  left_inv j := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl (show j.val.val.2 = 0 from j.property).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (M : Type v) [AddCommGroup M] [Module (fiberRing f g) M]

/-- Flatness after first-component base change makes the actual conductor
inclusion remain injective after tensoring. -/
theorem conductor_rTensor_injective [Module.Flat R (R ⊗[P] M)] :
    Function.Injective ((LinearMap.ker (Algebra.linearMap P S)).subtype.rTensor M) := by
  let J := LinearMap.ker (Algebra.linearMap P S)
  let I := (RingHom.ker f).restrictScalars P
  let E := conductorEquiv f g
  let : IsScalarTower P R I :=
    ⟨fun p r x => Subtype.ext (smul_assoc p r x.val)⟩
  let HR : I →ₗ[R] R := (RingHom.ker f).subtype
  let H : I →ₗ[P] R := HR.restrictScalars P
  have hH : Function.Injective (H.rTensor M) :=
    Module.Flat.rTensor_injective_of_flat_baseChange
      (R := P) (S := R) (M := M) (A := I) (B := R) HR (fun _ _ h => Subtype.ext h)
  have hnat (x : J ⊗[P] M) :
      H.rTensor M ((E.rTensor M) x) =
        (Algebra.linearMap P R).rTensor M (J.subtype.rTensor M x) := by
    induction x using TensorProduct.inductionOn with
    | tmul j m => rfl
    | add x y ihx ihy => simp only [map_add, ihx, ihy]
  intro x y hxy
  apply (E.rTensor M).injective
  apply hH
  exact (hnat x).trans
    ((congrArg ((Algebra.linearMap P R).rTensor M) hxy).trans (hnat y).symm)

private theorem ideal_rTensor_injective_of_le_conductor
    [Module.Flat R (R ⊗[P] M)] [Module.Flat S (S ⊗[P] M)]
    (hf : Function.Surjective f) (a : Ideal P)
    (ha : a ≤ RingHom.ker (algebraMap P S)) :
    Function.Injective (a.subtype.rTensor M) := by
  let J := RingHom.ker (algebraMap P S)
  let A := a.map (algebraMap P R)
  let : IsScalarTower P R A := ⟨fun p r x => Subtype.ext (smul_assoc p r x.val)⟩
  let H : a →ₗ[P] A :=
    { toFun := fun x => ⟨x.val.val.1, Ideal.mem_map_of_mem (algebraMap P R) x.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hH : Function.Injective H := by
    intro x y hxy
    have hx0 : x.val.val.2 = 0 := ha x.property
    have hy0 : y.val.val.2 = 0 := ha y.property
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (congrArg Subtype.val hxy) (hx0.trans hy0.symm)
  have hlift (r : R) (hr : r ∈ A) :
      ∀ j : P, j ∈ J → ∃ x : a, x.val.val.1 = j.val.1 * r := by
    induction hr using Submodule.span_induction with
    | mem r hr =>
      obtain ⟨x, hx, rfl⟩ := hr
      intro j hj
      exact ⟨⟨j * x, a.mul_mem_left j hx⟩, rfl⟩
    | zero =>
      intro j hj
      exact ⟨0, by simp⟩
    | add r s hr hs ihr ihs =>
      intro j hj
      obtain ⟨x, hx⟩ := ihr j hj
      obtain ⟨y, hy⟩ := ihs j hj
      exact ⟨x + y, by simpa [mul_add] using congrArg₂ (· + ·) hx hy⟩
    | smul r' r hr ih =>
      intro j hj
      have hj0 : f j.val.1 = 0 := by
        have hjS : j.val.2 = 0 := hj
        rw [show f j.val.1 = g j.val.2 from j.property, hjS, map_zero]
      let j' : P := ⟨(j.val.1 * r', 0), by
        change f (j.val.1 * r') = g 0
        rw [map_mul, hj0, zero_mul, map_zero]⟩
      have hj' : j' ∈ J := by change (0 : S) = 0; rfl
      obtain ⟨x, hx⟩ := ih j' hj'
      refine ⟨x, ?_⟩
      change x.val.val.1 = (j.val.1 * r') * r at hx
      simpa only [smul_eq_mul, mul_assoc] using hx
  have hkill (j : P) (hj : j ∈ J) (z : A ⧸ LinearMap.range H) : j • z = 0 := by
    obtain ⟨y, rfl⟩ := (LinearMap.range H).mkQ_surjective z
    change (Submodule.Quotient.mk (j • y) : A ⧸ LinearMap.range H) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    obtain ⟨x, hx⟩ := hlift y.val y.property j hj
    exact ⟨x, Subtype.ext hx⟩
  have hHS : Function.Injective (H.rTensor M) :=
    Module.Flat.rTensor_injective_of_flat_baseChange_of_annihilated_cokernel
      (S := S) (RingHom.surjective_pullbackSnd_of_surjective f g hf)
      (conductor_rTensor_injective f g M) hkill H (LinearMap.range H).mkQ hH
      (LinearMap.exact_map_mkQ_range H) (LinearMap.range H).mkQ_surjective
  have hA : Function.Injective ((A.subtype.restrictScalars P).rTensor M) :=
    Module.Flat.rTensor_injective_of_flat_baseChange A.subtype A.subtype_injective
  have hnat (x : a ⊗[P] M) :
      (A.subtype.restrictScalars P).rTensor M (H.rTensor M x) =
        (Algebra.linearMap P R).rTensor M (a.subtype.rTensor M x) := by
    induction x using TensorProduct.inductionOn with
    | tmul a m => rfl
    | add x y ihx ihy => simp only [map_add, ihx, ihy]
  intro x y hxy
  apply hHS
  apply hA
  exact (hnat x).trans
    ((congrArg ((Algebra.linearMap P R).rTensor M) hxy).trans (hnat y).symm)

/-- Flatness is detected by the two actual component base changes of a
Milnor square with surjective first boundary. This applies to arbitrary
modules and has no finite-generation or Noetherian hypothesis. -/
theorem flat_of_component_baseChanges
    [Module.Flat R (R ⊗[P] M)] [Module.Flat S (S ⊗[P] M)]
    (hf : Function.Surjective f) : Module.Flat P M := by
  apply Module.Flat.of_ideal_rTensor_injective_below_kernel
    (S := S) (RingHom.surjective_pullbackSnd_of_surjective f g hf)
  intro a ha
  exact ideal_rTensor_injective_of_le_conductor f g M hf a ha

end RingHom.Etale.MilnorPatching

namespace RingHom.Etale.MilnorPatching

universe u

attribute [local instance] FiniteFree.fstAlgebra FiniteFree.sndAlgebra

variable {R S T C D U : Type u}
  [CommRing R] [CommRing S] [CommRing T]
  [CommRing C] [CommRing D] [CommRing U]

/-- Flatness of the original seven-map fiber map follows from the two flat
components and the specified compatible tensor equivalences. -/
theorem flat_fiberMap
    (f : R →+* T) (g : S →+* T) (r : R →+* C) (s : S →+* D)
    (t : T →+* U) (b : C →+* U) (v : D →+* U)
    (hc : b.comp r = t.comp f) (hd : v.comp s = t.comp g) :
    letI : Algebra R T := f.toAlgebra
    letI : Algebra S T := g.toAlgebra
    letI : Algebra R C := r.toAlgebra
    letI : Algebra S D := s.toAlgebra
    letI : Algebra T U := t.toAlgebra
    ∀ (eC : T ⊗[R] C ≃ₐ[T] U) (eD : T ⊗[S] D ≃ₐ[T] U),
      (∀ c, eC (1 ⊗ₜ[R] c) = b c) →
      (∀ d, eD (1 ⊗ₜ[S] d) = v d) →
      Function.Surjective f → r.Flat → s.Flat →
      (fiberMap f g r s t b v hc hd).Flat := by
  let : Algebra R T := f.toAlgebra
  let : Algebra S T := g.toAlgebra
  let : Algebra R C := r.toAlgebra
  let : Algebra S D := s.toAlgebra
  let : Algebra T U := t.toAlgebra
  intro eC eD heC heD hf hr hs
  let P := fiberRing f g
  let Q := fiberRing b v
  let : Algebra P Q := (fiberMap f g r s t b v hc hd).toAlgebra
  let : Module.Flat R C := hr
  let : Module.Flat S D := hs
  let : Fact (b.comp (algebraMap R C) = (algebraMap T U).comp (algebraMap R T)) := ⟨hc⟩
  let : Fact (v.comp (algebraMap S D) = (algebraMap T U).comp (algebraMap S T)) := ⟨hd⟩
  let : Algebra P C := (r.comp (RingHom.pullbackFst f g)).toAlgebra
  let : Algebra P D := (s.comp (RingHom.pullbackSnd f g)).toAlgebra
  let : IsScalarTower P R C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower P S D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Module.Flat R (R ⊗[P] Q) := Module.Flat.of_linearEquiv
    (General.fstTensorEquiv R S T b v hf eC eD heC heD).toLinearEquiv
  let : Module.Flat S (S ⊗[P] Q) := Module.Flat.of_linearEquiv
    (General.sndTensorEquiv R S T b v hf eC eD heC heD).toLinearEquiv
  exact flat_of_component_baseChanges f g Q hf

end RingHom.Etale.MilnorPatching
