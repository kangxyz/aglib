/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.LinearAlgebra.Prod

/-! # Finite defect factorizations and the split kernel

Both defects of an original linear map and its parametrix factor through specified
finite modules. The enlarged split-surjection kernel is explicitly finite projective.
The source and the right-defect module must be projective; the target need not be.
All replacement maps and homotopies retain the given linear maps. No noetherianity is assumed.
-/

/-!
Source: `quillen-k-theory/Quillen/Aglib/Algebra/Module/FiniteParametrix.lean` from the supplied
frozen Quillen snapshot.
SHA-256: `91a94e6668a4b2f8098a646a53485376b278add2e70bba72034d00afd3643a06`.
Only native objects, maps and mathematical namespaces are used in this extraction.
-/

@[expose] public section

noncomputable section
universe u v

namespace Module

variable {R : Type u} [CommRing R]
  {A B F G : Type v} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup F] [Module R F] [AddCommGroup G] [Module R G]
  (d : A →ₗ[R] B) (s : B →ₗ[R] A) (t : F →ₗ[R] B) (r : B →ₗ[R] F)
  (hr : d.comp s + t.comp r = LinearMap.id)

/-- The original differential enlarged by its finite defect generators. -/
def parametrixTotal : A × F →ₗ[R] B := d.coprod t

/-- The actual parametrix and right defect factor give a section of the enlarged map. -/
def parametrixSection : B →ₗ[R] A × F := s.prod r

include hr in
/-- The specified original right defect identity is the splitting identity. -/
theorem parametrixTotal_section :
    (parametrixTotal d t).comp (parametrixSection s r) = LinearMap.id := by
  ext y
  exact LinearMap.congr_fun hr y

/-- The original split-surjection kernel projector. -/
def parametrixKernelRetraction : A × F →ₗ[R] LinearMap.ker (parametrixTotal d t) :=
  (LinearMap.id - (parametrixSection s r).comp (parametrixTotal d t)).codRestrict
    (LinearMap.ker (parametrixTotal d t)) (fun x => by
      change parametrixTotal d t (x - parametrixSection s r (parametrixTotal d t x)) = 0
      rw [map_sub]
      have hx := LinearMap.congr_fun (parametrixTotal_section d s t r hr)
        (parametrixTotal d t x)
      change parametrixTotal d t (parametrixSection s r (parametrixTotal d t x)) = _ at hx
      rw [hx, LinearMap.id_apply, sub_self])

/-- The kernel inclusion and actual projector are a genuine retraction. -/
theorem parametrixKernelRetraction_subtype :
    (parametrixKernelRetraction d s t r hr).comp
      (LinearMap.ker (parametrixTotal d t)).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change x.val - parametrixSection s r (parametrixTotal d t x.val) = x.val
  rw [show parametrixTotal d t x.val = 0 from x.property, map_zero, sub_zero]

variable (u : G →ₗ[R] A) (v : A →ₗ[R] G)
  (hl : s.comp d + u.comp v = LinearMap.id)

/-- Finite left-defect and added-column inputs map onto the original split kernel. -/
def parametrixKernelGenerators : G × F →ₗ[R] LinearMap.ker (parametrixTotal d t) :=
  (parametrixKernelRetraction d s t r hr).comp
    ((u.comp (LinearMap.fst R G F) -
      s.comp (t.comp (LinearMap.snd R G F))).prod (LinearMap.snd R G F))

include hl in
/-- Both original defect factorizations imply actual surjectivity from the finite inputs. -/
theorem parametrixKernelGenerators_surjective :
    Function.Surjective (parametrixKernelGenerators d s t r hr u) := by
  intro x
  refine ⟨(v x.val.1, x.val.2), ?_⟩
  have hx := x.property
  change d x.val.1 + t x.val.2 = 0 at hx
  have hd : d x.val.1 = -t x.val.2 := eq_neg_of_add_eq_zero_left hx
  have hlx := LinearMap.congr_fun hl x.val.1
  change s (d x.val.1) + u (v x.val.1) = x.val.1 at hlx
  have he : u (v x.val.1) - s (t x.val.2) = x.val.1 := by
    rw [hd, map_neg] at hlx
    simpa only [sub_eq_add_neg, add_comm] using hlx
  change parametrixKernelRetraction d s t r hr
      (u (v x.val.1) - s (t x.val.2), x.val.2) = x
  rw [he]
  exact LinearMap.congr_fun (parametrixKernelRetraction_subtype d s t r hr) x

include hr hl in
/-- The actual split-surjection kernel is finite projective, not just finite rank. -/
theorem finite_projective_parametrixKernel
    [Module.Projective R A] [Module.Projective R F]
    [Module.Finite R F] [Module.Finite R G] :
    Module.Finite R (LinearMap.ker (parametrixTotal d t)) ∧
      Module.Projective R (LinearMap.ker (parametrixTotal d t)) := by
  exact ⟨Module.Finite.of_surjective (parametrixKernelGenerators d s t r hr u)
      (parametrixKernelGenerators_surjective d s t r hr u v hl),
    Module.Projective.of_split (LinearMap.ker (parametrixTotal d t)).subtype
      (parametrixKernelRetraction d s t r hr)
      (parametrixKernelRetraction_subtype d s t r hr)⟩

/-- The replacement differential is the original kernel's second projection. -/
def parametrixReplacementDifferential : LinearMap.ker (parametrixTotal d t) →ₗ[R] F :=
  (LinearMap.snd R A F).comp (LinearMap.ker (parametrixTotal d t)).subtype

/-- The forward source map is the actual split-kernel projection of the first summand. -/
def parametrixForwardSource : A →ₗ[R] LinearMap.ker (parametrixTotal d t) :=
  (parametrixKernelRetraction d s t r hr).comp (LinearMap.inl R A F)

/-- The backward source map is the original kernel's first projection. -/
def parametrixBackwardSource : LinearMap.ker (parametrixTotal d t) →ₗ[R] A :=
  (LinearMap.fst R A F).comp (LinearMap.ker (parametrixTotal d t)).subtype

/-- The replacement homotopy is the actual split-kernel projection of the added summand. -/
def parametrixReplacementHomotopy : F →ₗ[R] LinearMap.ker (parametrixTotal d t) :=
  (parametrixKernelRetraction d s t r hr).comp (LinearMap.inr R A F)

/-- The literal forward maps commute with the original and replacement differentials. -/
theorem parametrixForward_chain :
    (parametrixReplacementDifferential d t).comp (parametrixForwardSource d s t r hr) =
      (-r).comp d := by
  ext x
  simp [parametrixReplacementDifferential, parametrixForwardSource,
    parametrixKernelRetraction, parametrixTotal, parametrixSection]

/-- The literal backward maps commute with the original and replacement differentials. -/
theorem parametrixBackward_chain :
    d.comp (parametrixBackwardSource d t) =
      (-t).comp (parametrixReplacementDifferential d t) := by
  ext x
  exact eq_neg_of_add_eq_zero_left x.property

/-- The original source composite differs from the identity by the given parametrix. -/
theorem parametrixBackward_forward_zero :
    (parametrixBackwardSource d t).comp (parametrixForwardSource d s t r hr) =
      LinearMap.id - s.comp d := by
  ext x
  simp [parametrixBackwardSource, parametrixForwardSource, parametrixKernelRetraction,
    parametrixTotal, parametrixSection]

include hr in
/-- The original target composite differs from the identity by the same parametrix. -/
theorem parametrixBackward_forward_one :
    (-t).comp (-r) = LinearMap.id - d.comp s := by
  rw [LinearMap.neg_comp, LinearMap.comp_neg, neg_neg]
  exact eq_sub_of_add_eq' hr

/-- The replacement source composite and its actual homotopy sum to the identity. -/
theorem parametrixForward_backward_zero_add :
    (parametrixForwardSource d s t r hr).comp (parametrixBackwardSource d t) +
      (parametrixReplacementHomotopy d s t r hr).comp
        (parametrixReplacementDifferential d t) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change parametrixKernelRetraction d s t r hr (x.val.1, 0) +
      parametrixKernelRetraction d s t r hr (0, x.val.2) = x
  rw [← map_add]
  simpa using LinearMap.congr_fun (parametrixKernelRetraction_subtype d s t r hr) x

/-- The replacement target composite and its same homotopy sum to the identity. -/
theorem parametrixForward_backward_one_add :
    (-r).comp (-t) + (parametrixReplacementDifferential d t).comp
      (parametrixReplacementHomotopy d s t r hr) = LinearMap.id := by
  ext x
  simp [parametrixReplacementDifferential, parametrixReplacementHomotopy,
    parametrixKernelRetraction, parametrixTotal, parametrixSection]

end Module
