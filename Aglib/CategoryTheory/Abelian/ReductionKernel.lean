/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Ordinary relation kernels under right exact reduction -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A right exact functor maps the kernel of an epimorphism onto the kernel
of its image. It need not preserve that kernel. -/
theorem epi_kernelComparison_of_epi (Q : C ⥤ C)
    [Q.PreservesZeroMorphisms] [PreservesFiniteColimits Q]
    {P F : C} (f : P ⟶ F) [Epi f] : Epi (kernelComparison f Q) := by
  have h := (ShortComplex.kernelSequence_exact f).map_of_epi_of_preservesCokernel Q
    (inferInstanceAs (Epi f)) (inferInstance)
  exact h.epi_kernelLift

/-- For a right exact reduction with epimorphic units, the map between
ordinary relation kernels is epimorphic. The lower row is specified by its
actual reduction isomorphisms, not by a cartesian-kernel hypothesis. -/
theorem epi_kernel_map_of_reduction (Q : C ⥤ C)
    [Q.PreservesZeroMorphisms] [PreservesFiniteColimits Q]
    (η : 𝟭 C ⟶ Q) [∀ M, Epi (η.app M)]
    {P F P' F' : C} (f : P ⟶ F) [Epi f] (f' : P' ⟶ F')
    (p : Q.obj P ≅ P') (q : Q.obj F ≅ F')
    (w : Q.map f ≫ q.hom = p.hom ≫ f') :
    Epi (kernel.map f f' (η.app P ≫ p.hom) (η.app F ≫ q.hom)
      (by simpa only [Functor.id_map, Category.assoc, w] using
        congrArg (fun k => k ≫ q.hom) (η.naturality f))) := by
  let e := kernel.mapIso (Q.map f) f' p q w
  let : Epi (kernelComparison f Q) := epi_kernelComparison_of_epi Q f
  have he : η.app (kernel f) ≫ kernelComparison f Q ≫ e.hom =
      kernel.map f f' (η.app P ≫ p.hom) (η.app F ≫ q.hom)
        (by simpa only [Functor.id_map, Category.assoc, w] using
          congrArg (fun k => k ≫ q.hom) (η.naturality f)) := by
    apply (cancel_mono (kernel.ι f')).mp
    simp only [Category.assoc, kernel.lift_ι, kernel.mapIso_hom,
      kernelComparison_comp_ι_assoc, e]
    simpa only [Functor.id_map, Category.assoc] using
      congrArg (fun k => k ≫ p.hom) (η.naturality (kernel.ι f)).symm
  rw [← he]
  infer_instance

end CategoryTheory.Abelian
