/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.RepresentedKernel
public import Aglib.AlgebraicGeometry.Group.Kernel.Basic

/-! The exact sequence of an original represented kernel marking. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel

universe u

attribute [local instance] Over.cartesianMonoidalCategory hasSheafifyLarge

variable {S : Scheme.{u}} {K G H : Grp (Over S)} {q : G ⟶ H}
  (m : KernelMarking K G H q)

/-- The original marked inclusion is annihilated by the quotient. -/
theorem markedKernel_inclusion_comp : m.inclusion ≫ q = 0 := by
  apply (Grp.forget (Over S)).map_injective
  exact m.over

variable [IsCommMonObj K.X] [IsCommMonObj G.X] [IsCommMonObj H.X]

/-- The represented sequence uses the given original kernel marking. -/
abbrev markedKernelSequence : ShortComplex (AbelianSheaf.{u, u + 1} S) :=
  letI : Mono m.inclusion.hom.hom := m.isPullback.mono_fst_of_mono
  ShortComplex.mk (representedSheafMap m.inclusion) (representedSheafMap q)
    (represented_composition_zero m.inclusion q (markedKernel_inclusion_comp m))

/-- The original marking exhibits the original represented insertion as the sheaf kernel. -/
def markedKernelSequenceIsKernel :
    IsLimit (KernelFork.ofι (markedKernelSequence m).f (markedKernelSequence m).zero) :=
  letI : Mono m.inclusion.hom.hom := m.isPullback.mono_fst_of_mono
  representedKernelIsLimit m.inclusion q
    (fun x h => m.isPullback.lift x (toUnit _) h)
    (fun x h => m.isPullback.lift_fst x (toUnit _) h)
    (markedKernel_inclusion_comp m)

/-- An epimorphic quotient gives the short exact sequence of the original marked kernel. -/
theorem markedKernelSequence_shortExact [Epi (representedSheafMap q)] :
    (markedKernelSequence m).ShortExact := by
  let h := markedKernelSequenceIsKernel m
  let : Mono (markedKernelSequence m).f := mono_of_isLimit_fork h
  let : Epi (markedKernelSequence m).g := inferInstanceAs (Epi (representedSheafMap q))
  exact ⟨(markedKernelSequence m).exact_of_f_is_kernel h⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.RepresentedKernel
