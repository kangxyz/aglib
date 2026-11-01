/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Kernel.QuasiFinite
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Finiteness of proper group morphisms with finite kernel

Over any base scheme, a finite universal marked kernel gives local
quasi-finiteness of the original group morphism. Properness of the source and
separatedness of the target make that same morphism proper, hence finite.
Source local finite type follows from its properness; target local finite type
is retained for the geometric-fibre criterion. The actual categorical kernel
is the final specialization.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Group.Kernel

variable {S : Scheme.{u}}

/-- Over any base scheme, a finite universal marked kernel, proper source and
separated locally finite-type target make the original group morphism finite. -/
theorem isFinite_of_isFinite_kernelMarking
    {M G H : Grp (Over S)} {f : G ⟶ H}
    [IsProper G.X.hom] [LocallyOfFiniteType H.X.hom] [IsSeparated H.X.hom]
    (m : KernelMarking M G H f) [IsFinite M.X.hom] : IsFinite f.hom.hom.left := by
  have : LocallyQuasiFinite f.hom.hom.left :=
    locallyQuasiFinite_of_isFinite_kernelMarking m
  have : IsProper (f.hom.hom.left ≫ H.X.hom) := by
    rw [Over.w f.hom.hom]
    infer_instance
  have : IsProper f.hom.hom.left := IsProper.of_comp f.hom.hom.left H.X.hom
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- A finite actual categorical kernel makes a group morphism from a proper
source to a separated locally finite-type target finite over any base scheme. -/
theorem isFinite_of_isFinite_group
    {G H : Grp (Over S)} (f : G ⟶ H)
    [IsProper G.X.hom] [LocallyOfFiniteType H.X.hom] [IsSeparated H.X.hom]
    [IsFinite (group f).X.hom] : IsFinite f.hom.hom.left :=
  isFinite_of_isFinite_kernelMarking (marking f)

end AlgebraicGeometry.Scheme.Group.Kernel
