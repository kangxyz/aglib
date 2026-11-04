/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.KernelPairing
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.KernelRank
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Dual.Multiplication
public import Aglib.AlgebraicGeometry.Group.CartierDuality.Rank
public import Aglib.AlgebraicGeometry.Group.Kernel.Commutative
public import Aglib.AlgebraicGeometry.Group.Finite.Monomorphism
public import Aglib.AlgebraicGeometry.Group.Kernel.Functoriality
public import Aglib.AlgebraicGeometry.AbelianScheme.OverField.Multiplication.GroupMap

/-!
# Cartier duality of the original positive multiplication kernels

The same normalized Poincare character map on the original dual kernel is
monic. The structural degrees agree, so this very map identifies the
dual kernel with the Cartier dual of the original primal kernel, including
noninvertible positive levels.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open Scheme.OverField Scheme.Group
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.RelativePicard

attribute [local instance] Over.cartesianMonoidalCategory

section Primal

variable {k : Type u} [Field k] (A : Grp (FScheme k)) [IsCommMonObj A.X]
  [IsHProjective A.X.hom] [GeometricallyIntegral A.X.hom]

/-- The native Cartier dual of the original positive multiplication kernel. -/
abbrev multiplicationKernelCartierDual (n : ℕ) (hn : 0 < n) : Grp (FScheme k) :=
  let G := MultiplicationKernel.kernelGroup A n
  letI : IsFinite G.X.hom := Multiplication.kernelGroup_isFinite_of_pos A n hn
  letI : IsCommMonObj G.X :=
    Kernel.isCommMonObj_group (MultiplicationKernel.multiplicationHom A n)
  CartierDuality.dualGroup G

end Primal

variable {k : Type u} [Field k] (A : Grp (FScheme k))
  (P : LocallyNoetherianOver (Spec (.of k))) [LocallyOfFiniteType P.obj.hom]
  (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf A.X.hom).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- The same native multiplication kernel of the supplied original dual. -/
abbrev dualMultiplicationKernel (n : ℕ) : Grp (FScheme k) :=
  letI := picardCommGrpObj A.X.hom P R
  letI : IsCommMonObj (picardIdentityComponent A.X.hom P R) :=
    inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
  MultiplicationKernel.kernelGroup (Grp.mk (picardIdentityComponent A.X.hom P R)) n

/-- The original dual multiplication kernel inherits commutativity. -/
theorem isCommMonObj_dualMultiplicationKernel (n : ℕ) :
    IsCommMonObj (dualMultiplicationKernel A P R n).X := by
  let := picardCommGrpObj A.X.hom P R
  let D := picardIdentityComponent A.X.hom P R
  let : IsCommMonObj D := inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
  exact Kernel.isCommMonObj_group (MultiplicationKernel.multiplicationHom (Grp.mk D) n)

/-- The actual inclusion of the original dual multiplication kernel. -/
abbrev dualMultiplicationKernelInclusion (n : ℕ) :
    dualMultiplicationKernel A P R n ⟶ Grp.mk (picardIdentityComponent A.X.hom P R) :=
  letI := picardCommGrpObj A.X.hom P R
  letI : IsCommMonObj (picardIdentityComponent A.X.hom P R) :=
    inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
  Kernel.inclusion (MultiplicationKernel.multiplicationHom _ n)

variable [IsHProjective A.X.hom] [GeometricallyIntegral A.X.hom] [Smooth A.X.hom]
  [IsSeparated P.obj.hom]

/-- Finiteness of the same original positive dual multiplication kernel. -/
theorem isFinite_dualMultiplicationKernel (n : ℕ) (hn : 0 < n) :
    IsFinite (dualMultiplicationKernel A P R n).X.hom := by
  let := picardCommGrpObj A.X.hom P R
  let D := picardIdentityComponent A.X.hom P R
  let : IsCommMonObj D := inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
  obtain ⟨hproj, _, hint, _⟩ :=
    isHProjective_smooth_geometricallyIntegral_picardIdentityComponent A.X P R
  let : IsHProjective D.hom := hproj
  let : GeometricallyIntegral D.hom := hint
  exact Multiplication.kernelGroup_isFinite_of_pos (Grp.mk D) n hn

variable [IsCommMonObj A.X]

/-- Original Picard pullback by multiplication kills the actual dual kernel. -/
theorem dualMultiplicationKernelInclusion_comp_pullback (n : ℕ) :
    (dualMultiplicationKernelInclusion A P R n).hom.hom ≫
        picardIdentityComponentPullback P R P R
          (MultiplicationKernel.multiplicationHom A n).hom.hom = 1 := by
  let := picardCommGrpObj A.X.hom P R
  let D := picardIdentityComponent A.X.hom P R
  let : IsCommMonObj D := inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
  let H := Grp.mk D
  obtain ⟨hproj, _, hint, _⟩ :=
    isHProjective_smooth_geometricallyIntegral_picardIdentityComponent A.X P R
  let : IsHProjective D.hom := hproj
  let : GeometricallyIntegral D.hom := hint
  have h₁ : picardIdentityComponentPullback P R P R
      (MultiplicationKernel.multiplicationHom A n).hom.hom = (𝟙 D) ^ n := by
    rw [MultiplicationKernel.multiplicationHom_hom, MultiplicationKernel.multiplication]
    exact picardIdentityComponentPullback_multiplication A.X P R n
  have h₂ : (dualMultiplicationKernelInclusion A P R n).hom.hom ≫
      (MultiplicationKernel.multiplicationHom H n).hom.hom = 1 :=
    Kernel.inclusion_comp_eq_one (MultiplicationKernel.multiplicationHom H n)
  rw [h₁]
  rw [MultiplicationKernel.multiplicationHom_hom, MultiplicationKernel.multiplication] at h₂
  exact h₂

/-- The original normalized character on the same actual dual kernel. -/
def multiplicationKernelCartierHom (n : ℕ) (hn : 0 < n) :
    dualMultiplicationKernel A P R n ⟶ multiplicationKernelCartierDual A n hn := by
  let q := MultiplicationKernel.multiplicationHom A n
  let : IsFinite q.hom.hom.left :=
    (Multiplication.multiplicationHom_finite_flat_surjective A n hn).1
  let : IsCommMonObj (Kernel.group q).X := Kernel.isCommMonObj_group q
  let := isFinite_dualMultiplicationKernel A P R n hn
  exact poincareKernelCartierHom A A P R P R q (dualMultiplicationKernel A P R n)
    (dualMultiplicationKernelInclusion A P R n)
    (dualMultiplicationKernelInclusion_comp_pullback A P R n)

/-- The same normalized character map is monic on every original test. -/
theorem mono_multiplicationKernelCartierHom (n : ℕ) (hn : 0 < n) :
    Mono (multiplicationKernelCartierHom A P R n hn).hom.hom := by
  let := picardCommGrpObj A.X.hom P R
  let D := picardIdentityComponent A.X.hom P R
  let : IsCommMonObj D := inferInstanceAs (IsCommMonObj (Group.identityComponentOver P.obj))
  let q := MultiplicationKernel.multiplicationHom A n
  let j := dualMultiplicationKernelInclusion A P R n
  have hm := Multiplication.multiplicationHom_finite_flat_surjective A n hn
  let : IsFinite q.hom.hom.left := hm.1
  let : Flat q.hom.hom.left := hm.2.1
  let : Surjective q.hom.hom.left := hm.2.2
  let : IsCommMonObj (Kernel.group q).X := Kernel.isCommMonObj_group q
  let := isFinite_dualMultiplicationKernel A P R n hn
  let : Mono j.hom.hom :=
    (Kernel.square (MultiplicationKernel.multiplicationHom (Grp.mk D) n)).mono_fst_of_mono
  exact mono_poincareKernelCartierHom A A P R P R q (dualMultiplicationKernel A P R n) j
    (dualMultiplicationKernelInclusion_comp_pullback A P R n)

/-- Equal structural degrees make the same original character map an isomorphism. -/
def multiplicationKernelCartierIso (n : ℕ) (hn : 0 < n) :
    dualMultiplicationKernel A P R n ≅ multiplicationKernelCartierDual A n hn := by
  let G := MultiplicationKernel.kernelGroup A n
  let : IsFinite G.X.hom := Multiplication.kernelGroup_isFinite_of_pos A n hn
  let : IsCommMonObj G.X := Kernel.isCommMonObj_group (MultiplicationKernel.multiplicationHom A n)
  let := isFinite_dualMultiplicationKernel A P R n hn
  let f := multiplicationKernelCartierHom A P R n hn
  let : Mono f.hom.hom := mono_multiplicationKernelCartierHom A P R n hn
  have hdeg : Hom.finiteSchemeDegree k (dualMultiplicationKernel A P R n).X.hom =
      Hom.finiteSchemeDegree k G.X.hom :=
    finiteSchemeDegree_multiplicationKernel_picardIdentityComponent_eq A.X P R n hn
  exact isoOfMonoOfFiniteSchemeDegreeEq f
    (hdeg.trans (CartierDuality.finiteSchemeDegree_dualGroup G).symm)

/-- The isomorphism retains the exact original normalized character map. -/
theorem multiplicationKernelCartierIso_hom (n : ℕ) (hn : 0 < n) :
    (multiplicationKernelCartierIso A P R n hn).hom =
      multiplicationKernelCartierHom A P R n hn := by
  let G := MultiplicationKernel.kernelGroup A n
  let : IsFinite G.X.hom := Multiplication.kernelGroup_isFinite_of_pos A n hn
  let : IsCommMonObj G.X := Kernel.isCommMonObj_group (MultiplicationKernel.multiplicationHom A n)
  let : IsFinite (dualMultiplicationKernel A P R n).X.hom :=
    isFinite_dualMultiplicationKernel A P R n hn
  let : Mono (multiplicationKernelCartierHom A P R n hn).hom.hom :=
    mono_multiplicationKernelCartierHom A P R n hn
  unfold multiplicationKernelCartierIso
  exact isoOfMonoOfFiniteSchemeDegreeEq_hom (multiplicationKernelCartierHom A P R n hn) _

end AlgebraicGeometry.Scheme.RelativePicard
