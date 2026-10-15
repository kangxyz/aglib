/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Category.Grp.Zero
public import Aglib.AlgebraicGeometry.Modules.Support
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Spectrum.Prime.Module
/-!
# Support of actual sheaves associated to modules

For the actual tilde sheaf on an affine scheme, stalk support agrees with
module-theoretic support. It is therefore closed for a finitely generated
module. The same conclusion is transferred to an actual quasi-coherent
sheaf with finitely generated global sections via mathlib's canonical
`fromTildeΓ` isomorphism. No affine equivalence or closedness is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

/-- The stalk support of the associated module sheaf is the usual support of
the original module by localization at primes. -/
theorem support_tilde (M : ModuleCat.{u} R) :
    support (tilde M) = Module.support R M := by
  ext x
  rw [mem_support, Module.mem_support_iff, ← not_subsingleton_iff_nontrivial]
  apply not_congr
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  change Subsingleton ((tilde M).presheaf.stalk x) ↔
    Subsingleton (LocalizedModule x.asIdeal.primeCompl M)
  rw [IsLocalizedModule.subsingleton_iff x.asIdeal.primeCompl (tilde.toStalk M x).hom,
    LocalizedModule.subsingleton_iff]

/-- The actual associated sheaf of a finite module has closed stalk support. -/
theorem isClosed_support_tilde (M : ModuleCat.{u} R) [Module.Finite R M] :
    IsClosed (support (tilde M)) := by
  rw [support_tilde]
  exact Module.isClosed_support

/-- The support of a quasi-coherent sheaf on an affine scheme can be computed
from its actual module of global sections. -/
theorem support_eq_support_globalSections (M : (Spec R).Modules) [M.IsQuasicoherent] :
    support M = Module.support R (moduleSpecΓFunctor.obj M) := by
  rw [← support_tilde]
  exact support_eq_of_iso (asIso M.fromTildeΓ).symm

/-- A quasi-coherent sheaf on an affine scheme whose global-sections module
is finite has closed stalk support. -/
theorem isClosed_support_of_finite_globalSections (M : (Spec R).Modules)
    [M.IsQuasicoherent] [Module.Finite R (moduleSpecΓFunctor.obj M)] :
    IsClosed (support M) := by
  rw [support_eq_support_globalSections]
  exact Module.isClosed_support

end AlgebraicGeometry.Scheme.Modules
