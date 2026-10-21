/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.CompleteBase

/-!
# Recovery of global sections from their original reductions

The degree-zero complete-base formal-functions comparison recovers compatible
sections of the actual quotient sheaves. The resulting section has exactly the
specified reductions; no choice of a replacement quotient is made.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable (X : Scheme.{u}) {A : Type u} [CommRing A]

/-- Degree-zero identification commutes with the original coefficient maps. -/
theorem moduleH0EquivOfHom_naturality (α : A →+* Γ(X, ⊤))
    {M N : X.Modules} (φ : M ⟶ N)
    (x : (moduleCohomologyFunctorOfHom X α 0).obj M) :
    moduleH0EquivOfHom X α N (moduleCohomologyMapOfHom X α φ 0 x) =
      φ.app ⊤ (moduleH0EquivOfHom X α M x) :=
  (Sheaf.H.equiv₀_naturality Limits.isTerminalTop
    ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) x).symm

/-- Inverse degree-zero identification is natural as well. -/
theorem moduleH0EquivOfHom_symm_naturality (α : A →+* Γ(X, ⊤))
    {M N : X.Modules} (φ : M ⟶ N) (x : Γ(M, ⊤)) :
    moduleCohomologyMapOfHom X α φ 0 ((moduleH0EquivOfHom X α M).symm x) =
      (moduleH0EquivOfHom X α N).symm (φ.app ⊤ x) :=
  Sheaf.H.equiv₀_symm_naturality Limits.isTerminalTop
    ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) x

variable [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (F : X.Modules)
  (hF : Modules.QuasiCoherent.affineLocallyFiniteType X F)

local notation "α" => Modules.idealThickeningBaseScalar f

include hF in
/-- Compatible global sections of all original reductions recover a unique
original section over a complete Noetherian proper base. -/
theorem existsUnique_section_of_quotientSections
    (s : ∀ n : ℕ, Γ(Modules.idealQuotient X α F (I ^ n), ⊤))
    (hs : ∀ (m n : ℕ) (h : m ≤ n),
      (Modules.idealPowerQuotientMap X α F I h).app ⊤ (s n) = s m) :
    ∃! t : Γ(F, ⊤), ∀ n : ℕ,
      (Modules.idealQuotientπ X α F (I ^ n)).app ⊤ t = s n := by
  let c : ModuleCat.sectionsSubmodule (idealPowerQuotientCohomology X α F I 0) :=
    ⟨fun n => (moduleH0EquivOfHom X α _).symm (s n.unop), by
      intro i j a
      change moduleCohomologyMapOfHom X α
        (Modules.idealPowerQuotientMap X α F I (leOfHom a.unop)) 0 _ = _
      exact (moduleH0EquivOfHom_symm_naturality X α _ (s i.unop)).trans
        (congrArg (moduleH0EquivOfHom X α _).symm (hs _ _ _))⟩
  let e := moduleCohomologyFormalFunctionsCompleteEquiv I f F hF 0
  let t := moduleH0EquivOfHom X α F (e.symm c)
  have hcoord (z : Γ(F, ⊤)) (n : ℕ) :
      (e ((moduleH0EquivOfHom X α F).symm z)).val (op n) =
        (moduleH0EquivOfHom X α _).symm
          ((Modules.idealQuotientπ X α F (I ^ n)).app ⊤ z) :=
    (moduleCohomologyFormalFunctionsCompleteEquiv_apply I f F hF 0 _ n).trans
      (moduleH0EquivOfHom_symm_naturality X α _ z)
  have ht (n : ℕ) : (Modules.idealQuotientπ X α F (I ^ n)).app ⊤ t = s n := by
    apply (moduleH0EquivOfHom X α _).symm.injective
    have h := congrArg (fun z => z.val (op n)) (e.apply_symm_apply c)
    have h' : (e (e.symm c)).val (op n) =
        (moduleH0EquivOfHom X α _).symm
          ((Modules.idealQuotientπ X α F (I ^ n)).app ⊤ t) := by
      simpa only [t, LinearEquiv.symm_apply_apply] using hcoord t n
    exact h'.symm.trans h
  refine ⟨t, ht, ?_⟩
  intro t' ht'
  apply (moduleH0EquivOfHom X α F).symm.injective
  apply e.injective
  apply Subtype.ext
  funext n
  exact (hcoord t' n.unop).trans
    ((congrArg (moduleH0EquivOfHom X α _).symm
      ((ht' n.unop).trans (ht n.unop).symm)).trans (hcoord t n.unop).symm)

end AlgebraicGeometry.Scheme.Cohomology
