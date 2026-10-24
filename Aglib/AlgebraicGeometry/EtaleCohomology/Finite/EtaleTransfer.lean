/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteEtaleTransfer.Trace
public import Aglib.AlgebraicGeometry.EtaleCohomology.SlicePullback.SourceSquare
public import Aglib.CategoryTheory.Preadditive.CoprimeScalar

/-! # Finite-etale transfer on original scheme cohomology

For a finite-etale cover of constant actual rank, the normalized represented
transfer gives an additive transfer on the original cohomology of any scheme.
The composite with the original pullback is multiplication by the rank. If
that rank is prime to an annihilator of the coefficient, the original pullback
has an additive retraction, in independent source and target Ext universes.

These are ordinary-cohomology statements. They do not assert a natural sheaf
trace or its compatibility with extension by zero or compact supports.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.Sheaf.Hypercohomology CategoryTheory.Sheaf.SliceCohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w₀ w₁

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} (Y : Scheme.FiniteEtale X)
  [HasExt.{w₀} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w₁} (AbelianSheaf.{u, u + 1} Y.obj.left)]

/-- Transfer on the original cohomology of an arbitrary scheme, normalized by
an actual constant finite-etale rank. No torsion hypothesis is needed. -/
theorem exists_finiteEtale_cohomologyTransfer (n : ℕ)
    (hn : ∀ x : X, Y.obj.hom.finrank x = n)
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    ∃ tr : Sheaf.H.{w₁} ((inverseImage Y.obj.hom).obj F) q →+ Sheaf.H.{w₀} F q,
      ∀ x, tr (cohomologyPullback.{u, w₀, w₁} Y.obj.hom F q x) = n • x := by
  let J := Scheme.smallEtaleTopology X
  let U : X.Etale := (Scheme.FiniteEtale.toEtale X).obj Y
  let : HasExt.{w₁} (AbelianSheaf.{u, u + 1} U.left) :=
    inferInstanceAs (HasExt.{w₁} (AbelianSheaf.{u, u + 1} Y.obj.left))
  let : HasExt.{u + 2} (Sheaf (J.over U) AddCommGrpCat.{u + 1}) := HasExt.standard _
  obtain ⟨τ, hτ⟩ := Scheme.FiniteEtale.exists_normalized_transfer Y n hn
  have hτ' : τ ≫ representedIntegerAugmentation U = n • 𝟙 _ := by
    simpa only [representedIntegerAugmentation, etaleTerminalIsTerminal] using hτ
  let e₁ : Sheaf.H.{w₁} ((inverseImage (X := X) (S := U.left) U.hom).obj F) q ≃+
      Sheaf.H.{u + 2}
        ((Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).inverse.obj
          ((inverseImage (X := X) (S := U.left) U.hom).obj F)) q :=
    sliceCohomologyEquiv.{u, u + 1, u + 2, w₁}
      U ((inverseImage (X := X) (S := U.left) U.hom).obj F) q
  let e₂ : Sheaf.H.{u + 2}
      ((Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).inverse.obj
        ((inverseImage (X := X) (S := U.left) U.hom).obj F)) q ≃+ Sheaf.H.{u + 2} (F.over U) q :=
    ((Sheaf.functorH.{u + 2, u + 1, u, u + 1} (J.over U) q).mapIso
      ((inverseImageSliceInverseIso U).app F)).addCommGroupIsoToAddEquiv
  let e₃ := sliceComparison.{w₀, u + 2, u + 1, u, u + 1} J U F q
  let e := (e₁.trans e₂).trans e₃.symm
  let tr := ((Ext.mk₀ τ).precomp F (Nat.zero_add q)).comp e.toAddMonoidHom
  refine ⟨tr, ?_⟩
  intro x
  have he : e (cohomologyPullback.{u, w₀, w₁} (X := X) (S := U.left) U.hom F q x) =
      (Ext.mk₀ (representedIntegerAugmentation U)).comp x (Nat.zero_add q) := by
    have h : e₂ (e₁
        (cohomologyPullback.{u, w₀, w₁} (X := X) (S := U.left) U.hom F q x)) =
        e₃ ((Ext.mk₀ (representedIntegerAugmentation U)).comp x (Nat.zero_add q)) :=
      cohomologyPullback_sliceComparison.{u, w₀, w₁, u + 2} U F q x
    exact (congrArg e₃.symm h).trans (e₃.symm_apply_apply _)
  change (Ext.mk₀ τ).comp
    (e (cohomologyPullback.{u, w₀, w₁} (X := X) (S := U.left) U.hom F q x)) (Nat.zero_add q) = n • x
  rw [he, Ext.mk₀_comp_mk₀_assoc, hτ']
  let Z := (constantSheaf J AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let a : (Z ⟶ Z) →+ Sheaf.H.{w₀} F q :=
    (x.postcomp Z (Nat.zero_add q)).comp Ext.addEquiv₀.symm.toAddMonoidHom
  exact (a.map_nsmul n (𝟙 Z)).trans (congrArg (n • ·) (Ext.mk₀_id_comp x))

/-- A finite-etale pullback of degree prime to an annihilator has an actual
additive retraction on original cohomology, not merely an abstract embedding. -/
theorem exists_finiteEtale_cohomologyRetraction (n : ℕ)
    (hn : ∀ x : X, Y.obj.hom.finrank x = n)
    (F : AbelianSheaf.{u, u + 1} X) (p : ℕ) (hcop : n.Coprime p)
    (hp : p • 𝟙 F = 0) (q : ℕ) :
    ∃ r : Sheaf.H.{w₁} ((inverseImage Y.obj.hom).obj F) q →+ Sheaf.H.{w₀} F q,
      Function.LeftInverse r (cohomologyPullback.{u, w₀, w₁} Y.obj.hom F q) := by
  obtain ⟨tr, htr⟩ := exists_finiteEtale_cohomologyTransfer.{u, w₀, w₁} Y n hn F q
  let : IsIso (n • 𝟙 F) :=
    Preadditive.isIso_nsmul_id_of_coprime F n p hcop hp
  let e : Sheaf.H.{w₀} F q ≃+ Sheaf.H.{w₀} F q :=
    ((Sheaf.functorH.{w₀, u + 1, u, u + 1} (Scheme.smallEtaleTopology X) q).mapIso
      (asIso (n • 𝟙 F))).addCommGroupIsoToAddEquiv
  have he (x : Sheaf.H.{w₀} F q) : e x = n • x := by
    change ((Sheaf.functorH.{w₀, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) q).map (n • 𝟙 F)) x = n • x
    rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id]
    rfl
  refine ⟨e.symm.toAddMonoidHom.comp tr, ?_⟩
  intro x
  change e.symm (tr (cohomologyPullback.{u, w₀, w₁} Y.obj.hom F q x)) = x
  rw [htr, ← he, e.symm_apply_apply]

/-- Coprime finite-etale restriction is injective on original cohomology of
any scheme, with the actual geometric degree and coefficient annihilator. -/
theorem finiteEtale_cohomologyPullback_injective (n : ℕ)
    (hn : ∀ x : X, Y.obj.hom.finrank x = n)
    (F : AbelianSheaf.{u, u + 1} X) (p : ℕ) (hcop : n.Coprime p)
    (hp : p • 𝟙 F = 0) (q : ℕ) :
    Function.Injective (cohomologyPullback.{u, w₀, w₁} Y.obj.hom F q) := by
  obtain ⟨r, hr⟩ := exists_finiteEtale_cohomologyRetraction.{u, w₀, w₁} Y n hn F p hcop hp q
  exact hr.injective

/-- Original cohomology vanishing descends through a finite-etale cover whose
constant rank is prime to an annihilator of the original coefficient. -/
theorem subsingleton_H_of_finiteEtale_of_coprime (n : ℕ)
    (hn : ∀ x : X, Y.obj.hom.finrank x = n)
    (F : AbelianSheaf.{u, u + 1} X) (p : ℕ) (hcop : n.Coprime p)
    (hp : p • 𝟙 F = 0) (q : ℕ)
    [Subsingleton (Sheaf.H.{w₁} ((inverseImage Y.obj.hom).obj F) q)] :
    Subsingleton (Sheaf.H.{w₀} F q) :=
  (finiteEtale_cohomologyPullback_injective.{u, w₀, w₁} Y n hn F p hcop hp q).subsingleton

end AlgebraicGeometry.Scheme.EtaleCohomology
