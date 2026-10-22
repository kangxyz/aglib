/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Boundary.Patch
public import Aglib.AlgebraicGeometry.Compactification.Boundary.Complement
public import Aglib.AlgebraicGeometry.Compactification.Boundary.ModifiedModel

/-! # Actual patches after the finite boundary modifications -/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Compactification

/-- Construct the actual patch for one of the modified proper models. The
ambient open is precisely the complement of the boundary appearing in the
finite boundary theorem, not merely a smaller open neighborhood. -/
theorem exists_modified_boundary_patch
    {X Y Y' S : Scheme.{u}} [IsNoetherian S]
    (pX : X ⟶ S) [IsSeparated pX] [QuasiCompact pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ S) [IsProper pY]
    (V : Y.Opens) [IsSchemeTheoreticallyDominant V.ι]
    (q : V.toScheme ⟶ X) [IsProper q]
    (hq : V.ι ≫ pY = q ≫ pX)
    (W : X.Opens) [IsIso (q ∣_ W)]
    (s : W.toScheme ⟶ V.toScheme) [IsSchemeTheoreticallyDominant s]
    (hs : s ≫ q = W.ι)
    (β : Y' ⟶ Y) (hβ : Blowup.AdmissibleSequence V β) :
    letI : IsIso (β ∣_ V) := hβ.restrict_isIso
    ∃ (O : Y'.Opens) (M : Scheme.{u}) (pM : M ⟶ S)
      (x : X ⟶ M) (o : O.toScheme ⟶ M) (r : W.toScheme ⟶ O.toScheme),
      (O : Set Y') = (closure (β ⁻¹' (V.ι '' (q ⁻¹' (W : Set X)ᶜ))))ᶜ ∧
      IsNoetherian M ∧ IsSeparated pM ∧ QuasiCompact pM ∧ LocallyOfFiniteType pM ∧
      IsOpenImmersion x ∧ IsSchemeTheoreticallyDominant x ∧ IsOpenImmersion o ∧
      IsOpenImmersion r ∧ IsSchemeTheoreticallyDominant r ∧
      x ≫ pM = pX ∧ o ≫ pM = O.ι ≫ β ≫ pY ∧ W.ι ≫ x = r ≫ o ∧
      r ≫ O.ι = s ≫ inv (β ∣_ V) ≫ (β ⁻¹ᵁ V).ι := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian pY
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace pY
  let : IsNoetherian Y := ⟨⟩
  let : NoetherianSpace V.toScheme := by
    change NoetherianSpace (V : Set Y)
    infer_instance
  let : IsProper β := hβ.isProper
  let : IsIso (β ∣_ V) := hβ.restrict_isIso
  let V' := β ⁻¹ᵁ V
  let q' : V'.toScheme ⟶ X := (β ∣_ V) ≫ q
  obtain ⟨hqp, hqiso, hsd, he⟩ := protected_model_transfer V q W s hs β hβ
  let : IsProper q' := hqp
  let : IsIso (q' ∣_ W) := hqiso
  let : IsSchemeTheoreticallyDominant
      (inv (q' ∣_ W) ≫ (q' ⁻¹ᵁ W).ι ≫ V'.ι) := by
    rw [← Category.assoc, ← he]
    exact hsd
  let F : Closeds V.toScheme :=
    ⟨q ⁻¹' (W : Set X)ᶜ, W.isOpen.isClosed_compl.preimage q.continuous⟩
  let F' : Closeds V'.toScheme :=
    ⟨(β ∣_ V) ⁻¹' (F : Set V.toScheme), F.isClosed.preimage (β ∣_ V).continuous⟩
  let O := boundaryComplementOpen V' F'
  have hO : (O : Set Y') =
      (closure (β ⁻¹' (V.ι '' (q ⁻¹' (W : Set X)ᶜ))))ᶜ := by
    change (closure (V'.ι '' ((β ∣_ V) ⁻¹' (F : Set V.toScheme))))ᶜ = _
    rw [← preimage_open_image_closed β V F]
    rfl
  have hpre : V'.ι ⁻¹ᵁ O = q' ⁻¹ᵁ W := by
    rw [show O = boundaryComplementOpen V' F' from rfl, preimage_boundaryComplementOpen]
    apply SetLike.coe_injective
    ext z
    change (¬ ¬ q' z ∈ (W : Set X)) ↔ q' z ∈ (W : Set X)
    exact not_not
  have hbase : V'.ι ≫ (β ≫ pY) = q' ≫ pX := by
    change (β ⁻¹ᵁ V).ι ≫ β ≫ pY = ((β ∣_ V) ≫ q) ≫ pX
    rw [← morphismRestrict_ι_assoc, hq, Category.assoc]
  obtain ⟨M, pM, x, o, r, hM, hpMs, hpMq, hpMl, hx, hxd, ho, hr, hrd,
      hxbase, hobase, hoverlap, hri⟩ :=
    exists_finiteType_boundary_patch q' V'.ι pX (β ≫ pY) hbase W O hpre
  refine ⟨O, M, pM, x, o, r, hO, hM, hpMs, hpMq, hpMl, hx, hxd, ho, hr, hrd,
    hxbase, ?_, hoverlap, ?_⟩
  · simpa only [Category.assoc] using hobase
  · rw [hri, ← Category.assoc, ← he, Category.assoc]

end AlgebraicGeometry.Scheme.Compactification
