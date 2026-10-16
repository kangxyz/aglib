/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Localization.Quotient
public import Aglib.AlgebraicGeometry.Modules.Coherent.Extension.Subobjects

/-!
# Fractions for coherent open restriction

A subobject-extension hypothesis realizes each restricted morphism by a fraction with a support
denominator. The locally Noetherian subobject theorem provides the unconditional fraction
construction.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/GraphFractions.lean`.
SHA-256: `84a93a709298d75d09a6b405a0df211628e99311c660ce74bfc3ea4407c92e08`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/Fullness.lean`.
SHA-256: `61afed4d0f4e8a0a3ffbefa660420929f4823a2a75701f5a9115cad7f0bbe9ec`.
Selected original statements and proofs; canonical lower APIs replace the recorded source wrappers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ModuleCat
open AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open CategoryTheory.ExactCategory
namespace AlgebraicGeometry.Scheme.Modules.Coherent
variable {U X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- Extension of coherent subobjects gives the genuine fraction required
for quotient fullness. The geometric extension hypothesis remains explicit. -/
theorem coherent_fraction_of_subobject_extension
    (hSub : ∀ (H : FiniteTypeSheaves X) (A : FiniteTypeSheaves U)
      (i : A ⟶ (finiteTypeSheavesRestriction j).obj H), Mono i →
      ∃ (H' : FiniteTypeSheaves X) (s : H' ⟶ H), Mono s ∧
        ∃ (e : (finiteTypeSheavesRestriction j).obj H' ≅ A),
          (finiteTypeSheavesRestriction j).map s = e.hom ≫ i)
    {M N : FiniteTypeSheaves X}
    (φ : (finiteTypeSheavesRestriction j).obj M ⟶ (finiteTypeSheavesRestriction j).obj N) :
    ∃ (M' : FiniteTypeSheaves X) (s : M' ⟶ M) (g : M' ⟶ N),
      (finiteTypeSheavesSupportedAway j).isoModSerre s ∧
        (finiteTypeSheavesRestriction j).map s ≫ φ = (finiteTypeSheavesRestriction j).map g := by
  let F := finiteTypeSheavesRestriction j
  let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryProducts F
  let i : F.obj M ⟶ F.obj (M ⊞ N) := biprod.lift (𝟙 _) φ ≫ (F.mapBiprod M N).inv
  have hi : Mono i := by
    change Mono (biprod.lift (𝟙 _) φ ≫ (F.mapBiprod M N).inv)
    infer_instance
  have hi₁ : i ≫ F.map biprod.fst = 𝟙 _ := by
    dsimp [i]
    simp [← F.map_comp]
  have hi₂ : i ≫ F.map biprod.snd = φ := by
    dsimp [i]
    simp only [← F.map_comp, biprod.lift_desc, Category.id_comp,
      Preadditive.add_comp, Category.assoc, biprod.inl_snd, biprod.inr_snd,
      F.map_zero, F.map_id, zero_add]
    exact Category.comp_id φ
  obtain ⟨H', t, _, e, ht⟩ := hSub (M ⊞ N) (F.obj M) i hi
  let s : H' ⟶ M := t ≫ biprod.fst
  let g : H' ⟶ N := t ≫ biprod.snd
  have hs : F.map s = e.hom := by
    dsimp [s]
    rw [F.map_comp, ht, Category.assoc, hi₁, Category.comp_id]
  have hg : F.map g = e.hom ≫ φ := by
    dsimp [g]
    rw [F.map_comp, ht, Category.assoc, hi₂]
  refine ⟨H', s, g, ?_, ?_⟩
  · rw [finiteTypeSheavesSupportedAway_isoModSerre_iff]
    change IsIso (F.map s)
    rw [hs]
    infer_instance
  · change F.map s ≫ φ = F.map g
    rw [hs, hg]

/-- The graph-extension hypothesis proves fullness of the actual quotient
functor; faithfulness was already proved without this hypothesis. -/
theorem quotientCoherentRestriction_full_of_subobject_extension
    (hSub : ∀ (H : FiniteTypeSheaves X) (A : FiniteTypeSheaves U)
      (i : A ⟶ (finiteTypeSheavesRestriction j).obj H), Mono i →
      ∃ (H' : FiniteTypeSheaves X) (s : H' ⟶ H), Mono s ∧
        ∃ (e : (finiteTypeSheavesRestriction j).obj H' ≅ A),
          (finiteTypeSheavesRestriction j).map s = e.hom ≫ i) :
    (quotientCoherentRestriction j).Full := by
  let Q := (finiteTypeSheavesSupportedAway j).isoModSerre.Q
  have : Q.EssSurj := Localization.essSurj Q (finiteTypeSheavesSupportedAway j).isoModSerre
  apply Functor.full_of_comp_essSurj (quotientCoherentRestriction j) Q
  intro M N φ
  change (finiteTypeSheavesRestriction j).obj M ⟶ (finiteTypeSheavesRestriction j).obj N at φ
  obtain ⟨M', s, g, hs, hsg⟩ := coherent_fraction_of_subobject_extension j hSub φ
  have : IsIso (Q.map s) := Localization.inverts Q (finiteTypeSheavesSupportedAway j).isoModSerre s
    hs
  have : IsIso ((finiteTypeSheavesRestriction j).map s) :=
    (finiteTypeSheavesSupportedAway_isoModSerre_iff j s).mp hs
  refine ⟨inv (Q.map s) ≫ Q.map g, ?_⟩
  apply (cancel_epi ((finiteTypeSheavesRestriction j).map s)).mp
  rw [Functor.map_comp, Functor.map_inv]
  simp only [Q, quotientCoherentRestriction_map_Q, IsIso.hom_inv_id_assoc]
  exact hsg.symm

/-- Actual coherent open morphisms admit supported-Serre fractions on the
ambient locally noetherian scheme. -/
theorem coherent_exists_fraction {M N : FiniteTypeSheaves X}
    (φ : (finiteTypeSheavesRestriction j).obj M ⟶ (finiteTypeSheavesRestriction j).obj N) :
    ∃ (M' : FiniteTypeSheaves X) (s : M' ⟶ M) (g : M' ⟶ N),
      (finiteTypeSheavesSupportedAway j).isoModSerre s ∧
        (finiteTypeSheavesRestriction j).map s ≫ φ = (finiteTypeSheavesRestriction j).map g := by
  apply coherent_fraction_of_subobject_extension j
  intro H A i hi
  have : Mono i := hi
  exact coherent_subobject_extension j H A i

end AlgebraicGeometry.Scheme.Modules.Coherent
