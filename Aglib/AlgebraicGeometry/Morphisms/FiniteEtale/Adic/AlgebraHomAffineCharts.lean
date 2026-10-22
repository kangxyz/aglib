/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.AlgebraHomAffineCover

/-!
# Reconstructing a morphism from its original affine section maps

Only the actual inverse-image affine opens and native `Spec.map` are used.
The local maps and their original coordinate equations are glued together;
no relative spectrum or category of affine algebras is introduced.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules.Algebra

variable {X Y Z : Scheme.{u}}

/-- The chart-map naturality calculation is performed before geometric specialization. -/
theorem affineChartMap_naturality
    {P₀ P₁ T : Scheme.{u}} {R₀ R₁ S₀ S₁ : CommRingCat.{u}}
    (e₀ : P₀ ≅ Spec R₀) (e₁ : P₁ ≅ Spec R₁) (j : P₀ ⟶ P₁)
    (k₀ : Spec S₀ ⟶ T) (k₁ : Spec S₁ ⟶ T)
    (r : R₁ ⟶ R₀) (s : S₁ ⟶ S₀) (a₀ : S₀ ⟶ R₀) (a₁ : S₁ ⟶ R₁)
    (hj : e₀.inv ≫ j = Spec.map r ≫ e₁.inv)
    (hk : Spec.map s ≫ k₁ = k₀) (ha : a₁ ≫ r = s ≫ a₀) :
    j ≫ e₁.hom ≫ Spec.map a₁ ≫ k₁ = e₀.hom ≫ Spec.map a₀ ≫ k₀ := by
  apply (cancel_epi e₀.inv).mp
  calc
    e₀.inv ≫ j ≫ e₁.hom ≫ Spec.map a₁ ≫ k₁ =
        (e₀.inv ≫ j) ≫ e₁.hom ≫ Spec.map a₁ ≫ k₁ := by simp only [Category.assoc]
    _ = (Spec.map r ≫ e₁.inv) ≫ e₁.hom ≫ Spec.map a₁ ≫ k₁ := by rw [hj]
    _ = Spec.map r ≫ Spec.map a₁ ≫ k₁ := by simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = Spec.map a₀ ≫ Spec.map s ≫ k₁ := by
      rw [← Spec.map_comp_assoc, ha, Spec.map_comp_assoc]
    _ = Spec.map a₀ ≫ k₀ := by rw [hk]
    _ = e₀.inv ≫ e₀.hom ≫ Spec.map a₀ ≫ k₀ := by simp only [Iso.inv_hom_id_assoc]

/-- Glue the whole native map-and-coordinate packet while its charts are abstract. -/
def affineChartHomData {S : Scheme.{u}} {P Q : Over S}
    (C : P.left.OpenCover) [Category* C.I₀] [C.LocallyDirected]
    (R T : C.I₀ → CommRingCat.{u}) (e : ∀ i, C.X i ≅ Spec (R i))
    (j : ∀ i, Spec (R i) ⟶ P.left) (k : ∀ i, Spec (T i) ⟶ Q.left)
    (hf : ∀ i, j i = (e i).inv ≫ C.f i) (a : ∀ i, T i ⟶ R i)
    (r : ∀ {i j : C.I₀}, (i ⟶ j) → (R j ⟶ R i))
    (s : ∀ {i j : C.I₀}, (i ⟶ j) → (T j ⟶ T i))
    (hj : ∀ {i j : C.I₀} (f : i ⟶ j),
      (e i).inv ≫ C.trans f = Spec.map (r f) ≫ (e j).inv)
    (hk : ∀ {i j : C.I₀} (f : i ⟶ j), Spec.map (s f) ≫ k j = k i)
    (ha : ∀ {i j : C.I₀} (f : i ⟶ j), a j ≫ r f = s f ≫ a i)
    (hb : ∀ i, Spec.map (a i) ≫ k i ≫ Q.hom = j i ≫ P.hom) :
    { g : P ⟶ Q // ∀ i, j i ≫ g.left = Spec.map (a i) ≫ k i } := by
  let l (i : C.I₀) := (e i).hom ≫ Spec.map (a i) ≫ k i
  have hn {i j : C.I₀} (f : i ⟶ j) : C.trans f ≫ l j = l i :=
    affineChartMap_naturality (e i) (e j) (C.trans f) (k i) (k j)
      (r f) (s f) (a i) (a j) (hj f) (hk f) (ha f)
  have hw (i : C.I₀) : l i ≫ Q.hom = C.f i ≫ P.hom := by
    apply (cancel_epi (e i).inv).mp
    simpa only [l, hf, Category.assoc, Iso.inv_hom_id_assoc] using hb i
  let g := C.glueMorphismsOverOfLocallyDirected l (fun {_ _} f => hn f) hw
  refine ⟨g, fun i => ?_⟩
  have hg : C.f i ≫ g.left = l i :=
    C.map_glueMorphismsOverOfLocallyDirected_left l (fun {_ _} f => hn f) hw i
  rw [hf, Category.assoc, hg]
  simp only [l, Iso.inv_hom_id_assoc]

variable (p : Y ⟶ X) (q : Z ⟶ X) [IsAffineHom p] [IsAffineHom q]

/-- Original structural ring compatibility gives the original affine-chart base square. -/
theorem affineSectionSpecMap_over
    (ρ : ∀ U : X.affineOpens, Γ(Z, q ⁻¹ᵁ U.val) ⟶ Γ(Y, p ⁻¹ᵁ U.val))
    (hbase : ∀ U : X.affineOpens, q.app U.val ≫ ρ U = p.app U.val)
    (U : X.affineOpens) :
    Spec.map (ρ U) ≫ (U.property.preimage q).fromSpec ≫ q =
      (U.property.preimage p).fromSpec ≫ p := by
  rw [← U.property.SpecMap_appLE_fromSpec q (U.property.preimage q) le_rfl,
    ← U.property.SpecMap_appLE_fromSpec p (U.property.preimage p) le_rfl,
    Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app,
    ← Spec.map_comp_assoc, hbase U]

/-- The actual glued morphism and all original affine coordinate equations are specialized once. -/
def affineSectionHomData
    (ρ : ∀ U : X.affineOpens, Γ(Z, q ⁻¹ᵁ U.val) ⟶ Γ(Y, p ⁻¹ᵁ U.val))
    (hnat : ∀ {U V : X.affineOpens} (i : U ⟶ V),
      ρ V ≫ Y.presheaf.map (homOfLE (p.preimage_mono i.le)).op =
        Z.presheaf.map (homOfLE (q.preimage_mono i.le)).op ≫ ρ U)
    (hbase : ∀ U : X.affineOpens, q.app U.val ≫ ρ U = p.app U.val) :
    { g : Over.mk p ⟶ Over.mk q // ∀ U : X.affineOpens,
        (U.property.preimage p).fromSpec ≫ g.left =
          Spec.map (ρ U) ≫ (U.property.preimage q).fromSpec } :=
  affineChartHomData (P := Over.mk p) (Q := Over.mk q) (affineInverseImageCover p)
    (fun U => Γ(Y, p ⁻¹ᵁ U.val)) (fun U => Γ(Z, q ⁻¹ᵁ U.val))
    (fun U => (U.property.preimage p).isoSpec) (fun U => (U.property.preimage p).fromSpec)
    (fun U => (U.property.preimage q).fromSpec) (fun _ => rfl) ρ
    (fun {_ _} i => Y.presheaf.map (homOfLE (p.preimage_mono i.le)).op)
    (fun {_ _} i => Z.presheaf.map (homOfLE (q.preimage_mono i.le)).op)
    (fun {U V} i => (affineOpen_isoSpec_inv_restriction (V.property.preimage p)
      (U.property.preimage p) (homOfLE (p.preimage_mono i.le))).symm)
    (fun {U V} i => (V.property.preimage q).map_fromSpec (U.property.preimage q)
      (homOfLE (q.preimage_mono i.le)).op)
    hnat (affineSectionSpecMap_over p q ρ hbase)

end AlgebraicGeometry.Scheme.Modules.Algebra
