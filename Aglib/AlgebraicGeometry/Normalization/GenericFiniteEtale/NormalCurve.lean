/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.FundamentalGroup.Field.Basic
public import Aglib.AlgebraicGeometry.Stalk.CodimensionOne
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.LocalPullback
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.Finite
public import Aglib.AlgebraicGeometry.Morphisms.Etale.Locus

/-!
# Generic finite-etale normalization over a normal curve

Each embedding of an original chart algebra gives a geometric point of the same
original cover. Fixedness of every original point therefore fixes every embedding.
For an integral normal locally Noetherian target of dimension at most one, the
actual generic fiber and codimension-one stalk pullbacks detect etaleness of its
relative normalization. Empty and split covers are allowed.

Extraction source: `R5Lab.Aglib.AlgebraicGeometry.Normalization.NormalCurvePurity`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`, lines 39–141, SHA-256
`e9581abb5be829a48e08470ac47e77caf953f58103dce915b7c540b0a7aac94c`.
The original finite-etale cover and the native relative normalization maps are retained.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.FiniteEtale (Fiber)
open AlgebraicGeometry.Scheme.FiniteEtale.FieldGalois

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.NormalCurve

universe u

section Coordinates

variable (X : Scheme.{u}) [IsIntegral X] (C : Scheme.FiniteEtale (Spec X.functionField))
  (U : X.Opens) [Nonempty U]

/-- Every embedding of the literal chart algebra gives a geometric point of the same
original cover, using its constructed affine identification. -/
def chartAlgebraPoint (φ : (Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U))
    →ₐ[X.functionField]
    AlgebraicClosure X.functionField) : Fiber (geometricPoint X.functionField) C :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    (localOriginalIso X C U).inv) (by
      have hstruct : (localOriginalIso X C U).inv ≫ C.obj.hom =
          Spec.map (CommRingCat.ofHom (algebraMap X.functionField (Γ(C.obj.left, (C.obj.hom ≫
              X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U)))) := by
        apply (cancel_epi (localOriginalIso X C U).hom).mp
        simp only [Iso.hom_inv_id_assoc]
        exact (localOriginalIso_structure X C U).symm
      change (Spec.map _ ≫ _) ≫ C.obj.hom = Spec.map _
      rw [Category.assoc, hstruct, ← Spec.map_comp]
      congr 1
      ext r
      exact φ.commutes r)

/-- Fixing every geometric point of the original cover fixes every embedding of its
literal chart algebra, for the same absolute Galois automorphism. -/
theorem chart_embeddings_fixed_of_points_fixed
    (σ : Field.absoluteGaloisGroup X.functionField)
    (hfixed : ∀ t : Fiber (geometricPoint X.functionField) C,
      pointEnd X.functionField σ ≫ t = t)
    (φ : (Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U)) →ₐ[X.functionField]
        AlgebraicClosure X.functionField) :
    σ.toAlgHom.comp φ = φ := by
  have h := congrArg (fun t : Fiber (geometricPoint X.functionField) C => t.left)
    (hfixed (chartAlgebraPoint X C U φ))
  change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (localOriginalIso X C U).inv) =
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (localOriginalIso X C U).inv at h
  rw [← Category.assoc, ← Spec.map_comp] at h
  have hring := Spec.map_inj.mp ((cancel_mono (localOriginalIso X C U).inv).mp h)
  apply AlgHom.ext
  intro a
  exact congrArg (fun f : (Γ(C.obj.left, (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U)) ⟶
      CommRingCat.of (AlgebraicClosure X.functionField) =>
    f.hom a) hring

end Coordinates

/-- A stalk on a scheme of topological dimension at most one has dimension zero or one. -/
theorem stalk_dimension_zero_or_one (X : Scheme.{u})
    (hdim : topologicalKrullDim X ≤ 1) (x : X) :
    ringKrullDim (X.presheaf.stalk x) = 0 ∨ ringKrullDim (X.presheaf.stalk x) = 1 := by
  have horder : Order.krullDim X ≤ 1 := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact hdim
  have hco : Order.coheight x ≤ 1 := by
    exact_mod_cast (Order.coheight_le_krullDim x).trans horder
  rw [ringKrullDim_stalk_eq_coheight]
  rcases Order.le_one_iff.mp hco with h | h
  · left
    exact_mod_cast h
  · right
    exact_mod_cast h

/-- A point of an integral scheme with a dimension-zero stalk is its actual generic point. -/
theorem eq_genericPoint_of_stalk_dimension_zero
    (X : Scheme.{u}) [IsIntegral X] (x : X)
    (hd : ringKrullDim (X.presheaf.stalk x) = 0) : x = genericPoint X := by
  have hz : Order.coheight x = 0 := by
    rw [ringKrullDim_stalk_eq_coheight] at hd
    exact_mod_cast hd
  have hmax := Order.coheight_eq_zero.mp hz
  have hback : x ⤳ genericPoint X := hmax (genericPoint_specializes x)
  exact (hback.antisymm (genericPoint_specializes x)).eq

/-- The actual generic pullback of relative normalization recovers the original etale cover. -/
theorem normalization_generic_etale
    (X : Scheme.{u}) [IsIntegral X] (C : Scheme.FiniteEtale (Spec X.functionField)) :
    Etale (pullback.snd (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization
      (X.fromSpecStalk (genericPoint X))) := by
  let e := genericFiberOverIso X C
  have he : e.inv.left ≫ C.obj.hom =
      pullback.snd (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization
        (X.fromSpecStalk (genericPoint X)) := e.inv.w
  rw [← he]
  infer_instance

/-- On an integral normal locally Noetherian curve, etaleness of all actual codimension-one
stalk pullbacks and the recovered generic cover imply etaleness of relative normalization. -/
theorem normalization_etale_of_codimensionOne
    (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (hdim : topologicalKrullDim X ≤ 1) (C : Scheme.FiniteEtale (Spec X.functionField))
    (hlocal : ∀ x : CodimensionOnePoint X,
      Etale (pullback.snd (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization
        (X.fromSpecStalk x.1))) :
    Etale (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization := by
  let f := (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization
  have : LocallyOfFinitePresentation f := inferInstanceAs
    (LocallyOfFinitePresentation
      (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization)
  have hneighborhood : ∀ z : (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).normalization,
      ∃ W : (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).normalization.Opens,
        z ∈ W ∧ Etale (W.ι ≫ f) := by
    intro z
    apply LocalRing.Etale.exists_etale_neighborhood_of_etale_stalkBaseChange f z
    rcases stalk_dimension_zero_or_one X hdim (f z) with hzero | hone
    · have heq := eq_genericPoint_of_stalk_dimension_zero X (f z) hzero
      have hg : ∀ y : X, y = genericPoint X →
          Etale (pullback.snd f (X.fromSpecStalk y)) := by
        rintro y rfl
        exact normalization_generic_etale X C
      exact hg (f z) heq
    · exact hlocal ⟨f z, hone⟩
  choose W hz hW using hneighborhood
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale) W
  · apply top_le_iff.mp
    intro z _
    exact (le_iSup W z) (hz z)
  · exact hW

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.NormalCurve
