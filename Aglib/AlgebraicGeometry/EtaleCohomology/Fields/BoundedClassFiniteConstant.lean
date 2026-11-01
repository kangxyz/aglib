/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.BoundedCoefficientClass
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.BoundedFiniteTrivialization

/-! # Original bounded classes represented by finite constants after field extension

The actual coefficient-stage class and its actual finite Galois trivialization
are combined over the literal field pullback. The output coefficient arrow is
the inverse of the original square-induced trivialization followed by the
pullback of the original stage arrow. Its cohomology image is exactly the
original class pulled back to that field, not a replacement class.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields

universe u e eL

attribute [local instance] hasSheafifyLarge

/-- A specified constant trivialization transports through an original
commuting square using only the native inverse-image composition isomorphisms. -/
def constantTrivializationAlongSquare
    {X S Y T : Scheme.{u}} (p : X ⟶ S) (f : Y ⟶ X) (q : Y ⟶ T) (b : T ⟶ S)
    (h : f ≫ p = q ≫ b) (E : AbelianSheaf.{u, u + 1} S)
    (A : AddCommGrpCat.{u + 1})
    (t : (inverseImage b).obj E ≅
      (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A) :
    (inverseImage f).obj ((inverseImage p).obj E) ≅
      (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A :=
  ((inverseImageComp p f).app E).symm ≪≫
    eqToIso (congrArg (fun v => (inverseImage v).obj E) h) ≪≫
      (inverseImageComp b q).app E ≪≫ (inverseImage q).mapIso t ≪≫
        (inverseImageConstantIso q).app A

/-- The entire original class construction and image equation are proved over
an arbitrary actual square before the native field specialization. -/
theorem exists_constant_class_of_square_trivialization
    {X S Y T : Scheme.{u}} (p : X ⟶ S) (f : Y ⟶ X) (r : Y ⟶ T) (b : T ⟶ S)
    (h : f ≫ p = r ≫ b)
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{eL} (AbelianSheaf.{u, u + 1} Y)]
    (E F : AbelianSheaf.{u, u + 1} S) (a : E ⟶ F)
    (A : AddCommGrpCat.{u + 1})
    (t : (inverseImage b).obj E ≅
      (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)
    (q : ℕ) (d : Sheaf.H.{e} ((inverseImage p).obj E) q)
    (c : Sheaf.H.{e} ((inverseImage p).obj F) q)
    (hd : Sheaf.H.map ((inverseImage p).map a) q d = c) :
    let s := constantTrivializationAlongSquare p f r b h E A t
    ∃ dB : Sheaf.H.{eL}
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A) q,
      Sheaf.H.map (s.inv ≫ (inverseImage f).map ((inverseImage p).map a)) q dB =
        cohomologyPullback.{u, e, eL} f ((inverseImage p).obj F) q c := by
  let s := constantTrivializationAlongSquare p f r b h E A t
  let dL := cohomologyPullback.{u, e, eL} f ((inverseImage p).obj E) q d
  refine ⟨Sheaf.H.map s.hom q dL, ?_⟩
  change Sheaf.H.map (s.inv ≫ (inverseImage f).map ((inverseImage p).map a)) q
    (Sheaf.H.map s.hom q dL) = _
  rw [← Sheaf.H.map_comp_apply, Iso.hom_inv_id_assoc]
  exact (cohomologyPullback_coefficientMap f ((inverseImage p).map a) q d).symm.trans
    (congrArg (fun z => cohomologyPullback.{u, e, eL} f ((inverseImage p).obj F) q z) hd)

/-- The original bounded field class is the image of an actual finite-constant
class after one produced finite Galois field extension. The original stage
coefficient arrow, trivialization, field square and coefficient composite are
retained explicitly, and the two Ext universes are independent. -/
theorem exists_finiteGalois_constant_class
    (K : Type u) [Field K]
    (F : AbelianSheaf.{u, u + 1} (Spec (.of K)))
    (n : ℕ) (hn : 0 < n) (hF : n • 𝟙 F = 0)
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of K))
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [hExtY : HasExt.{e} (AbelianSheaf.{u, u + 1} Y)]
    [hExtL : ∀ L : FiniteGaloisIntermediateField K (SeparableClosure K),
      HasExt.{eL} (AbelianSheaf.{u, u + 1} (pullback p (Spec.algebraMap K L)))]
    [UnivLE.{u + 1, e}]
    (q : ℕ) (c : Sheaf.H.{e} ((inverseImage p).obj F) q) :
    ∃ (E : AbelianSheaf.{u, u + 1} (Spec (.of K))) (a : E ⟶ F),
      n • 𝟙 E = 0 ∧ IsFiniteLocallyConstant E ∧
      ∃ (L : FiniteGaloisIntermediateField K (SeparableClosure K))
        (B : Type u) (_ : AddCommGroup B) (_ : Finite B),
        (∀ b : B, n • b = 0) ∧
        ∃ t : (inverseImage (Spec.algebraMap K L)).obj E ≅
            ConstantFinite.coefficient B (Spec (.of L)),
          let f := pullback.fst p (Spec.algebraMap K L)
          let r := pullback.snd p (Spec.algebraMap K L)
          let s := constantTrivializationAlongSquare p f r (Spec.algebraMap K L)
            pullback.condition E (ConstantFinite.value B) t
          ∃ d : Sheaf.H.{eL}
              (ConstantFinite.coefficient B (pullback p (Spec.algebraMap K L))) q,
            Sheaf.H.map (s.inv ≫ (inverseImage f).map ((inverseImage p).map a)) q d =
              cohomologyPullback.{u, e, eL} f ((inverseImage p).obj F) q c := by
  have hstage :=
    @exists_finiteLocallyConstant_coefficient_class.{u, e} K inferInstance F n hn hF
      Y p inferInstance inferInstance hExtY inferInstance q c
  obtain ⟨E, a, hE, hfinite, d, hd⟩ := hstage
  have htrivial := @exists_finiteGalois_bounded_small_trivialization.{u}
    K inferInstance E hfinite n hE
  obtain ⟨L, B, hB, hfiniteB, hBn, ht⟩ := htrivial
  let := hB
  let := hfiniteB
  obtain ⟨t⟩ := ht
  refine ⟨E, a, hE, hfinite, L, B, hB, hfiniteB, hBn, t, ?_⟩
  have H := @exists_constant_class_of_square_trivialization.{u, e, eL}
    Y (Spec (.of K)) (pullback p (Spec.algebraMap K L)) (Spec (.of L))
    p (pullback.fst p (Spec.algebraMap K L)) (pullback.snd p (Spec.algebraMap K L))
    (Spec.algebraMap K L) pullback.condition hExtY (hExtL L)
    E F a (ConstantFinite.value B) t q d c hd
  exact H

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields
