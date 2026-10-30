/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.Translation
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Local properties spread along group translations

Over an algebraically closed field, translates of a nonempty source open
cover a group scheme locally of finite type. Consequently any scheme
morphism property local at the source holds for a group homomorphism if it
holds on that open. The proof uses the actual translation isomorphisms and
homomorphism square. The construction is shared by flatness and etaleness.

The translation isomorphism and compatibility equation are extracted
unchanged from `Curves/Isogeny/Etale`; the source-cover proof is its general
morphism-property form.
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Scheme.Group.Translation

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{u}} {G H : Grp (Over S)}

/-- Translation by the inverse point is the inverse of the actual translation. -/
def translationIso (a : 𝟙_ (Over S) ⟶ G.X) : G.X ≅ G.X where
  hom := translation a
  inv := translation a⁻¹
  hom_inv_id := by
    change translationHom (G := G) a⁻¹ * translationHom (G := G) a = 1
    rw [← map_mul, inv_mul_cancel, map_one]
  inv_hom_id := by
    change translationHom (G := G) a * translationHom (G := G) a⁻¹ = 1
    rw [← map_mul, mul_inv_cancel, map_one]

/-- A native group homomorphism commutes with the literal translations. -/
@[reassoc] theorem translation_comp_hom (f : G ⟶ H)
    (a : 𝟙_ (Over S) ⟶ G.X) :
    translation a ≫ f.hom.hom = f.hom.hom ≫ translation (a ≫ f.hom.hom) := by
  simp [translation, MonObj.mul_comp, MonObj.comp_mul]

end AlgebraicGeometry.Scheme.Group.Translation

namespace AlgebraicGeometry.Scheme.Group.Translation

attribute [local instance] Over.cartesianMonoidalCategory

/-- A property local at the source spreads from a nonempty open along
actual group translations over an algebraically closed field. -/
theorem property_of_nonempty_open
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    {k : Type u} [Field k] [IsAlgClosed k]
    (G H : Grp (Over (Spec (.of k)))) [LocallyOfFiniteType G.X.hom]
    (f : G ⟶ H) (W : G.X.left.Opens) (hW : Nonempty W)
    (hP : P (W.ι ≫ f.hom.hom.left)) : P f.hom.hom.left := by
  let : JacobsonSpace G.X.left := LocallyOfFiniteType.jacobsonSpace G.X.hom
  obtain ⟨p, hpW, hp⟩ := nonempty_inter_closedPoints
    (show (W : Set G.X.left).Nonempty from
      ⟨(Classical.choice hW).val, (Classical.choice hW).property⟩) W.isOpen.isLocallyClosed
  let c : 𝟙_ (Over (Spec (.of k))) ⟶ G.X :=
    Over.homMk (pointOfClosedPoint G.X.hom p hp) (pointOfClosedPoint_comp G.X.hom p hp)
  have hc : c.left (IsLocalRing.closedPoint k) = p := by
    exact pointOfClosedPoint_apply G.X.hom p hp _
  let t (a : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) : W.toScheme ⟶ G.X.left :=
    W.ι ≫ (translation a).left
  have htIso (a : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) : IsIso (translation a).left := by
    let : IsIso (translation a) := (translationIso a).isIso_hom
    exact (Over.forget (Spec (.of k))).map_isIso (translation a)
  have htOpen (a : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) : IsOpenImmersion (t a) := by
    let := htIso a
    dsimp [t]
    infer_instance
  let U (a : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) : G.X.left.Opens := (t a).opensRange
  have hProp (a : 𝟙_ (Over (Spec (.of k))) ⟶ G.X) : P (t a ≫ f.hom.hom.left) := by
    have heq : t a ≫ f.hom.hom.left =
        (W.ι ≫ f.hom.hom.left) ≫ (translation (a ≫ f.hom.hom)).left := by
      dsimp [t]
      rw [Category.assoc, ← Over.comp_left, translation_comp_hom]
      rfl
    rw [heq]
    let : IsIso (translation (a ≫ f.hom.hom)).left := by
      let : IsIso (translation (a ≫ f.hom.hom)) :=
        (translationIso (a ≫ f.hom.hom)).isIso_hom
      exact (Over.forget (Spec (.of k))).map_isIso (translation (a ≫ f.hom.hom))
    exact (P.cancel_right_of_respectsIso _ _).mpr hP
  have hCover : iSup U = ⊤ := by
    apply top_le_iff.mp
    intro x _
    by_contra hx
    obtain ⟨q, hqU, hq⟩ := nonempty_inter_closedPoints
      (show ((iSup U : G.X.left.Opens) : Set G.X.left)ᶜ.Nonempty from ⟨x, hx⟩)
      (iSup U).isOpen.isClosed_compl.isLocallyClosed
    let b : 𝟙_ (Over (Spec (.of k))) ⟶ G.X :=
      Over.homMk (pointOfClosedPoint G.X.hom q hq) (pointOfClosedPoint_comp G.X.hom q hq)
    have hb : b.left (IsLocalRing.closedPoint k) = q :=
      pointOfClosedPoint_apply G.X.hom q hq _
    have htrans : c ≫ translation (b * c⁻¹) = b := by
      simp [comp_translation]
    have hq : q ∈ U (b * c⁻¹) := by
      refine ⟨⟨p, hpW⟩, ?_⟩
      have hpoint : (translation (b * c⁻¹)).left (c.left (IsLocalRing.closedPoint k)) =
          b.left (IsLocalRing.closedPoint k) :=
        congrArg (fun z : 𝟙_ (Over (Spec (.of k))) ⟶ G.X =>
          z.left (IsLocalRing.closedPoint k)) htrans
      change (translation (b * c⁻¹)).left p = q
      simpa only [hc, hb] using hpoint
    exact hqU (Opens.mem_iSup.mpr ⟨b * c⁻¹, hq⟩)
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := P) U hCover
  intro a
  let := htOpen a
  let e := IsOpenImmersion.isoOfRangeEq (t a) (U a).ι (by simp [U])
  apply (MorphismProperty.cancel_left_of_respectsIso P e.hom
    ((U a).ι ≫ f.hom.hom.left)).mp
  rw [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]
  exact hProp a

end AlgebraicGeometry.Scheme.Group.Translation
