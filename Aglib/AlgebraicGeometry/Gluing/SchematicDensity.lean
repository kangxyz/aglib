/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.Basic
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing extensions from a schematically dense source

Maps on an open cover which extend the same map from a quasi-compact,
scheme-theoretically dominant source glue into a relatively separated target.
The dense morphism need not be an open immersion. The construction retains the
literal cover maps, the original dense-source map, and the structural morphism.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

universe u v

namespace AlgebraicGeometry.Scheme.Cover

variable {X U Y S : Scheme.{u}} (C : X.OpenCover.{v})
  (pX : X ⟶ S) (pY : Y ⟶ S) [IsSeparated pY]
  (j : U ⟶ X) [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
  (gU : U ⟶ Y) (g : ∀ i, C.X i ⟶ Y)
  (hbase : ∀ i, C.f i ≫ pX = g i ≫ pY)
  (hcompat : ∀ i, pullback.fst (C.f i) j ≫ g i = pullback.snd (C.f i) j ≫ gU)

include hbase hcompat in
/-- Compatibility on the dense base changes implies actual equality on every
whole overlap of the open cover. Quasi-compactness of the dense morphism is used
only for scheme-theoretic dominance after flat base change. -/
lemma overlap_eq_of_schemeTheoreticallyDominant (i k : C.I₀) :
    pullback.fst (C.f i) (C.f k) ≫ g i = pullback.snd (C.f i) (C.f k) ≫ g k := by
  let w : pullback (C.f i) (C.f k) ⟶ X := pullback.fst (C.f i) (C.f k) ≫ C.f i
  let t := pullback.fst w j
  let : IsSchemeTheoreticallyDominant t := inferInstance
  apply QuasiDomination.hom_ext_of_schemeTheoreticallyDominant t pY
  · simpa only [Category.assoc, ← hbase i, ← hbase k] using
      congrArg (fun a => a ≫ pX) (pullback.condition (f := C.f i) (g := C.f k))
  · let li : pullback w j ⟶ pullback (C.f i) j :=
      pullback.lift (t ≫ pullback.fst (C.f i) (C.f k)) (pullback.snd w j) (by
        simpa only [t, w, Category.assoc] using (pullback.condition (f := w) (g := j)))
    let lk : pullback w j ⟶ pullback (C.f k) j :=
      pullback.lift (t ≫ pullback.snd (C.f i) (C.f k)) (pullback.snd w j) (by
        calc
          (t ≫ pullback.snd (C.f i) (C.f k)) ≫ C.f k =
              t ≫ (pullback.fst (C.f i) (C.f k) ≫ C.f i) := by
            simpa only [Category.assoc] using
              congrArg (fun a => t ≫ a) (pullback.condition (f := C.f i) (g := C.f k)).symm
          _ = pullback.snd w j ≫ j := pullback.condition)
    have hi : t ≫ pullback.fst (C.f i) (C.f k) ≫ g i = pullback.snd w j ≫ gU := by
      simpa [li] using congrArg (fun a => li ≫ a) (hcompat i)
    have hk : t ≫ pullback.snd (C.f i) (C.f k) ≫ g k = pullback.snd w j ≫ gU := by
      simpa [lk] using congrArg (fun a => lk ≫ a) (hcompat k)
    exact hi.trans hk.symm

/-- Glue the actual local extensions of a common schematically dense map. -/
def glueMorphismsOfSchemeTheoreticallyDominant : X ⟶ Y :=
  C.glueMorphisms g
    (overlap_eq_of_schemeTheoreticallyDominant C pX pY j gU g hbase hcompat)

/-- The glued map restricts to the originally supplied morphism on every chart. -/
@[reassoc (attr := simp)]
lemma ι_glueMorphismsOfSchemeTheoreticallyDominant (i : C.I₀) :
    C.f i ≫ glueMorphismsOfSchemeTheoreticallyDominant C pX pY j gU g hbase hcompat = g i :=
  C.ι_glueMorphisms g _ i

/-- The global extension agrees with the literal map on the dense source.
This is checked on the actual pullback cover of that source. -/
@[reassoc (attr := simp)]
lemma comp_glueMorphismsOfSchemeTheoreticallyDominant :
    j ≫ glueMorphismsOfSchemeTheoreticallyDominant C pX pY j gU g hbase hcompat = gU := by
  apply Scheme.Cover.hom_ext (C.pullback₂ j)
  intro i
  change pullback.snd (C.f i) j ≫ (j ≫ _) = pullback.snd (C.f i) j ≫ gU
  rw [← Category.assoc, ← pullback.condition, Category.assoc,
    ι_glueMorphismsOfSchemeTheoreticallyDominant]
  exact hcompat i

/-- The global extension preserves the specified structural morphism. -/
@[reassoc (attr := simp)]
lemma glueMorphismsOfSchemeTheoreticallyDominant_comp :
    glueMorphismsOfSchemeTheoreticallyDominant C pX pY j gU g hbase hcompat ≫ pY = pX := by
  apply C.hom_ext
  intro i
  simpa using (hbase i).symm

include hbase hcompat in
/-- Actual global gluing with all chart triangles, the original-source triangle,
and the base triangle retained together. -/
lemma exists_glue_of_schemeTheoreticallyDominant :
    ∃ G : X ⟶ Y, (∀ i, C.f i ≫ G = g i) ∧ j ≫ G = gU ∧ G ≫ pY = pX :=
  ⟨glueMorphismsOfSchemeTheoreticallyDominant C pX pY j gU g hbase hcompat,
    ι_glueMorphismsOfSchemeTheoreticallyDominant C pX pY j gU g hbase hcompat,
    comp_glueMorphismsOfSchemeTheoreticallyDominant C pX pY j gU g hbase hcompat,
    glueMorphismsOfSchemeTheoreticallyDominant_comp C pX pY j gU g hbase hcompat⟩

end AlgebraicGeometry.Scheme.Cover
