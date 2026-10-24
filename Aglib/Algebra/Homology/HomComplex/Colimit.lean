/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Homology.HomComplex.Precomposition

/-!
# Cochain descent along native colimits of source complexes

Compatible cochains on every stage descend uniquely to the actual colimit.
This is the degreewise continuity input for predecessor inverse limits of
Hom complexes; no exactness of arbitrary inverse limits is used.
-/

@[expose] public noncomputable section

universe w w' v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {J : Type w} [Category.{w'} J] [HasColimitsOfShape J C]
  (F : J ⥤ CochainComplex C ℤ) (I : CochainComplex C ℤ) (n : ℤ)
  (z : ∀ j, Cochain (F.obj j) I n)
  (hz : ∀ {j k : J} (f : j ⟶ k),
    (Cochain.ofHom (F.map f)).comp (z k) (zero_add n) = z j)

/-- The component cocone of a compatible cochain family. -/
def cochainCocone (p q : ℤ) (hpq : p + n = q) :
    Cocone (F ⋙ eval C (.up ℤ) p) where
  pt := I.X q
  ι :=
    { app := fun j => (z j).v p q hpq
      naturality := fun j k f => by
        simpa using Cochain.congr_v (hz f) p q hpq }

/-- Descend a compatible family to a cochain on the original colimit complex. -/
def cochainDesc : Cochain (colimit F) I n :=
  Cochain.mk (fun p q hpq =>
    (isColimitOfPreserves (eval C (.up ℤ) p) (colimit.isColimit F)).desc
      (cochainCocone F I n z hz p q hpq))

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma cochainDesc_precomp (j : J) :
    (Cochain.ofHom (colimit.ι F j)).comp (cochainDesc F I n z hz) (zero_add n) = z j := by
  ext p q hpq
  simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  exact (isColimitOfPreserves (eval C (.up ℤ) p) (colimit.isColimit F)).fac
    (cochainCocone F I n z hz p q hpq) j

set_option backward.isDefEq.respectTransparency false in
/-- Restrictions to all original colimit inclusions determine a cochain. -/
lemma cochain_ext_colimit {a b : Cochain (colimit F) I n}
    (h : ∀ j, (Cochain.ofHom (colimit.ι F j)).comp a (zero_add n) =
      (Cochain.ofHom (colimit.ι F j)).comp b (zero_add n)) : a = b := by
  ext p q hpq
  apply (isColimitOfPreserves (eval C (.up ℤ) p) (colimit.isColimit F)).hom_ext
  intro j
  change (colimit.ι F j).f p ≫ a.v p q hpq =
    (colimit.ι F j).f p ≫ b.v p q hpq
  simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
    Cochain.congr_v (h j) p q hpq

/-- Descent is the genuine universal property, with no separately chosen target carrier. -/
lemma cochainDesc_unique (a : Cochain (colimit F) I n)
    (ha : ∀ j, (Cochain.ofHom (colimit.ι F j)).comp a (zero_add n) = z j) :
    a = cochainDesc F I n z hz := by
  apply cochain_ext_colimit F I n
  intro j
  rw [ha j, cochainDesc_precomp]

/-- Compatible boundaries descend with their primitives, retaining strict equality. -/
lemma δ_cochainDesc (m : ℤ) :
    δ n m (cochainDesc F I n z hz) =
      cochainDesc F I m (fun j => δ n m (z j))
        (fun {_ _} f => by rw [← δ_ofHom_comp, hz f]) := by
  apply cochain_ext_colimit F I m
  intro j
  rw [← δ_ofHom_comp, cochainDesc_precomp, cochainDesc_precomp]

end CochainComplex.HomComplex
