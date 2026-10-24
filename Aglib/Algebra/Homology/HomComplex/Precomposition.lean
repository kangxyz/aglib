/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # Native Hom-complex precomposition and injective extension -/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L M : CochainComplex C ℤ} (f : K ⟶ L) (I : CochainComplex C ℤ)

/-- Precomposition on the existing native complex of abelian groups. -/
def precompMap : HomComplex L I ⟶ HomComplex K I where
  f n := AddCommGrpCat.ofHom
    { toFun := fun z => (Cochain.ofHom f).comp z (zero_add n)
      map_zero' := by simp
      map_add' := fun a b => Cochain.comp_add _ a b _ }
  comm' n m _hnm := by
    ext z
    change δ n m ((Cochain.ofHom f).comp z (zero_add n)) =
      (Cochain.ofHom f).comp (δ n m z) (zero_add m)
    exact δ_ofHom_comp f z m

@[simp]
lemma precompMap_f_apply (n : ℤ) (z : Cochain L I n) :
    (precompMap f I).f n z = (Cochain.ofHom f).comp z (zero_add n) := rfl

@[simp]
lemma precompMap_id : precompMap (𝟙 K) I = 𝟙 (HomComplex K I) := by
  ext n z
  change (Cochain.ofHom (𝟙 K)).comp z (zero_add n) = z
  exact Cochain.id_comp z

@[reassoc]
lemma precompMap_comp (g : L ⟶ M) :
    precompMap (f ≫ g) I = precompMap g I ≫ precompMap f I := by
  ext n z
  change (Cochain.ofHom (f ≫ g)).comp z (zero_add n) =
    (Cochain.ofHom f).comp ((Cochain.ofHom g).comp z (zero_add n)) (zero_add n)
  rw [Cochain.ofHom_comp]
  exact Cochain.comp_assoc_of_first_is_zero_cochain (Cochain.ofHom f)
    (Cochain.ofHom g) z (zero_add n)

variable [Mono f] [∀ n, Injective (I.X n)]

/-- Termwise injectivity extends every cochain along a monomorphism of sources.
No cycle or chain-map extension is asserted. -/
lemma precompMap_surjective (n : ℤ) : Function.Surjective ((precompMap f I).f n) := by
  have (p : ℤ) : Mono (f.f p) := (HomologicalComplex.eval C (.up ℤ) p).map_mono f
  intro z
  refine ⟨Cochain.mk (fun p q hpq => Injective.factorThru (z.v p q hpq) (f.f p)), ?_⟩
  change (Cochain.ofHom f).comp
    (Cochain.mk (fun p q hpq => Injective.factorThru (z.v p q hpq) (f.f p)))
    (zero_add n) = z
  ext p q hpq
  simp [Injective.comp_factorThru]

end CochainComplex.HomComplex
