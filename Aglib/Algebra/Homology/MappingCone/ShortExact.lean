/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.MappingCone.Map
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Actual mapping cones preserve short exact coefficient sequences

The functor uses the original signed mapping cone and its literal maps of commuting squares.
The existing homotopy-cofiber term comparison identifies these maps with actual binary
biproduct maps. Kernel universal properties and degreewise exactness prove preservation of
short exact sequences whenever both endpoint functors preserve the given sequence.

Source: `Quillen/Algebra/Homology/MappingConeShortExact.lean` from the delivered archive.
Source SHA-256: `efc41ac9598b78dbcfe52dcc62a429d2e2f3d193693d7dabb362ef25b9815fd2`.
Selection: the complete general construction and short-exactness theorem, with native
short-complex and cochain-complex owners; the original maps and hypotheses are retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open _root_.CochainComplex
attribute [local instance] Abelian.hasFiniteBiproducts
namespace CategoryTheory.ShortComplex
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The literal block-diagonal short complex of two original short complexes. -/
def biprodMap (S T : ShortComplex A) : ShortComplex A :=
  ShortComplex.mk (biprod.map S.f T.f) (biprod.map S.g T.g) (by
    apply biprod.hom_ext <;> simp)

/-- The actual block-diagonal sequence is short exact by the two kernel universal properties. -/
theorem shortExact_biprodMap {S T : ShortComplex A}
    (hS : S.ShortExact) (hT : T.ShortExact) : (biprodMap S T).ShortExact := by
  have : Mono S.f := hS.mono_f
  have : Mono T.f := hT.mono_f
  have : Epi S.g := hS.epi_g
  have : Epi T.g := hT.epi_g
  have hk : IsLimit (KernelFork.ofι (biprod.map S.f T.f)
      (biprodMap S T).zero) := by
    refine KernelFork.IsLimit.ofι _ _ (fun {W} m hm =>
      biprod.lift
        (hS.fIsKernel.lift (KernelFork.ofι (m ≫ biprod.fst) ?_))
        (hT.fIsKernel.lift (KernelFork.ofι (m ≫ biprod.snd) ?_))) ?_ ?_
    · simpa only [biprodMap, Category.assoc, biprod.map_fst, zero_comp] using
        congrArg (fun f => f ≫ (biprod.fst : S.X₃ ⊞ T.X₃ ⟶ S.X₃)) hm
    · simpa only [biprodMap, Category.assoc, biprod.map_snd, zero_comp] using
        congrArg (fun f => f ≫ (biprod.snd : S.X₃ ⊞ T.X₃ ⟶ T.X₃)) hm
    · intro W m hm
      apply biprod.hom_ext
      · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc]
        exact hS.fIsKernel.fac _ WalkingParallelPair.zero
      · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc]
        exact hT.fIsKernel.fac _ WalkingParallelPair.zero
    · intro W m hm t ht
      apply biprod.hom_ext
      · apply (cancel_mono S.f).1
        have h := congrArg (fun f => f ≫ (biprod.fst : S.X₂ ⊞ T.X₂ ⟶ S.X₂)) ht
        have h' : t ≫ biprod.fst ≫ S.f = m ≫ biprod.fst := by
          simpa only [Category.assoc, biprod.map_fst] using h
        simpa only [biprod.lift_fst, Category.assoc, Fork.app_zero_eq_ι, KernelFork.ι_ofι] using
          h'.trans (hS.fIsKernel.fac
          (KernelFork.ofι (m ≫ biprod.fst) (by
            simpa only [biprodMap, Category.assoc, biprod.map_fst, zero_comp] using
              congrArg (fun f => f ≫ (biprod.fst : S.X₃ ⊞ T.X₃ ⟶ S.X₃)) hm))
          WalkingParallelPair.zero).symm
      · apply (cancel_mono T.f).1
        have h := congrArg (fun f => f ≫ (biprod.snd : S.X₂ ⊞ T.X₂ ⟶ T.X₂)) ht
        have h' : t ≫ biprod.snd ≫ T.f = m ≫ biprod.snd := by
          simpa only [Category.assoc, biprod.map_snd] using h
        simpa only [biprod.lift_snd, Category.assoc, Fork.app_zero_eq_ι, KernelFork.ι_ofι] using
          h'.trans (hT.fIsKernel.fac
          (KernelFork.ofι (m ≫ biprod.snd) (by
            simpa only [biprodMap, Category.assoc, biprod.map_snd, zero_comp] using
              congrArg (fun f => f ≫ (biprod.snd : S.X₃ ⊞ T.X₃ ⟶ T.X₃)) hm))
          WalkingParallelPair.zero).symm
  exact {
    exact := ShortComplex.exact_of_f_is_kernel _ hk
    mono_f := by change Mono (biprod.map S.f T.f); infer_instance
    epi_g := by change Epi (biprod.map S.g T.g); infer_instance }

end CategoryTheory.ShortComplex

namespace CochainComplex
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The existing homotopy-cofiber comparison, on the literal signed mapping cone. -/
def mappingConeTermIso {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    (mappingCone f).X n ≅ K.X (n + 1) ⊞ L.X n :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod f n (n + 1) rfl

/-- The actual first cone inclusion is the original biproduct inclusion. -/
@[reassoc (attr := simp)]
theorem mappingConeTermIso_inl {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    (mappingCone.inl f).v (n + 1) n (by omega) ≫ (mappingConeTermIso f n).hom =
      biprod.inl :=
  HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom f (n + 1) n rfl

/-- The actual second cone inclusion is the original biproduct inclusion. -/
@[reassoc (attr := simp)]
theorem mappingConeTermIso_inr {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    (mappingCone.inr f).f n ≫ (mappingConeTermIso f n).hom = biprod.inr :=
  HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom f (n + 1) n rfl

/-- Literal cone maps are the original endpoint biproduct maps in every degree. -/
theorem mappingConeTermIso_naturality {K L K' L' : CochainComplex A ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) (n : ℤ) :
    (mappingConeTermIso f n).hom ≫ biprod.map (a.f (n + 1)) (b.f n) =
      (mappingCone.map f g a b h).f n ≫ (mappingConeTermIso g n).hom := by
  simp [mappingCone.ext_from_iff _ (n + 1) n rfl, mappingCone.map]

variable {D : Type u'} [Category.{v'} D]

/-- The actual signed cone functor of an actual natural transformation. -/
def mappingConeNatTransFunctor {F G : D ⥤ CochainComplex A ℤ} (α : F ⟶ G) :
    D ⥤ CochainComplex A ℤ where
  obj K := mappingCone (α.app K)
  map g := mappingCone.map _ _ (F.map g) (G.map g) (α.naturality g).symm
  map_id K := by
    ext n
    simp [mappingCone.ext_from_iff _ (n + 1) n rfl, mappingCone.map]
  map_comp f g := by
    ext n
    simp [mappingCone.ext_from_iff _ (n + 1) n rfl, mappingCone.map]

variable [Preadditive D] {F G : D ⥤ CochainComplex A ℤ} [F.Additive] [G.Additive]

instance mappingConeNatTransFunctor_additive (α : F ⟶ G) :
    (mappingConeNatTransFunctor α).Additive where
  map_add {K L} f g := by
    ext n
    simp [mappingConeNatTransFunctor, mappingCone.ext_from_iff _ (n + 1) n rfl,
      mappingCone.map, Preadditive.comp_add, Preadditive.add_comp]

/-- Both actual endpoint sequences being short exact makes their literal cone sequence exact. -/
theorem mappingConeNatTransFunctor_shortExact (α : F ⟶ G) (S : ShortComplex D)
    (hF : (S.map F).ShortExact) (hG : (S.map G).ShortExact) :
    (S.map (mappingConeNatTransFunctor α)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let U := (S.map F).map (HomologicalComplex.eval A (.up ℤ) (n + 1))
  let V := (S.map G).map (HomologicalComplex.eval A (.up ℤ) n)
  let e : ((S.map (mappingConeNatTransFunctor α)).map
      (HomologicalComplex.eval A (.up ℤ) n)) ≅ ShortComplex.biprodMap U V :=
    ShortComplex.isoMk (mappingConeTermIso (α.app S.X₁) n)
      (mappingConeTermIso (α.app S.X₂) n) (mappingConeTermIso (α.app S.X₃) n)
      (mappingConeTermIso_naturality _ _ (F.map S.f) (G.map S.f)
        (α.naturality S.f).symm n)
      (mappingConeTermIso_naturality _ _ (F.map S.g) (G.map S.g)
        (α.naturality S.g).symm n)
  exact ShortComplex.shortExact_of_iso e.symm
    (ShortComplex.shortExact_biprodMap
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp hF (n + 1))
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp hG n))

end CochainComplex
