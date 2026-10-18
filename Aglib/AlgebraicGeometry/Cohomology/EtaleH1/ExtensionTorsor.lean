/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.TorsorCohomology
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Torsors as fibres of actual locally surjective abelian extensions

Construction prerequisite for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. The carrier is the actual sheaf of
sections over a fixed global quotient section, not an assumed torsor model.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.EtaleH1
universe u
attribute [local instance] hasSheafifyLarge
variable {X : Scheme.{u}}

/-- Restriction of an actual global section of an abelian sheaf. -/
def restrictSection (F : AbelianSheaf.{u, u + 1} X)
    (z : F.obj.obj (op (etaleTerminal X))) (U : X.Etaleᵒᵖ) : F.obj.obj U :=
  F.obj.map ((etaleTerminalIsTerminal X).from U.unop).op z

theorem restrictSection_naturality (F : AbelianSheaf.{u, u + 1} X)
    (z : F.obj.obj (op (etaleTerminal X))) {U V : X.Etaleᵒᵖ} (f : U ⟶ V) :
    F.obj.map f (restrictSection F z U) = restrictSection F z V := by
  have h : ((etaleTerminalIsTerminal X).from U.unop).op ≫ f =
      ((etaleTerminalIsTerminal X).from V.unop).op :=
    congrArg Quiver.Hom.op ((etaleTerminalIsTerminal X).hom_ext _ _)
  change F.obj.map f (F.obj.map ((etaleTerminalIsTerminal X).from U.unop).op z) = _
  rw [← Functor.map_comp_apply, h]
  rfl

variable (S : ShortComplex (AbelianSheaf.{u, u + 1} X))
variable (z : S.X₃.obj.obj (op (etaleTerminal X)))

/-- Sections of the middle sheaf lying over the specified quotient section. -/
def extensionFiberSubfunctor : Subfunctor (underlyingSetSheaf S.X₂).obj where
  obj U := {s | S.g.hom.app U s = restrictSection S.X₃ z U}
  map {U V} f s hs := by
    change S.g.hom.app V (S.X₂.obj.map f s) = restrictSection S.X₃ z V
    have hn := ConcreteCategory.congr_hom (S.g.hom.naturality f) s
    change S.g.hom.app V (S.X₂.obj.map f s) = S.X₃.obj.map f (S.g.hom.app U s) at hn
    rw [hn, hs, restrictSection_naturality]

/-- A fibre condition is local because the quotient is a sheaf. -/
theorem extensionFiber_isSheaf :
    Presheaf.IsSheaf (Scheme.smallEtaleTopology X) (extensionFiberSubfunctor S z).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply (Subfunctor.isSheaf_iff (J := Scheme.smallEtaleTopology X) (extensionFiberSubfunctor S z)
    ((isSheaf_iff_isSheaf_of_type _ _).mp (underlyingSetSheaf S.X₂).property)).2
  intro U s hs
  change S.g.hom.app U s = restrictSection S.X₃ z U
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp
    (underlyingSetSheaf S.X₃).property).isSeparated _ hs).ext
  intro V f hf
  change S.X₃.obj.map f.op (S.g.hom.app U s) = S.X₃.obj.map f.op (restrictSection S.X₃ z U)
  rw [restrictSection_naturality]
  have hn := ConcreteCategory.congr_hom (S.g.hom.naturality f.op) s
  change S.g.hom.app (op V) (S.X₂.obj.map f.op s) =
    S.X₃.obj.map f.op (S.g.hom.app U s) at hn
  rw [← hn]
  exact hf

/-- The actual sheaf-theoretic fibre. -/
def extensionFiberSheaf : SetSheaf X :=
  ⟨(extensionFiberSubfunctor S z).toFunctor, extensionFiber_isSheaf S z⟩

/-- Evaluation preserves the actual kernel in a short exact sheaf sequence. -/
def extensionSectionKernel (hS : S.ShortExact) (U : X.Etaleᵒᵖ) :
    IsLimit (KernelFork.ofι (S.f.hom.app U)
      (show S.f.hom.app U ≫ S.g.hom.app U = 0 from
        congrArg (fun q => q.hom.app U) S.zero)) := by
  exact KernelFork.mapIsLimit _ hS.fIsKernel
    (sheafToPresheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1} ⋙
      (CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj U)

/-- The fibre of a short exact abelian sheaf sequence over a global section
is a genuine torsor, with action by addition of the kernel inclusion. -/
def extensionFiberTorsor (hS : S.ShortExact) : Torsor S.X₁ where
  carrier := extensionFiberSheaf S z
  action U a t := ⟨S.f.hom.app U a + (show S.X₂.obj.obj U from t.val), by
    change S.g.hom.app U (S.f.hom.app U a + (show S.X₂.obj.obj U from t.val)) = _
    rw [map_add]
    have hz : S.g.hom.app U (S.f.hom.app U a) = 0 :=
      congrArg (fun q => q.hom.app U a) S.zero
    rw [hz, zero_add]
    exact t.property⟩
  zero_action U t := by apply Subtype.ext; simp
  add_action U a b t := by apply Subtype.ext; simp [add_assoc]
  naturality {U V} f a t := by
    apply Subtype.ext
    change S.X₂.obj.map f (S.f.hom.app U a + (show S.X₂.obj.obj U from t.val)) =
      S.f.hom.app V (S.X₁.obj.map f a) + S.X₂.obj.map f (show S.X₂.obj.obj U from t.val)
    rw [map_add]
    exact congrArg (· + S.X₂.obj.map f (show S.X₂.obj.obj U from t.val))
      (ConcreteCategory.congr_hom (S.f.hom.naturality f) a).symm
  unique_transport U s t := by
    let SU : ShortComplex AddCommGrpCat.{u + 1} := ShortComplex.mk
      (S.f.hom.app U) (S.g.hom.app U)
      (congrArg (fun q => q.hom.app U) S.zero)
    have hex : SU.Exact := SU.exact_of_f_is_kernel (extensionSectionKernel S hS U)
    obtain ⟨a, ha⟩ := (ShortComplex.ab_exact_iff SU).mp hex ((show S.X₂.obj.obj U from t.val) -
      (show S.X₂.obj.obj U from s.val)) (by
      change S.g.hom.app U ((show S.X₂.obj.obj U from t.val) - (show S.X₂.obj.obj U from s.val)) = 0
      rw [map_sub, s.property, t.property, sub_self])
    have hi : Function.Injective (S.f.hom.app U) := by
      let : Mono (S.f.hom.app U) := mono_of_isLimit_fork (extensionSectionKernel S hS U)
      exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance
    refine ⟨a, ?_, ?_⟩
    · apply Subtype.ext
      change S.f.hom.app U a + (show S.X₂.obj.obj U from s.val) = t.val
      change S.f.hom.app U a = (show S.X₂.obj.obj U from t.val) - (show S.X₂.obj.obj U from
        s.val) at ha
      exact eq_sub_iff_add_eq.mp ha
    · intro b hb
      apply hi
      have hb' := congrArg Subtype.val hb
      change S.f.hom.app U b + (show S.X₂.obj.obj U from s.val) = t.val at hb'
      exact (eq_sub_iff_add_eq.mpr hb').trans ha.symm
  locally_nonempty U := by
    let : Sheaf.IsLocallySurjective S.g :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1} S.g).mpr hS.epi_g
    refine (Scheme.smallEtaleTopology X).superset_covering ?_
      (Presheaf.imageSieve_mem (Scheme.smallEtaleTopology X) S.g.hom
        (restrictSection S.X₃ z (op U)))
    rintro V f ⟨t, ht⟩
    exact ⟨⟨t, ht.trans (restrictSection_naturality S.X₃ z f.op)⟩⟩

end AlgebraicGeometry.Scheme.EtaleH1

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 e253e8aa107e7041b57acc328a4109a66c86deda16fe337e14e0fb62c6ec34f4.
Definitions, hypotheses and universes are retained modulo native names. -/
