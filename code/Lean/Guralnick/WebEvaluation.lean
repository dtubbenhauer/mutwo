import Guralnick.ParabolicWeb

/-!
# Integral evaluation of refinement paths

A split is the actual inclusion of parabolic right ideals. A merge is the
unique integral map taking every `C_I*h` to `C_J*h`. Thus resolving a thick
vertex into binary vertices does not change its map. This file evaluates
paths of absolute-position parabolic refinements, not arbitrary annular
rotations: equal masks alone cannot justify forgetting winding.
-/
noncomputable section
namespace Guralnick.WebEvaluation
open Hecke ParabolicWeb SphericalMaps

/-- The action on every cyclic generator determines a merge uniquely. -/
theorem merge_linear_unique {A : Type*} [Ring A] [Algebra SphericalMaps.R A]
    {C₀ C₁ : A} (f g : Merge C₀ C₁) : f.linear=g.linear := by
  apply LinearMap.ext
  intro x
  obtain ⟨h,hh⟩:=x.property
  have hx : x=generator C₀ h := Subtype.ext hh.symm
  apply Subtype.ext
  rw [hx,f.on_generator,g.on_generator]

/-- Two consecutive integral merges are the direct integral merge. -/
theorem merge_comp_unique {A : Type*} [Ring A] [Algebra SphericalMaps.R A]
    {C₀ C₁ C₂ : A} (f : Merge C₀ C₁) (g : Merge C₁ C₂) (h : Merge C₀ C₂) :
    g.linear.comp f.linear=h.linear := by
  apply LinearMap.ext
  intro x
  obtain ⟨a,ha⟩:=x.property
  have hx : x=generator C₀ a := Subtype.ext ha.symm
  have hf : f.linear (generator C₀ a)=generator C₁ a :=
    Subtype.ext (f.on_generator a)
  apply Subtype.ext
  simp only [LinearMap.comp_apply,hx,hf,g.on_generator,h.on_generator]

variable {n : ℕ} {c : WindowCoxeter n} (K : KLRealization c)
variable (D : ∀ I : Index n, LongestData c I) (L : Laws K D)

abbrev ModuleAt (I : Index n) := spherical (symmetrizer K D I)

def split {I J : Index n} (h : J.val⊆I.val) :
    ModuleAt K D I →ₗ[Hecke.R] ModuleAt K D J :=
  Submodule.inclusion (L.inclusion J I h)

def merge {I J : Index n} (h : I.val⊆J.val) :
    ModuleAt K D I →ₗ[Hecke.R] ModuleAt K D J :=
  (Classical.choice (L.merge_exists I J h)).linear

@[simp] theorem split_val {I J : Index n} (h : J.val⊆I.val) (x : ModuleAt K D I) :
    (split K D L h x).val=x.val := rfl

@[simp] theorem merge_generator {I J : Index n} (h : I.val⊆J.val)
    (a : Hecke.Algebra n) :
    (merge K D L h (generator (symmetrizer K D I) a)).val=symmetrizer K D J*a :=
  (Classical.choice (L.merge_exists I J h)).on_generator a

theorem split_comp {I J T : Index n} (h₁ : J.val⊆I.val) (h₂ : T.val⊆J.val) :
    (split K D L h₂).comp (split K D L h₁)=split K D L (h₂.trans h₁) := by
  ext x
  rfl

theorem merge_comp {I J T : Index n} (h₁ : I.val⊆J.val) (h₂ : J.val⊆T.val) :
    (merge K D L h₂).comp (merge K D L h₁)=merge K D L (h₁.trans h₂) :=
  merge_comp_unique _ _ _

theorem split_refl (I : Index n) : split K D L (Finset.Subset.refl I.val)=LinearMap.id := by
  ext x
  rfl

theorem merge_refl (I : Index n) : merge K D L (Finset.Subset.refl I.val)=LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨a,ha⟩:=x.property
  have hx : x=generator (symmetrizer K D I) a := Subtype.ext ha.symm
  apply Subtype.ext
  rw [hx,merge_generator]
  rfl

/-- Paths of actual absolute-position refinements. There is deliberately
no constructor interpreting arbitrary annular winding as an identity. -/
inductive Path : Index n → Index n → Type
  | nil (I : Index n) : Path I I
  | split {I J T : Index n} (p : Path I J) (h : T.val⊆J.val) : Path I T
  | merge {I J T : Index n} (p : Path I J) (h : J.val⊆T.val) : Path I T

namespace Path

def linear : {I J : Index n} → Path I J → ModuleAt K D I →ₗ[Hecke.R] ModuleAt K D J
  | _,_,.nil _ => LinearMap.id
  | _,_,.split p h => (WebEvaluation.split K D L h).comp (linear p)
  | _,_,.merge p h => (WebEvaluation.merge K D L h).comp (linear p)

def raw {I J : Index n} (p : Path I J) : Hecke.Algebra n :=
  (linear K D L p (generator (symmetrizer K D I) 1)).val

/-- Binary resolution of a multi-split has exactly its direct map. -/
theorem split_split {I J U T : Index n} (p : Path I J)
    (h₁ : U.val⊆J.val) (h₂ : T.val⊆U.val) :
    linear K D L ((p.split h₁).split h₂)=linear K D L (p.split (h₂.trans h₁)) := by
  simp only [linear,←LinearMap.comp_assoc,WebEvaluation.split_comp]

/-- Binary resolution of a multi-merge has exactly its direct map. -/
theorem merge_merge {I J U T : Index n} (p : Path I J)
    (h₁ : J.val⊆U.val) (h₂ : U.val⊆T.val) :
    linear K D L ((p.merge h₁).merge h₂)=linear K D L (p.merge (h₁.trans h₂)) := by
  simp only [linear,←LinearMap.comp_assoc,WebEvaluation.merge_comp]

end Path

namespace Family
variable {m : ℕ} {c : WindowCoxeter (2*m+1)} (K : KLRealization c)
variable (D : ∀ I : Index (2*m+1), LongestData c I) (L : Laws K D)

/-- The six operations, as a typed path rather than a prescribed answer. -/
def path (m : ℕ) : Path (ParabolicWeb.Family.source m) (ParabolicWeb.Family.output m) :=
  ((((((Path.nil (ParabolicWeb.Family.source m)).split
    (ParabolicWeb.Family.output_source m)).merge (ParabolicWeb.Family.output_cyclic m)).split
    (ParabolicWeb.Family.common_cyclic m)).merge (ParabolicWeb.Family.common_middle m)).split
    (ParabolicWeb.Family.common_middle m)).merge (ParabolicWeb.Family.common_output m)

theorem linear_eq_sixMaps :
    Path.linear K D L (path m)=(ParabolicWeb.Family.sixMaps K D L).linear := by
  apply LinearMap.ext
  intro x
  simp only [path,Path.linear,split,merge,SixMaps.linear,ParabolicWeb.Family.sixMaps,
    LinearMap.comp_apply,LinearMap.id_apply]

theorem raw_eq : Path.raw K D L (path m)=ParabolicWeb.Family.raw K D L := by
  simp only [Path.raw,linear_eq_sixMaps,SixMaps.linear_apply]
  rfl

end Family
end Guralnick.WebEvaluation
