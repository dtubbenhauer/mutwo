import Guralnick.WebTraceEvaluation

/-!
# Right Hecke linearity of the graph evaluation

The interpreted graph is an actual morphism of spherical right Hecke
modules, not just a coefficient-ring linear map with a selected value.
Every local map commutes with right multiplication; its value on the
spherical generator therefore determines the whole morphism.
-/
noncomputable section
namespace Guralnick.WebRightLinearity
open SphericalMaps

variable {A : Type*} [Ring A] [Algebra SphericalMaps.R A]

def rightMul {C : A} (x : spherical C) (h : A) : spherical C :=
  ⟨x.val*h,right_closed C x h⟩

@[simp] theorem rightMul_val {C : A} (x : spherical C) (h : A) :
    (rightMul x h).val=x.val*h := rfl

@[simp] theorem rightMul_generator (C a h : A) :
    rightMul (generator C a) h=generator C (a*h) := by
  apply Subtype.ext
  exact mul_assoc C a h

def RightLinear {C D : A} (f : spherical C →ₗ[SphericalMaps.R] spherical D) : Prop :=
  ∀ (x : spherical C) (h : A), f (rightMul x h)=rightMul (f x) h

theorem merge_rightLinear {C D : A} (f : Merge C D) : RightLinear f.linear := by
  intro x h
  obtain ⟨a,ha⟩:=x.property
  have hx : x=generator C a := Subtype.ext ha.symm
  apply Subtype.ext
  simp only [hx,rightMul_generator,f.on_generator,rightMul_val]
  exact (mul_assoc D a h).symm

theorem inclusion_rightLinear {C D : A} (h : spherical C≤spherical D) :
    RightLinear (Submodule.inclusion h) := by
  intro x a
  rfl

theorem id_rightLinear (C : A) : RightLinear (LinearMap.id : spherical C →ₗ[SphericalMaps.R] spherical C) := by
  intro x a
  rfl

theorem comp_rightLinear {C D E : A}
    {f : spherical C →ₗ[SphericalMaps.R] spherical D}
    {g : spherical D →ₗ[SphericalMaps.R] spherical E}
    (hf : RightLinear f) (hg : RightLinear g) : RightLinear (g.comp f) := by
  intro x a
  exact (congrArg g (hf x a)).trans (hg (f x) a)

/-- Equality of the generator images is equality of the entire right
module maps, once actual right-linearity has been established. -/
theorem ext_generator {C D : A} (f g : spherical C →ₗ[SphericalMaps.R] spherical D)
    (hf : RightLinear f) (hg : RightLinear g)
    (h : (f (generator C 1)).val=(g (generator C 1)).val) : f=g := by
  apply LinearMap.ext
  intro x
  obtain ⟨a,ha⟩:=x.property
  have hx : x=rightMul (generator C 1) a := by
    apply Subtype.ext
    simpa [rightMul,generator] using ha.symm
  rw [hx,hf,hg]
  exact congrArg (fun y : spherical D => rightMul y a) (Subtype.ext h)

open Hecke ParabolicWeb WebTrace WebEvaluation WebTraceEvaluation
variable {n : ℕ} (hn : 0<n) {c : WindowCoxeter n} (K : KLRealization c)
variable (D : ∀ I : Index n, LongestData c I) (L : Laws K D)

theorem reframe_rightLinear {I J : Index n} (h : I=J) :
    RightLinear (reframe K D h) := by
  subst J
  exact id_rightLinear _

theorem event_rightLinear {s t : State} (e : Event hn s t) :
    RightLinear (e.linear hn K D L) := by
  cases hop : e.op with
  | split i a b =>
    rw [e.linear_split hn K D L i a b hop]
    exact inclusion_rightLinear _
  | merge i =>
    rw [e.linear_merge hn K D L i hop]
    exact merge_rightLinear _
  | rotateRight =>
    rw [e.linear_rotateRight hn K D L hop]
    exact reframe_rightLinear K D _
  | rotateLeft =>
    rw [e.linear_rotateLeft hn K D L hop]
    exact reframe_rightLinear K D _

theorem program_rightLinear {s t : State} (p : Program hn s t) :
    RightLinear (p.linear hn K D L) := by
  induction p with
  | nil =>
    simpa only [Program.linear] using id_rightLinear (symmetrizer K D (stateIndex hn s))
  | snoc p e ih =>
    simpa only [Program.linear] using comp_rightLinear ih (event_rightLinear hn K D L e)

/-- For fixed actual endpoint states, the raw element certifies equality
of whole integral Hecke-module morphisms, rather than a single numerical readout. -/
theorem program_ext_raw {s t : State} (p q : Program hn s t)
    (h : p.raw hn K D L=q.raw hn K D L) :
    p.linear hn K D L=q.linear hn K D L :=
  ext_generator _ _ (program_rightLinear hn K D L p) (program_rightLinear hn K D L q) h

/-- The integral parabolic path interpretation also commutes with the
right Hecke action, before choosing any concrete graph. -/
theorem path_rightLinear {I J : Index n} (p : WebEvaluation.Path I J) :
    RightLinear (WebEvaluation.Path.linear K D L p) := by
  induction p with
  | nil =>
    simpa only [WebEvaluation.Path.linear] using id_rightLinear (symmetrizer K D I)
  | split p h ih =>
    simpa only [WebEvaluation.Path.linear,WebEvaluation.split] using
      comp_rightLinear ih (inclusion_rightLinear (L.inclusion _ _ h))
  | merge p h ih =>
    simpa only [WebEvaluation.Path.linear,WebEvaluation.merge] using
      comp_rightLinear ih (merge_rightLinear (Classical.choice (L.merge_exists _ _ h)))

end Guralnick.WebRightLinearity
