import Guralnick.WebEvaluation

/-!
# Binary resolution of the manuscript's six integral maps

This is a general map-composition statement, before any graph family or
KL coefficient is selected. It proves that the actual twelve trivalent
maps collapse to the six multi-splits/merges. Recut identities are handled
by the checked graph-trace evaluation, not postulated here.
-/
noncomputable section
namespace Guralnick.WebEvaluationCompression
open Hecke ParabolicWeb WebEvaluation

/-- The six intermediate binary cuts in a resolution of a six-map word. -/
structure Resolution {n : ℕ} (I₀ V J L K : Index n) where
  A : Index n
  B : Index n
  C : Index n
  D : Index n
  E : Index n
  F : Index n
  h₀A : A.val⊆I₀.val
  hAV : V.val⊆A.val
  hVJ : V.val⊆J.val
  hJB : B.val⊆J.val
  hBC : C.val⊆B.val
  hCL : L.val⊆C.val
  hLD : L.val⊆D.val
  hDK : D.val⊆K.val
  hKE : E.val⊆K.val
  hEL : L.val⊆E.val
  hLF : L.val⊆F.val
  hFV : F.val⊆V.val

namespace Resolution
variable {n : ℕ} {I₀ V J L K : Index n} (r : Resolution I₀ V J L K)

def finePath : WebEvaluation.Path I₀ V :=
  let a := (WebEvaluation.Path.nil I₀).split r.h₀A
  let v := a.split r.hAV
  let j := v.merge r.hVJ
  let b := j.split r.hJB
  let c := b.split r.hBC
  let l := c.split r.hCL
  let d := l.merge r.hLD
  let k := d.merge r.hDK
  let e := k.split r.hKE
  let l' := e.split r.hEL
  let f := l'.merge r.hLF
  f.merge r.hFV

def coarsePath : WebEvaluation.Path I₀ V :=
  ((((((WebEvaluation.Path.nil I₀).split (r.hAV.trans r.h₀A)).merge r.hVJ).split
    (r.hCL.trans (r.hBC.trans r.hJB))).merge (r.hLD.trans r.hDK)).split
      (r.hEL.trans r.hKE)).merge (r.hLF.trans r.hFV)

variable {c : WindowCoxeter n} (H : KLRealization c)
variable (longest : ∀ I : Index n, LongestData c I) (laws : Laws H longest)

/-- This follows from uniqueness of integral merges and composition of
actual inclusions, without dividing by a scalar or assuming a web relation. -/
theorem fine_linear_eq_coarse :
    Path.linear H longest laws r.finePath=Path.linear H longest laws r.coarsePath := by
  simp only [finePath,coarsePath,Path.linear,←LinearMap.comp_assoc,
    WebEvaluation.split_comp,WebEvaluation.merge_comp,LinearMap.comp_id]

/-- The same equality on the actual spherical generator. -/
theorem fine_raw_eq_coarse :
    Path.raw H longest laws r.finePath=Path.raw H longest laws r.coarsePath := by
  unfold Path.raw
  rw [fine_linear_eq_coarse]

end Resolution
end Guralnick.WebEvaluationCompression
