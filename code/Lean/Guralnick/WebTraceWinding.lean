import Guralnick.WebTraceCore
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Winding conservation during ordered replay

The winding of already attached graph edges plus the winding of live wires
is tracked through every checked operation. The allowed cut changes have a
fixed potential: zero at the zero cut, and N-cut otherwise. Thus a replay
from cut zero back to cut zero cannot silently insert a whole annular turn.
This does not identify arbitrary coils with identity; those operations are
not part of the checked recut grammar.
-/
namespace Guralnick.WebTraceWinding
open Web WebTrace

def wireCharge (w : Wire) : ℤ := (w.thickness : ℤ)*w.winding
def edgeCharge (e : Edge) : ℤ := (e.thickness : ℤ)*e.winding

def charge (s : State) : ℤ :=
  (s.builder.edges.map edgeCharge).sum + (s.wires.map wireCharge).sum

def potential (s : State) : ℤ :=
  if s.cut=0 then 0 else ((s.mass-s.cut : Nat) : ℤ)

private theorem mass_drop (s : State) (i : Nat) :
    s.mass = ((s.wires.take i).map Wire.thickness).sum +
      ((s.wires.drop i).map Wire.thickness).sum := by
  unfold State.mass State.boundary Boundary.mass
  rw [←List.sum_append,←List.map_append,List.take_append_drop]

private theorem charge_drop (s : State) (i : Nat) :
    charge s = (s.builder.edges.map edgeCharge).sum +
      ((s.wires.take i).map wireCharge).sum +
      ((s.wires.drop i).map wireCharge).sum := by
  unfold charge
  rw [add_assoc]
  congr 1
  rw [←List.sum_append,←List.map_append,List.take_append_drop]

/-- The checked replay preserves total thickness, including recutting. -/
theorem step_mass {op : Op} {s t : State} (h : step op s=some t) : t.mass=s.mass := by
  cases op with
  | split i a b =>
    dsimp only [step] at h
    split at h
    · contradiction
    · rename_i w ws hw
      split at h
      · rename_i hp
        simp only [Option.some.injEq] at h
        subst t
        have hm:=mass_drop s i
        simp only [hw,List.map_cons,List.sum_cons] at hm
        simp [State.mass,State.boundary,Boundary.mass,Builder.split] at hm ⊢
        omega
      · contradiction
  | merge i =>
    dsimp only [step] at h
    split at h
    · rename_i l r ws hw
      split at h
      · simp only [Option.some.injEq] at h
        subst t
        have hm:=mass_drop s i
        simp only [hw,List.map_cons,List.sum_cons] at hm
        simp [State.mass,State.boundary,Boundary.mass,Builder.merge] at hm ⊢
        omega
      · contradiction
    · contradiction
  | rotateRight =>
    dsimp only [step] at h
    split at h
    · rename_i w ws hw
      split at h
      · simp only [Option.some.injEq] at h
        subst t
        have hm : s.mass=w.thickness+(ws.map Wire.thickness).sum := by
          unfold State.mass State.boundary Boundary.mass
          rw [←List.sum_reverse,←List.map_reverse,hw]
          simp
        simpa [State.mass,State.boundary,Boundary.mass,Wire.wind] using hm.symm
      · contradiction
    · contradiction
  | rotateLeft =>
    dsimp only [step] at h
    split at h
    · rename_i w ws hw
      split at h
      · simp only [Option.some.injEq] at h
        subst t
        simp [State.mass,State.boundary,Boundary.mass,Wire.wind,hw,Nat.add_comm]
      · contradiction
    · contradiction

/-- Total thickness is preserved by every successful finite trace. -/
theorem run_mass {ops : List Op} {s t : State} (h : run ops s=some t) : t.mass=s.mass := by
  induction ops generalizing s with
  | nil =>
    simp only [run,Option.some.injEq] at h
    subst t
    rfl
  | cons op ops ih =>
    simp only [run] at h
    cases hs : step op s with
    | none => simp [hs] at h
    | some u =>
      simp only [hs,Option.bind_some] at h
      exact (ih h).trans (step_mass hs)

/-- A local step changes winding exactly by the canonical cut potential. -/
theorem step_charge {op : Op} {s t : State} (h : step op s=some t) :
    charge t-potential t=charge s-potential s := by
  have hm:=step_mass h
  cases op with
  | split i a b =>
    dsimp only [step] at h
    split at h
    · contradiction
    · rename_i w ws hw
      split at h
      · simp only [Option.some.injEq] at h
        subst t
        have hc:=charge_drop s i
        simp only [hw,List.map_cons,List.sum_cons] at hc
        have hp : potential ⟨(s.builder.split w a b).2.2,
            s.wires.take i ++ [(s.builder.split w a b).1,
              (s.builder.split w a b).2.1] ++ ws, s.cut⟩ = potential s := by
          unfold potential
          rw [hm]
        rw [hp]
        simp [charge,Builder.split,edgeCharge,wireCharge] at *
        omega
      · contradiction
  | merge i =>
    dsimp only [step] at h
    split at h
    · rename_i l r ws hw
      split at h
      · simp only [Option.some.injEq] at h
        subst t
        have hc:=charge_drop s i
        simp only [hw,List.map_cons,List.sum_cons] at hc
        have hp : potential ⟨(s.builder.merge l r).2,
            s.wires.take i ++ [(s.builder.merge l r).1] ++ ws,
            s.cut⟩ = potential s := by
          unfold potential
          rw [hm]
        rw [hp]
        simp [charge,Builder.merge,edgeCharge,wireCharge] at *
        omega
      · contradiction
    · contradiction
  | rotateRight =>
    dsimp only [step] at h
    split at h
    · rename_i w ws hw
      split at h
      · rename_i hp
        simp only [Option.some.injEq] at h
        subst t
        have hc : charge s=(s.builder.edges.map edgeCharge).sum+
            wireCharge w+(ws.map wireCharge).sum := by
          have hr : (s.wires.map wireCharge).sum =
              wireCharge w+(ws.map wireCharge).sum := by
            rw [←List.sum_reverse,←List.map_reverse,hw]
            simp
          unfold charge
          rw [hr]
          ring
        have hcut : s.mass-w.thickness≠0 := by omega
        have hdiff : s.mass-(s.mass-w.thickness)=w.thickness := by omega
        simp only [potential,hm,hcut,if_false,hp.1,if_true,hdiff]
        simp [charge,Wire.wind,wireCharge] at hc ⊢
        nlinarith
      · contradiction
    · contradiction
  | rotateLeft =>
    dsimp only [step] at h
    split at h
    · rename_i w ws hw
      split at h
      · rename_i hp
        simp only [Option.some.injEq] at h
        subst t
        have hcut : s.cut≠0 := by omega
        have hdiff : s.mass-s.cut=w.thickness := by omega
        simp [potential,hcut,hdiff,charge,hw,Wire.wind,wireCharge]
        ring
      · contradiction
    · contradiction

/-- Winding conservation for every successful finite trace. -/
theorem run_charge {ops : List Op} {s t : State} (h : run ops s=some t) :
    charge t-potential t=charge s-potential s := by
  induction ops generalizing s with
  | nil =>
    simp only [run,Option.some.injEq] at h
    subst t
    rfl
  | cons op ops ih =>
    simp only [run] at h
    cases hs : step op s with
    | none => simp [hs] at h
    | some u =>
      simp only [hs,Option.bind_some] at h
      exact (ih h).trans (step_charge hs)

private theorem zipIdx_charge (ws : List Wire) (start : Nat) :
    ((ws.zipIdx start).map (fun wi => wireCharge wi.1)).sum =
      (ws.map wireCharge).sum := by
  induction ws generalizing start with
  | nil => simp
  | cons w ws ih => simp [List.zipIdx_cons,ih]

/-- Finishing attaches the live wires without changing their winding. -/
theorem finish_charge (s : State) (input : Boundary) :
    (s.finish input).seamDegree=charge s := by
  simp only [State.finish,Builder.finish,Graph.seamDegree,charge,
    List.map_append,List.sum_append,List.map_map,Function.comp_def]
  change (s.builder.edges.map edgeCharge).sum +
    ((s.wires.zipIdx).map (fun wi => wireCharge wi.1)).sum = _
  rw [zipIdx_charge]

/-- Any successful checked trace with zero input and output cuts has
zero signed thickness-weighted winding. Arbitrary winding loops are not
silently admitted as chart changes by the replay grammar. -/
theorem run_zero_cut_seam {ops : List Op} {input : Boundary} {s : State}
    (hi : input.cut=0) (hs : s.cut=0) (h : run ops (initial input)=some s) :
    (s.finish input).seamDegree=0 := by
  rw [finish_charge]
  have hc:=run_charge h
  simpa [potential,hs,initial,hi,charge,List.map_map,Function.comp_def,wireCharge] using hc

/-- Moving the sole packet would be a whole annular turn, not a recut.
The replay checker explicitly rejects it, also at zero thickness. -/
theorem single_packet_turn_rejected (n : Nat) :
    step .rotateRight (initial ⟨0,[n]⟩)=none := by
  simp [step,initial,State.mass,State.boundary,Boundary.mass]

/-- A second right recut cannot be applied immediately at a nonzero cut. -/
theorem consecutive_right_rejected {s t : State} (h : step .rotateRight s=some t) :
    step .rotateRight t=none := by
  dsimp only [step] at h
  split at h
  · rename_i w ws hw
    split at h
    · rename_i hp
      simp only [Option.some.injEq] at h
      subst t
      have hn : s.mass-w.thickness≠0 := by omega
      dsimp only [step]
      split <;> simp [hn]
    · contradiction
  · contradiction

end Guralnick.WebTraceWinding
