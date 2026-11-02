import Guralnick.WebTraceWinding

/-!
# Canonical recuts preserve absolute thin positions

A recut changes the chosen first packet in the cyclic list, not the global
thin-position residues occupied by each named live graph edge. The winding
on that edge is still changed explicitly by replay and is checked separately
by `WebTraceWinding`. These facts justify equality transport between two
charts of the same actual finite parabolic; they do not identify arbitrary
physical coils with identity.
-/
namespace Guralnick.WebRecutPositions
open Web WebTrace

def mass (ws : List Wire) : Nat := (ws.map Wire.thickness).sum

/-- The named live source port together with every absolute one-based thin
position occupied by its packet, read from the chosen cut. -/
def occupied (N cut : Nat) : List Wire → List (End × List Nat)
  | [] => []
  | w::ws => (w.source,cyclicPositions N cut w.thickness)::
      occupied N (cut+w.thickness) ws

@[simp] theorem mass_append (xs ys : List Wire) : mass (xs++ys)=mass xs+mass ys := by
  simp [mass]

@[simp] theorem mass_cons (w : Wire) (ws : List Wire) :
    mass (w::ws)=w.thickness+mass ws := rfl

@[simp] theorem mass_nil : mass []=0 := rfl

/-- Concatenation uses the actual mass of the first packet list. -/
theorem occupied_append (N cut : Nat) (xs ys : List Wire) :
    occupied N cut (xs++ys)=occupied N cut xs++occupied N (cut+mass xs) ys := by
  induction xs generalizing cut with
  | nil => simp [occupied]
  | cons w ws ih => simp [occupied,ih,Nat.add_assoc]

/-- Moving the lift by one period leaves every absolute residue unchanged. -/
theorem cyclicPositions_period (N cut size : Nat) :
    cyclicPositions N (cut+N) size=cyclicPositions N cut size := by
  simp [cyclicPositions,Nat.add_mod,Nat.add_assoc]

theorem occupied_period (N cut : Nat) (ws : List Wire) :
    occupied N (cut+N) ws=occupied N cut ws := by
  induction ws generalizing cut with
  | nil => rfl
  | cons w ws ih =>
    simp only [occupied,cyclicPositions_period]
    rw [show cut+N+w.thickness=(cut+w.thickness)+N by omega,ih]

/-- At the zero cut, the last packet occupies the interval immediately
after the before; this is calculated from its actual thicknesses. -/
theorem occupied_last (N : Nat) (before : List Wire) (w : Wire) :
    occupied N 0 (before++[w])=occupied N 0 before++
      [(w.source,cyclicPositions N (mass before) w.thickness)] := by
  simp [occupied_append,occupied]

/-- A positive last-to-first recut is exactly cyclic reordering of the
same named occupied packets. The winding update does not rename a port. -/
theorem right_recut (N : Nat) (before : List Wire) (w : Wire)
    (hm : mass before+w.thickness=N) :
    occupied N (N-w.thickness) (w.wind 1::before)=
      (w.source,cyclicPositions N (mass before) w.thickness)::occupied N 0 before := by
  have hcut : N-w.thickness=mass before := by omega
  simp only [occupied,Wire.wind,hcut,hm]
  have hp : occupied N N before=occupied N 0 before := by
    simpa only [Nat.zero_add] using occupied_period N 0 before
  rw [hp]

/-- At a nonzero canonical cut, the first packet ends at the zero cut. -/
theorem occupied_first (N cut : Nat) (w : Wire) (ws : List Wire)
    (hc : cut+w.thickness=N) :
    occupied N cut (w::ws)=
      (w.source,cyclicPositions N cut w.thickness)::occupied N 0 ws := by
  simp only [occupied,hc]
  have hp : occupied N N ws=occupied N 0 ws := by
    simpa only [Nat.zero_add] using occupied_period N 0 ws
  rw [hp]

/-- Returning the first packet to the end preserves its actual residue
interval and that of every packet it passes in the displayed list. -/
theorem left_recut (N cut : Nat) (w : Wire) (ws : List Wire)
    (hm : mass ws=cut) :
    occupied N 0 (ws++[w.wind (-1)])=occupied N 0 ws++
      [(w.source,cyclicPositions N cut w.thickness)] := by
  simp [occupied_last,hm,Wire.wind]

/-- Every successful right recut preserves the named occupied residue
packets. This statement applies to actual replay states and uses total N. -/
theorem step_right_positions {N : Nat} {s t : State} (hm : s.mass=N)
    (h : step .rotateRight s=some t) :
    (occupied N t.cut t.wires).Perm (occupied N s.cut s.wires) := by
  dsimp only [step] at h
  split at h
  · rename_i w ws hw
    split at h
    · rename_i hp
      simp only [Option.some.injEq] at h
      subst t
      have hws : s.wires=ws.reverse++[w] := by
        have hh:=congrArg List.reverse hw
        simpa using hh
      have hmass : mass ws.reverse+w.thickness=N := by
        simpa [State.mass,State.boundary,Boundary.mass,hws,mass] using hm
      change (occupied N (s.mass-w.thickness) (w.wind 1::ws.reverse)).Perm _
      rw [hm,right_recut N ws.reverse w hmass,hp.1,hws,occupied_last]
      exact List.perm_append_comm (l₁ := [(w.source,cyclicPositions N (mass ws.reverse) w.thickness)])
        (l₂ := occupied N 0 ws.reverse)
    · contradiction
  · contradiction

/-- Every successful inverse recut preserves those same actual packets. -/
theorem step_left_positions {N : Nat} {s t : State} (hm : s.mass=N)
    (h : step .rotateLeft s=some t) :
    (occupied N t.cut t.wires).Perm (occupied N s.cut s.wires) := by
  dsimp only [step] at h
  split at h
  · rename_i w ws hw
    split at h
    · rename_i hp
      simp only [Option.some.injEq] at h
      subst t
      have hc : s.cut+w.thickness=N := hp.2.2.trans hm
      have hmass : mass ws=s.cut := by
        have hsum : w.thickness+mass ws=N := by
          simpa [State.mass,State.boundary,Boundary.mass,hw,mass] using hm
        omega
      change (occupied N 0 (ws++[w.wind (-1)])).Perm _
      rw [left_recut N s.cut w ws hmass,hw,occupied_first N s.cut w ws hc]
      exact List.perm_append_comm (l₁ := occupied N 0 ws)
        (l₂ := [(w.source,cyclicPositions N s.cut w.thickness)])
    · contradiction
  · contradiction

end Guralnick.WebRecutPositions
