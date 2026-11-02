import Guralnick.Web
import Mathlib.Tactic.FinCases

/-!
# Ordered, winding-sensitive replay of the concrete annular web

A trace acts on the ordered list of actual live graph ports. Splits and
merges consume those ports and create trivalent vertices; they do not merely
change a list of boundary thicknesses. The two recut operations retain the
crossing number on the moved edge. They are deliberately restricted to
canonical changes between the zero cut and one packet boundary: arbitrary
rotations and full annular turns are not silently identified with identity.
-/
namespace Guralnick.WebTrace
open Web

structure State where
  builder : Builder
  wires : List Wire
  cut : Nat
  deriving DecidableEq, Repr

def State.boundary (s : State) : Boundary := ⟨s.cut,s.wires.map Wire.thickness⟩
def State.mass (s : State) : Nat := s.boundary.mass
def State.frontier (s : State) : Nat × List Wire := (s.cut,s.wires)
def State.finish (s : State) (input : Boundary) : Graph :=
  s.builder.finish input s.wires s.cut

def initial (input : Boundary) : State :=
  ⟨{},input.packets.zipIdx.map (fun (a,i) => ⟨.input i,a,0⟩),input.cut⟩

inductive Op where
  | split (index a b : Nat)
  | merge (index : Nat)
  /-- Recut from the zero cut by moving the last packet to the front.
  This is not a freely iterable annular rotation. -/
  | rotateRight
  /-- Return from the canonical nonzero cut by moving its first packet
  to the end. Its thin positions must end exactly at the zero cut. -/
  | rotateLeft
  deriving DecidableEq, Repr

/-- A checked local operation. Order, incident ports, positive thickness,
local vertex type, and the directed seam crossing are all part of replay. -/
def step (op : Op) (s : State) : Option State :=
  match op with
  | .split i a b =>
    match s.wires.drop i with
    | [] => none
    | w::ws =>
      if 0<a ∧ 0<b ∧ w.thickness=a+b then
        let (l,r,builder) := s.builder.split w a b
        some ⟨builder,s.wires.take i ++ [l,r] ++ ws,s.cut⟩
      else none
  | .merge i =>
    match s.wires.drop i with
    | l::r::ws =>
      if 0<l.thickness ∧ 0<r.thickness then
        let (w,builder) := s.builder.merge l r
        some ⟨builder,s.wires.take i ++ [w] ++ ws,s.cut⟩
      else none
    | _ => none
  | .rotateRight =>
    match s.wires.reverse with
    | w::ws =>
      if s.cut=0 ∧ 0<w.thickness ∧ w.thickness<s.mass then
        some ⟨s.builder,w.wind 1 :: ws.reverse,s.mass-w.thickness⟩
      else none
    | [] => none
  | .rotateLeft =>
    match s.wires with
    | w::ws =>
      if 0<s.cut ∧ 0<w.thickness ∧ s.cut+w.thickness=s.mass then
        some ⟨s.builder,ws ++ [w.wind (-1)],0⟩
      else none
    | [] => none

def run : List Op → State → Option State
  | [],s => some s
  | op::ops,s => (step op s).bind (run ops)

/-- Graph evaluation here means replay into the combinatorial graph;
its subsequent integral Schur interpretation is a separate construction. -/
def graph (input : Boundary) (ops : List Op) : Option Graph :=
  (run ops (initial input)).map (fun s => s.finish input)

def familyInput (m : Nat) : Boundary := ⟨0,[2*m+1]⟩

/-- The literal trivalent resolutions of the six maps, with the two
canonical changes of cut written out as genuine operations. -/
def familyTrace (m : Nat) : List Op :=
  [.split 0 m (m+1), .split 1 1 m,
   .rotateRight, .merge 0,
   .split 0 m m, .split 1 1 (m-1), .rotateLeft, .split 3 (m-1) 1,
   .merge 1, .merge 1,
   .split 1 (m-1) m, .split 2 1 (m-1),
   .merge 0, .merge 2]

def checkpoint (stage : Fin 7) : Nat := [0,2,4,8,10,12,14].getD stage.val 0

def runPrefix (m : Nat) (count : Nat) : Option State :=
  run ((familyTrace m).take count) (initial (familyInput m))

end Guralnick.WebTrace
