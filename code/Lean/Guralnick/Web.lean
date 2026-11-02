import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-!
# The combinatorial annular web

This file records an actual directed, port-labelled graph, not merely a list of
edge thicknesses. A graph is assembled by binary splits and merges of open
edges. Integer winding on each edge records its signed crossing of the chosen
annular cut. The construction below is the six-map web in the manuscript,
with its multiple splits/merges resolved into trivalent vertices.

Scope: these are combinatorial statements. The graph, local ribbon orders
and integer winding record data of the drawn diagram; an annular embedding
and its equivalence under ambient isotopy are not formalized. There is no
interpretation in an affine Schur algebra here, and no claim that graph
equality is web-category equality or that this graph has a specified
canonical-basis expansion.
-/

namespace Guralnick.Web

/-- A cut specifies where the displayed cyclic list starts, in thin positions.
Ordinary boundaries have cut zero. The cyclic `J` boundary starts at `m+1`
(zero based), i.e. at position `m+2` in the manuscript. -/
structure Boundary where
  cut : Nat
  packets : List Nat
  deriving DecidableEq, Repr

def Boundary.mass (b : Boundary) : Nat := b.packets.sum

/-- Cyclic order of boundary packets, listed starting at the specified cut. -/
def Boundary.packetOrder (b : Boundary) : List Nat := List.range b.packets.length

/-- The zero-based first thin position of a boundary packet. Together with
`packetOrder`, this records the cut's position rather than forgetting it. -/
def Boundary.packetStart (b : Boundary) (i : Nat) : Nat :=
  (b.cut + (b.packets.take i).sum) % b.mass

inductive VertexKind where
  | split
  | merge
  deriving DecidableEq, Repr

/-- Port order matters. A split has input `[a+b]`, outputs `[a,b]`;
a merge has inputs `[a,b]`, output `[a+b]`. -/
structure Vertex where
  kind : VertexKind
  a : Nat
  b : Nat
  deriving DecidableEq, Repr

def Vertex.inputs (v : Vertex) : List Nat :=
  match v.kind with
  | .split => [v.a + v.b]
  | .merge => [v.a, v.b]

def Vertex.outputs (v : Vertex) : List Nat :=
  match v.kind with
  | .split => [v.a, v.b]
  | .merge => [v.a + v.b]

inductive LocalPort where
  | incoming (i : Nat)
  | outgoing (i : Nat)
  deriving DecidableEq, Repr

/-- Counterclockwise ribbon order at a trivalent vertex, starting with the
single leg. In the upward strip drawing, port 0 is the left branch and
port 1 the right branch. Cyclic rotations of these lists give the same
local ribbon order; no quotient by such rotations is used in this file. -/
def Vertex.ribbonOrder (v : Vertex) : List LocalPort :=
  match v.kind with
  | .split => [.incoming 0, .outgoing 1, .outgoing 0]
  | .merge => [.outgoing 0, .incoming 0, .incoming 1]

theorem Vertex.ribbonOrder_length (v : Vertex) : v.ribbonOrder.length = 3 := by
  cases v with
  | mk k a b => cases k <;> rfl

theorem Vertex.conserves (v : Vertex) : v.inputs.sum = v.outputs.sum := by
  cases v with
  | mk k a b => cases k <;> simp [Vertex.inputs, Vertex.outputs]

/-- At a vertex the port number is an output port for an edge source and an
input port for an edge target. Boundary indices are zero based. -/
inductive End where
  | input (i : Nat)
  | vertex (i port : Nat)
  | output (i : Nat)
  deriving DecidableEq, Repr

structure Edge where
  source : End
  target : End
  thickness : Nat
  winding : Int
  deriving DecidableEq, Repr

structure Graph where
  input : Boundary
  output : Boundary
  vertices : List Vertex
  edges : List Edge
  deriving DecidableEq, Repr

def Graph.sourcePorts (g : Graph) : List End :=
  (List.range g.input.packets.length).map End.input ++
  g.vertices.zipIdx.flatMap fun (v, i) =>
    (List.range v.outputs.length).map (End.vertex i)

def Graph.targetPorts (g : Graph) : List End :=
  g.vertices.zipIdx.flatMap (fun (v, i) =>
    (List.range v.inputs.length).map (End.vertex i)) ++
  (List.range g.output.packets.length).map End.output

def Graph.sourceLabel (g : Graph) : End → Option Nat
  | .input i => g.input.packets[i]?
  | .vertex i p => (g.vertices[i]?).bind fun v => v.outputs[p]?
  | .output _ => none

def Graph.targetLabel (g : Graph) : End → Option Nat
  | .input _ => none
  | .vertex i p => (g.vertices[i]?).bind fun v => v.inputs[p]?
  | .output i => g.output.packets[i]?

def Edge.ascending (e : Edge) : Bool :=
  match e.source, e.target with
  | .vertex i _, .vertex j _ => decide (i < j)
  | _, _ => true

/-- Every boundary/vertex port occurs exactly once, both endpoint labels agree
with the edge, every edge is positive, and internal edges go forward in the
vertex order. In particular, unused ports, duplicated wires and directed
cycles are excluded. -/
def Graph.WellFormed (g : Graph) : Prop :=
  (g.edges.map Edge.source).Perm g.sourcePorts ∧
  (g.edges.map Edge.target).Perm g.targetPorts ∧
  g.vertices.all (fun v => decide (0 < v.a ∧ 0 < v.b)) = true ∧
  g.edges.all (fun e =>
    decide (g.sourceLabel e.source = some e.thickness) &&
    decide (g.targetLabel e.target = some e.thickness) &&
    decide (0 < e.thickness) && e.ascending) = true

instance (g : Graph) : Decidable g.WellFormed := inferInstanceAs
  (Decidable ((g.edges.map Edge.source).Perm g.sourcePorts ∧
    (g.edges.map Edge.target).Perm g.targetPorts ∧
    g.vertices.all (fun v => decide (0 < v.a ∧ 0 < v.b)) = true ∧
    g.edges.all (fun e =>
      decide (g.sourceLabel e.source = some e.thickness) &&
      decide (g.targetLabel e.target = some e.thickness) &&
      decide (0 < e.thickness) && e.ascending) = true))

/-- Conservation of the declared input/output port labels. Well-formedness
additionally identifies these ports with the incident edges, used once. -/
def Graph.Conserves (g : Graph) : Prop :=
  ∀ v ∈ g.vertices, v.inputs.sum = v.outputs.sum

theorem Graph.conserves (g : Graph) : g.Conserves := by
  intro v _
  exact v.conserves

/-- Signed, thickness-weighted crossing number of the chosen seam. -/
def Graph.seamDegree (g : Graph) : Int :=
  (g.edges.map fun e => (e.thickness : Int) * e.winding).sum

def Graph.incomingMass (g : Graph) (i : Nat) : Nat :=
  ((g.edges.filter fun e => match e.target with
    | .vertex j _ => j == i
    | _ => false).map Edge.thickness).sum

def Graph.outgoingMass (g : Graph) (i : Nat) : Nat :=
  ((g.edges.filter fun e => match e.source with
    | .vertex j _ => j == i
    | _ => false).map Edge.thickness).sum

/-- The thin positions occupied by one packet, starting at a chosen cut.
The result uses the manuscript's one-based position labels. -/
def cyclicPositions (total cut size : Nat) : List Nat :=
  (List.range size).map fun i => (cut + i) % total + 1

/-- An open directed edge, before its target vertex or boundary is attached. -/
structure Wire where
  source : End
  thickness : Nat
  winding : Int := 0
  deriving DecidableEq, Repr

def Wire.wind (w : Wire) (n : Int) : Wire :=
  { w with winding := w.winding + n }

structure Builder where
  vertices : List Vertex := []
  edges : List Edge := []
  deriving DecidableEq, Repr

/-- Attach a split to an existing open edge. This is a raw constructor:
`Graph.WellFormed` checks that its input is exactly the sum of its outputs. -/
def Builder.split (s : Builder) (w : Wire) (a b : Nat) : Wire × Wire × Builder :=
  let i := s.vertices.length
  let v : Vertex := ⟨.split, a, b⟩
  let e : Edge := ⟨w.source, .vertex i 0, w.thickness, w.winding⟩
  (⟨.vertex i 0, a, 0⟩, ⟨.vertex i 1, b, 0⟩,
    ⟨s.vertices ++ [v], s.edges ++ [e]⟩)

/-- Attach an ordered merge. Both consumed edges retain their winding. -/
def Builder.merge (s : Builder) (left right : Wire) : Wire × Builder :=
  let i := s.vertices.length
  let v : Vertex := ⟨.merge, left.thickness, right.thickness⟩
  let e₀ : Edge := ⟨left.source, .vertex i 0, left.thickness, left.winding⟩
  let e₁ : Edge := ⟨right.source, .vertex i 1, right.thickness, right.winding⟩
  (⟨.vertex i 0, left.thickness + right.thickness, 0⟩,
    ⟨s.vertices ++ [v], s.edges ++ [e₀, e₁]⟩)

def Builder.finish (s : Builder) (input : Boundary) (outputs : List Wire)
    (cut : Nat := 0) : Graph :=
  { input := input
    output := ⟨cut, outputs.map Wire.thickness⟩
    vertices := s.vertices
    edges := s.edges ++ outputs.zipIdx.map (fun (w, i) =>
      ⟨w.source, .output i, w.thickness, w.winding⟩) }

structure Family where
  graph : Graph
  /-- Actual open wires after each of the six maps, together with the cut. -/
  frontiers : List (Nat × List Wire)
  /-- Cumulative number of trivalent vertices at these frontiers. -/
  stageEnds : List Nat
  deriving DecidableEq, Repr

def Family.boundaries (f : Family) : List Boundary :=
  f.frontiers.map fun (cut, wires) => ⟨cut, wires.map Wire.thickness⟩

/-- The manuscript's six operations, with `m ≥ 2` so the `m-1` edges are
positive. The two uses of `wind` implement the cyclic merge and split:
the right packet first crosses the cut positively; the corresponding output
packet returns across it negatively. The middle unit is not rotated.

Stage (c) resolves the cyclic `2m` packet into two `m` packets, then splits
these into `(m-1,1)` and `(1,m-1)`, in cyclic order. -/
def family (m : Nat) : Family :=
  let input : Wire := ⟨.input 0, 2 * m + 1, 0⟩
  let (left, rest, s₀) := Builder.split {} input m (m + 1)
  let (centre, right, s₁) := s₀.split rest 1 m
  let (cyclic, s₂) := s₁.merge (right.wind 1) left
  let (right₀, left₀, s₃) := s₂.split cyclic m m
  let (keepL, innerL, s₄) := s₃.split left₀ 1 (m - 1)
  let (innerR, keepR, s₅) := s₄.split (right₀.wind (-1)) (m - 1) 1
  let (middle₀, s₆) := s₅.merge innerL centre
  let (middle, s₇) := s₆.merge middle₀ innerR
  let (innerL', rest', s₈) := s₇.split middle (m - 1) m
  let (centre', innerR', s₉) := s₈.split rest' 1 (m - 1)
  let (left', s₁₀) := s₉.merge keepL innerL'
  let (right', s₁₁) := s₁₀.merge innerR' keepR
  { graph := s₁₁.finish ⟨0, [2 * m + 1]⟩ [left', centre', right']
    frontiers :=
      [(0, [input]),
       (0, [left, centre, right]),
       (m + 1, [cyclic, centre]),
       (0, [keepL, innerL, centre, innerR, keepR]),
       (0, [keepL, middle, keepR]),
       (0, [keepL, innerL', centre', innerR', keepR]),
       (0, [left', centre', right'])]
    stageEnds := [2, 3, 6, 8, 10, 12] }

theorem family_vertex_count (m : Nat) : (family m).graph.vertices.length = 12 := by
  rfl

theorem family_edge_count (m : Nat) : (family m).graph.edges.length = 20 := by
  rfl

theorem family_stage_ends (m : Nat) :
    (family m).stageEnds = [2, 3, 6, 8, 10, 12] := rfl

theorem family_input (m : Nat) :
    (family m).graph.input = ⟨0, [2 * m + 1]⟩ := rfl

theorem family_output (m : Nat) (hm : 2 ≤ m) :
    (family m).graph.output = ⟨0, [m, 1, m]⟩ := by
  have h₀ : 1 + (m - 1) = m := by omega
  have h₁ : m - 1 + 1 = m := by omega
  simp [family, Builder.split, Builder.merge, Builder.finish, Wire.wind, h₀, h₁]

theorem family_boundaries (m : Nat) (hm : 2 ≤ m) :
    (family m).boundaries =
      [⟨0, [2 * m + 1]⟩,
       ⟨0, [m, 1, m]⟩,
       ⟨m + 1, [2 * m, 1]⟩,
       ⟨0, [1, m - 1, 1, m - 1, 1]⟩,
       ⟨0, [1, 2 * m - 1, 1]⟩,
       ⟨0, [1, m - 1, 1, m - 1, 1]⟩,
       ⟨0, [m, 1, m]⟩] := by
  have h₀ : 1 + (m - 1) = m := by omega
  have h₁ : m - 1 + 1 = m := by omega
  have h₂ : m + (m - 1) = 2 * m - 1 := by omega
  simp [Family.boundaries, family, Builder.split, Builder.merge, Wire.wind,
    h₀, h₁, h₂, Nat.two_mul]

theorem family_boundary_mass (m : Nat) (hm : 2 ≤ m) :
    ∀ b ∈ (family m).boundaries, b.mass = 2 * m + 1 := by
  rw [family_boundaries m hm]
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h | h | h | h <;>
    subst b <;> simp [Boundary.mass] <;> omega

theorem family_wellFormed (m : Nat) (hm : 2 ≤ m) :
    (family m).graph.WellFormed := by
  unfold Graph.WellFormed
  constructor
  · dsimp [family, Builder.split, Builder.merge, Builder.finish, Wire.wind,
      Graph.sourcePorts, Vertex.outputs]
    simp only [List.flatMap_cons, List.flatMap_nil,
      List.length_cons, List.length_nil]
    decide
  constructor
  · dsimp [family, Builder.split, Builder.merge, Builder.finish, Wire.wind,
      Graph.targetPorts, Vertex.inputs]
    simp only [List.flatMap_cons, List.flatMap_nil,
      List.length_cons, List.length_nil]
    decide
  constructor
  · simp [family, Builder.split, Builder.merge, Builder.finish, Wire.wind]
    omega
  · simp [family, Builder.split, Builder.merge, Builder.finish, Wire.wind,
      Graph.sourceLabel, Graph.targetLabel, Vertex.inputs, Vertex.outputs,
      Edge.ascending]
    omega

theorem family_conserves (m : Nat) : (family m).graph.Conserves :=
  (family m).graph.conserves

theorem family_seam_degree (m : Nat) : (family m).graph.seamDegree = 0 := by
  simp [Graph.seamDegree, family, Builder.split, Builder.merge, Builder.finish,
    Wire.wind]
  omega

/-- Both directed seam crossings are retained. Zero total degree therefore
does not mean that the annular diagram has been replaced by a planar one. -/
theorem family_winding_list (m : Nat) :
    ((family m).graph.edges.map Edge.winding).filter (fun n => n != 0) = [1, -1] := by
  rfl

theorem family_incidence (m n : Nat) :
    ((family m).graph.edges.map fun e => (e.source, e.target, e.winding)) =
    ((family n).graph.edges.map fun e => (e.source, e.target, e.winding)) := by
  simp [family, Builder.split, Builder.merge, Builder.finish, Wire.wind]

/-- Conservation stated directly for the graph's edge list, rather than only
for the declared vertex labels. This is uniform in the edge thickness m. -/
theorem family_incident_conservation (m : Nat) (hm : 2 ≤ m)
    (i : Nat) (hi : i < 12) :
    (family m).graph.incomingMass i = (family m).graph.outgoingMass i := by
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
      i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Graph.incomingMass, Graph.outgoingMass, family, Builder.split,
      Builder.merge, Builder.finish, Wire.wind] <;> omega

end Guralnick.Web
