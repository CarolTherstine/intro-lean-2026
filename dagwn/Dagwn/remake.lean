--IS-A relationship
structure Edge where
  target_id : Nat
  relation_name : String

structure Vertex where
  id : Nat
  concept : String
  out_edges : List Edge

structure Graph where
  vertices : List Vertex

--================================================================
--                HELPER FUNCTIONS
--================================================================
def get_vertex (g : Graph) (id : Nat) :=
  g.vertices.find? (fun v => v.id == id)

def Graph.vertices' (g : Graph) : List Nat := g.vertices.map Vertex.id
def Vertex.out_edges' (x : Vertex) : List Nat := x.out_edges.map Edge.target_id

def reaches (g : Graph) (length x y : Nat) : Bool :=
  match length with
  | 0 => x == y
  | length + 1 =>
    x == y ||
    (match get_vertex g x with
      | none   => false
      | some v => v.out_edges.any (fun e => reaches g length e.target_id y))
termination_by length

inductive Reaches (g : Graph) : Nat → Nat → Prop where
  | basis : ∀ x y, x ∈ g.vertices → y ∈ g.vertices → y.id ∈ x.out_edges' → Reaches g x.id y.id
  | step : ∀ x y z,
      x ∈ g.vertices →
      y ∈ g.vertices →
      z ∈ g.vertices →
      z.id ∈ x.out_edges' →
      Reaches g z.id y.id →
      Reaches g x.id y.id

def G : Graph :=
  { vertices :=
    [ { id := 0, concept := "animal", out_edges :=
        [ { target_id := 1, relation_name := "is-a" }]}
    , { id := 1, concept := "dog", out_edges := [
        { target_id := 2, relation_name := "is-a" } ]}
    , { id := 2, concept := "cat", out_edges := [] } ] }

    example : Reaches G 0 2 := by
      apply Reaches.step G G.vertices[0] G.vertices[1]


def has_edge_to (edges : List Edge) (target : Nat) : Bool :=
  edges.any (fun e => e.target_id == target)

def has_edge_to_in_g (g : Graph) (x : Nat) : Bool :=
  g.vertices.any (fun v => v.out_edges.any (fun e => e.target_id == x))

def reaches_pos (g : Graph) (steps x y : Nat) : Bool :=
  match steps with
  | 0 => false
  | steps + 1 =>
    match get_vertex g x with
    | none   => false
    | some v => v.out_edges.any (fun e => reaches g steps e.target_id y)

--================================================================
--                SPECIFIC FUNCTIONS
--================================================================
--lower/child
--is x a parent to y
--is y an hyponym of x
def DirectHyponym (g : Graph) (x y : Nat) : Bool :=
  match get_vertex g x with
  | none   => false
  | some v => has_edge_to v.out_edges y

--is x a indirect hypernym of y
def IndirectHyponym (g : Graph) (x y : Nat) : Bool :=
  match get_vertex g x, get_vertex g y with
  | some _, some _ => reaches g (g.vertices.length + 1) x y
  | _, _           => false



--================================================================
--                THEOREM FUNCTIONS
--================================================================

def WellFormed (g : Graph) : Prop :=
  (∀ x ∈ g.vertices, get_vertex g x.id = some x) ∧
  (∀ v ∈ g.vertices, ∀ e ∈ v.out_edges, ∃ w ∈ g.vertices, w.id = e.target_id)

def Irreflexivity (g : Graph) : Prop :=
  ∀ x ∈ g.vertices, ¬ DirectHyponym g x.id x.id

inductive Transitivity (g : Graph) (x : Nat) : Nat → Prop where
  | step {cur : Nat} :
      x ≠ cur ∧
      reaches g (g.vertices.length + 1) x cur = true →
      (∀ nxt : Nat, (cur ≠ nxt ∧  DirectHyponym g cur nxt = true) → Transitivity g x nxt)

def Asymmetry (g  : Graph) : Prop :=
  ∀ x ∈ g.vertices, ∀ y ∈ g.vertices, (x ≠ y ∧ DirectHyponym g x.id y.id ) → ¬ IndirectHyponym g y.id x.id
