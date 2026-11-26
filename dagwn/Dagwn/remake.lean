--IS-A relationship
structure Vertex where
  id : Nat
  out_edges : List Nat
deriving DecidableEq

structure Graph where
  vertices : List Vertex
deriving DecidableEq

--================================================================
--                HELPER FUNCTIONS
--================================================================
def get_vertex (g : Graph) (id : Nat) :=
  g.vertices.find? (fun v => v.id == id)

def Graph.vertices' (g : Graph) : List Nat := g.vertices.map Vertex.id
--def Vertex.out_edges' (x : Vertex) : List Nat := x.out_edges.map Edge.target_id

def reaches (g : Graph) (length x y : Nat) : Bool :=
  match length with
  | 0 => x == y
  | length + 1 =>
    x == y ||
    (match get_vertex g x with
      | none   => false
      | some v => v.out_edges.any (fun e => reaches g length e y))
termination_by length

inductive Reaches (g : Graph) : Vertex → Vertex → Prop where
  | basis : ∀ x y, x ∈ g.vertices → y ∈ g.vertices → y.id ∈ x.out_edges → Reaches g x y
  | step : ∀ x y z,
      x ∈ g.vertices →
      y ∈ g.vertices →
      z ∈ g.vertices →
      y.id ∈ x.out_edges →
      Reaches g y z →
      Reaches g x z


theorem reaches_inv (g : Graph) (x y : Vertex) :
    Reaches g x y → x ∈ g.vertices ∧ y ∈ g.vertices := by
  intro h; cases h with
  | basis _ _ hx hy => exact ⟨hx, hy⟩
  | step _ _ _ hx _ hy => exact ⟨hx, hy⟩

def Asymmetry (g  : Graph) : Prop :=
  ∀ x y : Vertex,
  Reaches g x y  → ¬ Reaches g y x

def transvt (g  : Graph) : Prop :=
  ∀ x y z: Vertex, Reaches g x y → Reaches g y z → Reaches g x z

def Irreflexive (g  : Graph) : Prop :=
  ∀ x : Vertex, x ∈ g.vertices →
  ¬ x.id ∈ x.out_edges

def Acyclic (g : Graph) : Prop :=
  ∀ x : Vertex, ¬ Reaches g x x

theorem Reaches.trans {g : Graph} {x y z : Vertex}
    (h1 : Reaches g x y) (h2 : Reaches g y z) : Reaches g x z := by
  revert h2
  induction h1 with
  | basis _ _ hx hy hedge =>
    intro h2
    exact Reaches.step _ _ _ hx hy (reaches_inv g _ _ h2).2 hedge h2
  | step _ w _ hx hw _ hedge _ ih =>
    intro h2
    exact Reaches.step _ _ _ hx hw (reaches_inv g _ _ h2).2 hedge (ih h2)

theorem acyclic_with_irrefl_trans_asym :
  ∀ g : Graph, Acyclic g ↔ Asymmetry g ∧ Irreflexive g ∧ transvt g :=by
  intro g
  constructor
  · unfold Acyclic Asymmetry Irreflexive transvt
    intro h
    constructor
    . intro x y hxy hyx
      have hdir : Reaches g x x := by
        apply @Reaches.step g x y x
        ·
          have X := reaches_inv g x y hxy
          exact (reaches_inv g x y hxy).left
        ·
          have Y := reaches_inv g x y hxy
          exact (reaches_inv g y x hyx).left
        ·
          have X := reaches_inv g x y hxy
          exact (reaches_inv g x y hxy).left
        · sorry
        .sorry
    · sorry
  · sorry

def G : Graph :=
  { vertices :=
    [ { id := 0, out_edges :=
        [1]}
    , { id := 1,out_edges := [
2]}
    , { id := 2, out_edges := [] } ] }


#check @Reaches.step G G.vertices[0] G.vertices[1] G.vertices[2]

example : Reaches G 0 2 := by
  apply @Reaches.step G G.vertices[0] G.vertices[1] G.vertices[2]
  · decide
  · decide
  · decide
  · decide
  · apply @Reaches.basis G G.vertices[1] G.vertices[2]
    . decide
    . decide
    . decide

def has_edge_to (edges : List Nat) (target : Nat) : Bool :=
  edges.any (fun e => e == target )

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
