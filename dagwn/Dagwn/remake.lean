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
    refine ⟨?_, ?_, ?_⟩
    .
      intro x y hxy hyx
      exact h x (Reaches.trans hxy hyx)
    . intro x hx hedge
      exact h x (Reaches.basis x x hx hx hedge)
    .
      intro x y z hxy hyz
      exact Reaches.trans hxy hyz
  .
    unfold Acyclic Asymmetry Irreflexive transvt
    rintro ⟨hasym, -, -⟩ x hxx
    exact hasym x x hxx hxx

def G : Graph :=
  { vertices :=
    [ { id := 0, out_edges :=
        [1]}
    , { id := 1,out_edges := [
2]}
    , { id := 2, out_edges := [] } ] }


#check @Reaches.step G G.vertices[0] G.vertices[1] G.vertices[2]

example : Reaches G G.vertices[0] G.vertices[2] := by
  apply @Reaches.step G G.vertices[0] G.vertices[1] G.vertices[2]
  · decide
  · decide
  · decide
  · decide
  · apply @Reaches.basis G G.vertices[1] G.vertices[2]
    . decide
    . decide
    . decide
