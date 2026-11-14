--semantic lexical network - Wordnet
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

def reaches (g : Graph) (length x y : Nat) : Bool :=
  match length with
  | 0 => x == y
  | length + 1 =>
    x == y ||
    (match get_vertex g x with
     | none   => false
     | some v => v.out_edges.any (fun e => reaches g length e.target_id y))
termination_by length

def has_edge_to (edges : List Edge) (target : Nat) : Bool :=
  edges.any (fun e => e.target_id == target)

def has_edge_to_in_g (g : Graph) (x : Nat) : Bool :=
  g.vertices.any (fun v => v.out_edges.any (fun e => e.target_id == x))

--================================================================
--                SPECIFIC FUNCTIONS
--================================================================
--lower/child
--is x a parent to y (can be indirect)
def DirectHyponym (g : Graph) (x y : Nat) : Bool :=
  match get_vertex g x with
  | none   => false
  | some v => has_edge_to v.out_edges y

--upper/parent
--is x a child to y (can be indirect)
def DirectHypernym (g : Graph) (x y : Nat) : Bool :=
  DirectHyponym g y x

def IndirectHyponym (g : Graph) (x y : Nat) : Bool :=
  match get_vertex g x, get_vertex g y with
  | some _, some _ => reaches g (g.vertices.length + 1) x y
  | _, _           => false

def IndirectHypernym (g : Graph) (x y : Nat) : Bool :=
  IndirectHyponym g y x

--================================================================
--                THEOREM FUNCTIONS
--================================================================
--guarantee that for all vertices in g none is the hypernym to itself
-- therefore no vertices points to itself

--Theorem 1 : Irreflexivity
-- ∀ x (¬ (x → x))
def Irreflexivity_bool (g : Graph) : Bool
  := g.vertices.all (fun x => !DirectHypernym g x.id x.id)

--Theorem 2 : Transitivity
-- ∀ (x, y , z ) (x → y ∧ y → z) → x → z
def Transitivity_bool (g : Graph) : Bool :=
  g.vertices.all (fun x =>
    g.vertices.all (fun y =>
      g.vertices.all (fun z =>
        (DirectHypernym g x.id y.id && DirectHypernym g y.id z.id) -> IndirectHypernym g x.id z.id)
    ))

--Theorem 3 : Assymetry
--∀ (i, j) (i → j) → ¬ (j → i)
def Asymmetry_bool (g : Graph) : Bool :=
  g.vertices.all (fun x =>
    match get_vertex g x.id with
    | none => true
    | some v =>
      v.out_edges.all (fun y =>
        match get_vertex g y.target_id with
        | none => true
        | some _ => !IndirectHypernym g y.target_id x.id
      ))


--Theorem 4 : Unique Root
--Root(r)  :=  ∀ a ∈ S, r →* a
--∃! r ∈ S, Root(r)
def UniqueRoot_bool (g : Graph) (r : Nat) : Bool :=
  !has_edge_to_in_g g r &&
  g.vertices.all (fun v => IndirectHyponym g r v.id)

--exactly 1 unique
def HasOneUniqueRoot_bool (g : Graph) : Bool :=
  (g.vertices.filter (fun v => UniqueRoot_bool g v.id)).length == 1
--================================================================
--                WORDNET SPECIFIC
--================================================================
--specific wordnet graph
structure SynsetGraph where
  g : Graph
  irr: Irreflexivity_bool g :=by rfl
  ass: Asymmetry_bool g :=by rfl
  trsnt : Transitivity_bool g := by rfl
  universal_root: HasOneUniqueRoot_bool g :=by rfl


def cyclic_sanity_check : Graph :=
  { vertices :=
    [ { id := 0, concept := "A", out_edges := [{ target_id := 1, relation_name := "r" }] }
    , { id := 1, concept := "B", out_edges := [{ target_id := 0, relation_name := "r" }] } ] }

def dag_sanity_check : Graph :=
  { vertices :=
    [ { id := 0, concept := "A", out_edges := [{ target_id := 1, relation_name := "r" }] }
    , { id := 1, concept := "B", out_edges := [] } ] }

#eval Asymmetry_bool cyclic_sanity_check  -- false (0 → 1 and 1 → 0)
#eval Asymmetry_bool dag_sanity_check     -- true  (0 → 1 but 1 ⇏ 0)
