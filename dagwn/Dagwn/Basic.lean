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

--================================================================
--                SPECIFIC FUNCTIONS
--================================================================
--lower/child
--is x a parent to y (can be indirect)
def IsHyponym (g : Graph) (x y : Nat) : Bool :=
  match get_vertex g x, get_vertex g y with --if x and y id is in graph g
  | some _, some _ => reaches g (g.vertices.length + 1) x y --if not in the graph
  | _, _           => false

--upper/parent
--is x a child to y (can be indirect)
def IsHypernym (g : Graph) (x y : Nat) : Bool :=
  IsHyponym g y x

--================================================================
--                THEOREM FUNCTIONS
--================================================================
--guarantee that for all vertices in g none is the hypernym to itself
-- therefore no vertices points to itself
def Irreflexivity_bool (g : Graph) : Bool
  := g.vertices.all (fun x => !IsHypernym g x.id x.id)

def Asymmetry_bool (g : Graph) : Bool :=
  g.vertices.all (fun x =>
    match get_vertex g x.id with
    | none => true
    | some v =>
      v.out_edges.all (fun y =>
        match get_vertex g y.target_id with
        | none => true
        | some _ =>
          !(reaches g (g.vertices.length + 1) y.target_id x.id) -- y does NOT reach back to x
      ))

def Transitivity_bool (g : Graph) : Bool :=
  g.vertices.all (fun x =>
    match get_vertex g x.id with
    | none => true
    | some v =>
      v.out_edges.all (fun y =>
        match get_vertex g y.target_id with
        | none => true
        | some _ =>
          !(reaches g (g.vertices.length + 1) y.target_id x.id) -- y does NOT reach back to x
      ))

--================================================================
--                WORDNET SPECIFIC
--================================================================
--specific wordnet graph
structure SynsetGraph where
  g : Graph
  irr: Irreflexivity_bool g :=by rfl
  ass: Asymmetry_bool g :=by rfl
  trsnt : Transitivty_bool g := by rfl


theorem Transitivity : ∀ i j k : Nat , ∀ g : Graph , (IsHypernym g i j ∧ IsHypernym g j k → IsHypernym g i k) := by
  intro i j k g
  rfl
--Theorem 2 : Transitivity
-- ∀ (i, j , k ) (i → j ∧ j → k) → i → k

--==========================================================

theorem Assymetry : ∀ i j: Nat, ∀ g : Graph, IsHypernym g i j → IsHyponym g j i := by
  intro i j
  rfl





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
