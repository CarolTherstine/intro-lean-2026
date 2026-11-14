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

namespace graph

def get_vertex (g : Graph) (id : Nat) :=
  g.vertices.find? (fun v => v.id == id)

def has_edge_to (edges : List Edge) (target : Nat) : Bool :=
  edges.any (fun e => e.target_id == target)


def reaches (g : Graph) (length x y : Nat) : Bool :=
  match length with
  | 0 => x == y
  | length + 1 =>
    x == y ||
    (match get_vertex g x with
     | none   => false
     | some v => v.out_edges.any (fun e => reaches g length e.target_id y))
termination_by length

--lower/child
--is x a parent to y (can be indirect)
def IsHyponym (g : Graph) (x y : Nat) : Bool :=
  match get_vertex g x with --if x id is in graph g
  | none => false --if not in the graph
  | some v => reaches g (g.vertices.length+1) v.id y

--upper/parent
--is x a child to y (can be indirect)
def IsHypernym (g : Graph) (x y : Nat) : Bool :=
  IsHyponym g y x

--guarantee that for all vertices in g none is the hypernym to itself
-- therefore no vertices points to itself
def Irreflexivity_bool (g : Graph) : Bool
  := g.vertices.all (fun x => !IsHypernym g x.id x.id)

def Assymetry_bool (g : Graph) : Bool
  := g.vertices.all (fun x =>
    match get_vertex g x.id with --first we look up if x is in g
    | none => true --if not just continue, it doesnt invalidate
    | some v =>
      v.out_edges.all (fun y => --if y is a target id in out edges of some v that is x (ie y is a child to x)
        match get_vertex g y.target_id with
        | none => true --if not just continue
        | some w => !(has_edge_in_list w.out_edges x.id))) -- if some w that is y, if we dont have x in w out list (ie x is a child to w) then ok

def Transitivity_bool (g : Graph) : Bool
  :=

--specific wordnet graph
structure SynsetGraph where
  g : Graph
  irr: Irreflexivity_bool g :=by rfl
  ass: Assymetry_bool g :=by rfl
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
