Require Import Coq.Lists.List.
Import ListNotations.
Set Implicit Arguments.

Require Import  ZArith.
Require Import Coq.ZArith.Zbool.
Open Scope Z_scope.

Inductive op : Type :=
| Add : op
| Sub : op
| Mul : op
| Div : op
.

Inductive expr : Type :=
| Val : Z -> expr
| App : op -> expr -> expr -> expr
.

Search Zle.
Definition valid (o : op) (x : Z) (y : Z) : bool :=
  match o with
  | Add => true
  | Sub =>  (Zgt_bool x y)
  | Mul => true
  | Div => Zeq_bool (x mod y) 0
  end.

Definition applyOp (o : op) (x : Z) (y : Z) : Z :=
  match o with
  | Add => x + y
  | Sub => x - y
  | Mul => x * y
  | Div => x / y
  end.

Fixpoint eval (e : expr) : list Z :=
  match e with
  | Val n => [n]
  | App op l r =>
    List.flat_map (fun x =>
      List.flat_map (fun y =>
                       if valid op x y then [applyOp op x y] else []
                    ) (eval r)
                  ) (eval l)
  end.

Fixpoint values (e : expr) : list Z :=
  match e with
  | Val n => [n]
  | App _ l r => values l ++ values r
  end.

Fixpoint tails {A:Type} (xs : list A) : list (list A) :=
  match xs with
  | [] => []
  | x::xs' => xs :: tails xs'
  end.

Fixpoint permutations {A:Type} (xs : list A) : list (list A) :=
  fix insert (x :A) (ys:list A) {ys} : list (list A) :=
    match ys with
    | [] => [[x]]
    | y::ys' => (x::ys) :: List.map (fun l => y::l) (insert x ys)
    end.
  in List.foldr (fun x a => List.flat_map (insert x) a) [[]] xs

Fixpoint subbags (xs : list A) : list (list A) :=
  List.flat_map permutations (tails xs).