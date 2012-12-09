(* author: Dimitur Krustev *)
(* (re)started: 20100228-0307; 0421; 0508 *)

(* * * Introduction - in main TeX file *)

(** While the resulting supercompiler is too limited to be practically
useful, it can still achieve interesting results on select small examples 
(Sect. %\ref{subsec:sscp}%).
To give a glimpse of the separation of concerns achieved, here is a small
example of a normalization ([normConv]) of a simple expression,
contrasted with normalization plus positive information propagation ([norm]): 
<<
Eval compute in (let e := (IfNil Hd (Nil # Nil) (IfNil Hd Nil Tl)) 
  in (ntrm2trm (normConv e), ntrm2trm (norm e))).
=(IfNil Hd (Nil # Nil) (IfNil Hd Nil Tl), IfNil Hd (Nil # Nil) Tl)
>>
Notice the removal of the redundant test in the second expression.
*)

(** ** Notation
The text of this article is produced from a literate Coq script using the coqdoc
tool %\cite{CoqRefMan}%. All data type and function definitions, as well as
the statements of all lemmas/theorems, are given directly in Coq syntax.
We use almost none of the more advanced or specific 
features of this proof assistant, so while our readers should be 
familiar with functional programming and first-order logic, 
they do not need prior experience with Coq. Coq contains a total
functional programming sublanguage, similar in many respects to
languages like Haskell and OCaml (modulo totality requirements). 
It permits well-founded 
inductive%\footnote{Coinductive definitions are also possible, 
but we do not use them here}%
data type definitions (keyword [Inductive ...]), 
non-recursive global definitions ([Definition]),
structurally recursive global ([Fixpoint]) and local 
([fix]) definitions, pattern matching ([match ... with | ... => ... | ... end]),
lambda functions ([fun ... => ...]). 
Coq also embeds (a form of) intuitionistic logic%\footnote{Classical 
reasoning is also possible in Coq, but not required here}%, 
with the usual logical quantifiers and connectives ([forall], [exists], [->],
[False], [True], [~], [/\], [\/], [<->], [=]). 
Type information is specified as [(x: T)] for an object [x] having a type [T].
Computable types usually have sort [Set], while logical propositions 
live in sort [Prop]. There is a computable type [bool: Set] with a 
number of operations on it, which should not be confused with the
non-executable logical propositions and connectives living in [Prop].
We use other standard library types -- natural numbers
([nat] with constructors [O] and [S], and standard arithmetic operations),
and lists ([list X] with constructors [nil] and [::], and
standard list operations like [length] and [++] (append)).

We believe, that the formulation of definitions and lemma statements 
is more valuable in understanding this work than the detailed proofs themselves. 
Proofs can be quite lengthy and are usually expressed using a special 
tactic language -- which can be difficult to follow outside of Coq. The 
complete proofs can always be checked inside the original Coq source.  
Therefore, we have omitted them here and only 
give brief informal hints for some of the more complicated ones. 
Most of the lengthier proofs are broken up into 
a series of lemmas, each one building on the previous ones, and 
culminating in a final theorem with a typically trivial proof. We do 
give the statements of all such lemmas, not only the main theorems.  
Furthermore, proofs of individual lemmas usually proceed straightforwardly by 
induction, and can be automated to a great extent using suitable 
heuristics for automatic proof search %\cite{AChlipalaBookCPDT}%. 
*)

(* begin hide *)

Require Import List.

(* ***** *)

(* Simplified versions of Adam Chlipala'a automation tactics *)

(* Require Import Eqdep. *)

Require Omega.

Ltac miniSimplHyp :=
  match goal with
    | [ H : ex _ |- _ ] => destruct H

    | [ H : ?F ?X = ?F ?Y |- ?G ] =>
      (assert (X = Y); [ assumption | fail 1 ])
      || (injection H;
        match goal with
          | [ |- X = Y -> G ] =>
            try clear H; intros; try subst
        end)
    | [ H : ?F ?X ?U = ?F ?Y ?V |- ?G ] =>
      (assert (X = Y); [ assumption
        | assert (U = V); [ assumption | fail 1 ] ])
      || (injection H;
        match goal with
          | [ |- U = V -> X = Y -> G ] =>
            try clear H; intros; try subst
        end)
(*
    | [ H : existT _ ?T _ = existT _ ?T _ |- _ ] => generalize (inj_pair2 _ _ _ _ _ H); clear H
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => inversion H; clear H
*)
    | [ H : Some _ = Some _ |- _ ] => injection H; clear H
  end.

Hint Rewrite app_ass : miniCrushDb.

Ltac miniCrush :=
  let sintuition := simpl in *; intuition; try subst; 
        repeat (miniSimplHyp; intuition; try subst); try congruence in
    let rewriter := autorewrite with miniCrushDb in *;
      repeat (match goal with
                | [ H : _ |- _ ] => (rewrite H; [])
                  || (rewrite H; [ | solve [ miniCrush ] ])
                    || (rewrite H; [ | solve [ miniCrush ] 
                                     | solve [ miniCrush ] ])
              end; autorewrite with miniCrushDb in *)
    in (sintuition; rewriter;
        sintuition; try omega; try (elimtype False; omega)).

(* ***** *)

(* end hide *)

(** * Simple Expression Language %\label{sec:Trm}%
We start with an extremely simple domain of values - binary trees (or, equivalently,
Lisp-like S-expressions) with a single atom, [VNil]. As some of our built-in functions
will be partial, we also include a second dedicated atom, [VBottom], used to make
all built-in functions total.
*)

Inductive Val: Set :=
  | VNil: Val | VCons: Val -> Val -> Val | VBottom: Val.

(** The use of an untyped language is motivated by a hope for greater 
overall simplicity, although a move to a typed setting would certainly bring some
benefits. Notice that the domain is lifted, as [VCons] is not strict w.r.t. 
[VBottom]: [VCons VBottom VBottom <> VBottom].
*)

(** The expressions of our simple language are built of primitives for constructing
([Nil], [Cons]) and deconstructing ([Sel]) binary trees, 
function composition and identity ([Cmp], [Id]), and conditional expressions testing 
for null values. It is convenient to have also a bottom-building primitive, [Bottom],
but there is no way of testing for bottom:
*)

Inductive Selector: Set := | HD | TL.

Inductive Trm: Set :=
  | Nil: Trm | Cons: Trm -> Trm -> Trm | Sel: Selector -> Trm
  | Id: Trm | Cmp: Trm -> Trm -> Trm
  | IfNil: Trm -> Trm -> Trm -> Trm | Bottom.

(** We can use Coq's [Notation] mechanism to add a small amount of
syntax sugar (note that lower levels correspond to higher precedence). *)

Infix "$" := Cmp (at level 60, right associativity).
Notation Hd := (Sel HD). Notation Tl := (Sel TL).
Infix "#" := Cons (at level 62, right associativity).

(** A few things are notable in the choice of language. It is variable-free, all 
expressions denoting functions of type [Val -> Val]. It is the presence of pair
constructor and selectors, as well as function composition, as primitives, that
gives this language the ability to encode substitutions and to do away with variables.
As the language is not Turing-complete, it is straightforward to give its semantics
as a total function, [evalT]:
*)

Definition evalSel (sel: Selector) (v: Val) : Val := 
  match v with
  | VCons v1 v2 => match sel with | HD => v1 | TL => v2 end
  | _ => VBottom
  end.

Definition evalSels (sels: list Selector) (v: Val) : Val := 
  fold_left (fun v sel => evalSel sel v) sels v.

Fixpoint evalT (t: Trm) (v: Val) {struct t} : Val :=
  match t with
  | Nil => VNil
  | Cons t1 t2 => VCons (evalT t1 v) (evalT t2 v)
  | Sel sel => evalSel sel v
  | Id => v
  | Cmp t1 t2 => evalT t1 (evalT t2 v)
  | IfNil t1 t2 t3 => match evalT t1 v with
    | VNil => evalT t2 v | VCons _ _ => evalT t3 v | VBottom => VBottom
    end
  | Bottom => VBottom
  end.

(** ** Normalization of Simple Expressions %\label{subsec:normConv}%

The first step in our series of transformations will be to perform some standard
normalizing simplifications to expressions. As the resulting expressions
will always have a specific shape, we can define a special type for normal-form
expressions: 
*)

Inductive NTrm: Set :=
  | NNil: NTrm | NCons: NTrm -> NTrm -> NTrm 
  | NSelCmp: list Selector -> NTrm
  | NIfNil: list Selector -> NTrm -> NTrm -> NTrm
  | NBottom: (*Trm ->*) NTrm.

(** The important difference is, that in normal forms function composition can 
only be applied to pair selectors, and that tests in conditional expressions are
only of this special form of selector compositions. Notice that the selectors
appear in reverse order in lists, and such lists of selectors can be directly 
interpreted as positions in the binary trees of values. Of course, normal forms
can be injected back into the set of full-blown expressions:
*)

Definition sels2trm (sels: list Selector): Trm := fold_left (fun t sel => 
  match t with | Id => Sel sel | _ => Cmp (Sel sel) t end) sels Id.

Fixpoint ntrm2trm (nt: NTrm) {struct nt} :Trm :=
  match nt with
  | NNil => Nil
  | NCons nt1 nt2 => Cons (ntrm2trm nt1) (ntrm2trm nt2)
  | NSelCmp sels => sels2trm sels
  | NIfNil sels nt1 nt2 => IfNil (sels2trm sels) (ntrm2trm nt1) (ntrm2trm nt2)
  | NBottom => Bottom 
  end.

(** Using this injection, we can define a specialized evaluation function for
normal terms by re-using the main evaluation function. *)

Definition evalNT (nt: NTrm) (v: Val) : Val := evalT (ntrm2trm nt) v.

(** Next we establish some basic properties involving [evalSels], that will 
be useful in subsequent proofs. *)

(* * %\begin{small}% *)
Lemma evalT_sels2trm: forall sels: list Selector, forall v: Val, 
  evalT (sels2trm sels) v = evalSels sels v.
Proof.
(* begin hide *)
  intro sels.
  replace (sels) with (rev (rev sels)) by (apply rev_involutive).
  set (rsels := rev sels).
  unfold sels2trm. unfold evalSels.
  rewrite <- fold_left_rev_right.
  intro v.
  rewrite <- fold_left_rev_right.
  rewrite rev_involutive.
  generalize dependent v.
  induction rsels as [|rsel rsels']; try reflexivity.
  (* :: *) intro v.
    simpl.
    match goal with [|- context[match ?X with
      | Nil => _ | Cons _ _ => _ | Sel _ => _ | Id => _ | Cmp _ _ => _
      | IfNil _ _  _ => _ | Bottom => _ end]] => destruct X
      as [|? ?|?| |? ?|? ? ?|] _eqn: Heq end;
    miniCrush;
    rewrite <- IHrsels'; miniCrush.
(* end hide *)
Qed.
Hint Rewrite evalT_sels2trm : miniCrushDb.

Lemma evalSelsVBottom: forall sels: list Selector, evalSels sels VBottom = VBottom.
Proof.
(* begin hide *)
  induction sels.
    reflexivity.
    simpl. rewrite IHsels. reflexivity.
(* end hide *)
Qed.

Lemma evalSelsAppend: forall sels1 sels2: list Selector, forall v: Val,
  evalSels (sels1 ++ sels2) v = evalSels sels2 (evalSels sels1 v).
Proof.
(* begin hide *)
  unfold evalSels. apply fold_left_app.
(* end hide *)
Qed.
(* * %\end{small}% *)

(** The main normalization function, [normConv], uses a number of auxiliary 
operations on normal-form expressions, dealing mostly with special cases
of function composition. We list along the way some lemmas establishing
characteristic properties of the functions defined. The simplest cases
cover composition of a selector or a list of selectors with an expression.*)

Fixpoint normSelNCmp (sel: Selector) (nt: NTrm) {struct nt}: NTrm :=
  match nt with
  | NNil => NBottom
  | NCons nt1 nt2 => match sel with | HD => nt1 | TL => nt2 end
  | NSelCmp sels => NSelCmp (sels ++ (sel::nil))
  | NIfNil sels nt1 nt2 => NIfNil sels
      (normSelNCmp sel nt1) (normSelNCmp sel nt2)
  | NBottom => NBottom
  end.

(* * %\begin{small}% *)
Lemma normSelNCmpPreservesEval: forall (sel: Selector) (nt: NTrm) (v: Val),
  evalNT (normSelNCmp sel nt) v = evalSel sel (evalNT nt v).
Proof.
(* begin hide *)
  unfold evalNT.
  induction nt as [ | nt1 IHnt1 nt2 IHnt2 |
    sels | sels nt1 IHnt1 nt2 IHnt2 | ];
    try reflexivity.
  (* nt => NCons nt1 nt2 *) simpl. destruct sel; reflexivity.
  (* nt => NSelCmp sels *) simpl. intro v. 
    rewrite evalT_sels2trm. rewrite evalT_sels2trm.
    rewrite evalSelsAppend. reflexivity.
  (* nt => NIfNil sels nt1 nt2 *) simpl. intro v. 
    rewrite evalT_sels2trm. 
    rewrite IHnt1. rewrite IHnt2.
    destruct (evalSels sels v); reflexivity.
(* end hide *)
Qed.
(* * %\end{small}% *)


Definition normSelsNCmp (sels: list Selector) (nt: NTrm) : NTrm := 
  fold_left (fun nt sel => normSelNCmp sel nt) sels nt.

(* * %\begin{small}% *)
Lemma normSelsNCmpPreservesEvalT: forall sels: list Selector, forall nt: NTrm,
  forall v: Val, evalT (ntrm2trm (normSelsNCmp sels nt)) v 
  = evalSels sels (evalT (ntrm2trm nt) v).
Proof.
(* begin hide *)
  induction sels as [|sel sels']; try reflexivity.
  (* :: *)
    simpl. intros nt v. rewrite IHsels'.
    fold (evalNT (normSelNCmp sel nt) v).
    rewrite normSelNCmpPreservesEval. reflexivity.
(* end hide *)
Qed.
Hint Rewrite normSelsNCmpPreservesEvalT : miniCrushDb.

Lemma normSelsNCmpPreservesEval: forall sels: list Selector, forall nt: NTrm, forall v: Val,
  evalNT (normSelsNCmp sels nt) v = evalSels sels (evalNT nt v).
Proof.
(* begin hide *)
  unfold evalNT. apply normSelsNCmpPreservesEvalT.
(* end hide *)
Qed.

Lemma normSelsNCmp_NSelCmp: forall (sels1 sels2: list Selector),
  normSelsNCmp sels1 (NSelCmp sels2) = NSelCmp (sels2 ++ sels1).
Proof.
(* begin hide *)
  Hint Rewrite <- app_nil_end: miniCrushDb.
  induction sels1; miniCrush.
(* end hide *)
Qed.
(* * %\end{small}% *)

(** We also consider composition of selectors to the right of a normal-form
expression [nt]. *)

Fixpoint normNCmpSels (nt: NTrm) (sels: list Selector) {struct nt} 
  : NTrm := match nt with
  | NNil => NNil
  | NCons nt1 nt2 => 
      NCons (normNCmpSels nt1 sels) (normNCmpSels nt2 sels)
  | NSelCmp sels2 => NSelCmp (sels ++ sels2)
  | NIfNil sels2 nt1 nt2 => NIfNil (sels ++ sels2)
      (normNCmpSels nt1 sels) (normNCmpSels nt2 sels)
  | NBottom => NBottom
  end.

(* * %\begin{small}% *)
Lemma normNCmpSelsPreservesEval: forall sels: list Selector, forall nt: NTrm, forall v: Val,
  evalNT (normNCmpSels nt sels) v = evalNT nt (evalSels sels v).
Proof.
(* begin hide *)
  unfold evalNT.
  induction nt as [ | nt1 IHnt1 nt2 IHnt2 |
    sels1 | sels1 nt1 IHnt1 nt2 IHnt2 | ];
    try reflexivity.
  (* nt => NCons nt1 nt2 *) simpl. intro v. 
    rewrite IHnt1. rewrite IHnt2. reflexivity.
  (* nt => NSelCmp sels1 *) simpl. intro v.
    rewrite evalT_sels2trm. rewrite evalT_sels2trm.
    rewrite evalSelsAppend.
    reflexivity.
  (* nt => NIfNil sels1 nt1 nt2 *) simpl. intro v.
    rewrite evalT_sels2trm. rewrite evalT_sels2trm.
    rewrite IHnt1. rewrite IHnt2. 
    rewrite evalSelsAppend. reflexivity.
(* end hide *)
Qed.

Lemma normNCmpSels_app: forall (sels1 sels2: list Selector) (nt: NTrm),
  normNCmpSels nt (sels1 ++ sels2) 
  = normNCmpSels (normNCmpSels nt sels2) sels1.
Proof.
(* begin hide *)
  induction nt; miniCrush.
(* end hide *)
Qed.
(* * %\end{small}% *)

(** Next, we deal with building conditional expressions in normal form. If the normal
form of the condition is a value-constructing primitive, we can statically reduce the
whole if-expression. The other interesting case is when the condition is itself another
if-expression -- in this case we switch the order of the tests and duplicate the
original outer [NIfNil] inside the branches of the new outer [NIfNil].
*)

Fixpoint normNIf (nt1 nt2 nt3: NTrm) {struct nt1} : NTrm :=
  match nt1 with
  | NNil => nt2
  | NCons _ _ => nt3
  | NSelCmp sels => NIfNil sels nt2 nt3
  | NIfNil sels nt1_1 nt1_2 => NIfNil sels
      (normNIf nt1_1 nt2 nt3) (normNIf nt1_2 nt2 nt3)
  | NBottom => NBottom
  end.

(* * %\begin{small}% *)
Lemma normNIfPreservesEvalT: forall nt1 nt2 nt3: NTrm, forall v: Val,
  evalT (ntrm2trm (normNIf nt1 nt2 nt3)) v
  = match evalT (ntrm2trm nt1) v with
    | VNil => evalT (ntrm2trm nt2) v
    | VCons _ _ => evalT (ntrm2trm nt3) v
    | VBottom => VBottom
    end.
Proof.
(* begin hide *)
  induction nt1 as [ | nt1_1 IHnt1_1 nt1_2 IHnt1_2 |
    sels1 | sels1 nt1_1 IHnt1_1 nt1_2 IHnt1_2 | ];
    try reflexivity.
  (* nt1 => NIfNil sels1 nt1_1 nt1_2 *) simpl.
    intros nt2 nt3 v. rewrite IHnt1_1. rewrite IHnt1_2.
    rewrite evalT_sels2trm.
    destruct (evalSels sels1 v); reflexivity.
(* end hide *)
Qed.

Lemma normNIfPreservesEval: forall nt1 nt2 nt3: NTrm, forall v: Val,
  evalNT (normNIf nt1 nt2 nt3) v = match evalNT nt1 v with
    | VNil => evalNT nt2 v
    | VCons _ _ => evalNT nt3 v
    | VBottom => VBottom
    end.
Proof.
(* begin hide *)
  unfold evalNT. apply normNIfPreservesEvalT.
(* end hide *)
Qed.
(* * %\end{small}% *)

(** The sequence of operations on normal-form expressions culminates in a 
function [normNCmp], which permits to form the composition of two normal-form 
expressions without having function composition as primitive. The most
interesting cases here involve the composition of [NIfNil] and
[NSelCmp]/[NIfNil]: 
*)

Definition normNCmp : NTrm -> NTrm -> NTrm :=
  fix normNCmp_nt1 (nt1: NTrm): NTrm -> NTrm := 
  fix normNCmp_nt2 (nt2: NTrm): NTrm := 
  match nt1 with
  | NNil => NNil
  | NCons nt1_1 nt1_2 => 
      NCons (normNCmp_nt1 nt1_1 nt2) (normNCmp_nt1 nt1_2 nt2)
  | NSelCmp sels => normSelsNCmp sels nt2
  | NIfNil sels nt1_1 nt1_2 => match nt2 with
    | NSelCmp sels2 => NIfNil (sels2 ++ sels)
        (normNCmpSels nt1_1 sels2) (normNCmpSels nt1_2 sels2)
    | NIfNil sels2 nt2_1 nt2_2 => NIfNil sels2
        (normNCmp_nt2 nt2_1) (normNCmp_nt2 nt2_2)
    | _ => normNIf (normSelsNCmp sels nt2) 
        (normNCmp_nt1 nt1_1 nt2) (normNCmp_nt1 nt1_2 nt2)
    end
  | NBottom => NBottom
  end.
  
(** We can easily establish that the composition of 2 if-expressions can be
replaced by pushing the first if-expression inside the branches of the second: *)

Lemma normNCmpIfIf: forall sels1 sels2: list Selector,
  forall nt1_1 nt1_2 nt2_1 nt2_2: NTrm, let nt1 := NIfNil sels1 nt1_1 nt1_2 in 
  normNCmp nt1 (NIfNil sels2 nt2_1 nt2_2)
  = NIfNil sels2 (normNCmp nt1 nt2_1) (normNCmp nt1 nt2_2).
Proof.
(* begin hide *)
  reflexivity.
(* end hide *)
Qed.

(** We also establish that [normNCmp] satisfies the defining property of
function composition; this is the key lemma on which correctness of 
normalization relies:
*)

Lemma normNCmpPreservesEval: forall nt1 nt2: NTrm, forall v: Val,
  evalNT (normNCmp nt1 nt2) v = evalNT nt1 (evalNT nt2 v).
Proof.
(* begin hide *)
  unfold evalNT.
  induction nt1 as [ | nt1_1 IHnt1_1 nt1_2 IHnt1_2 |
    sels1 | sels1 nt1_1 IHnt1_1 nt1_2 IHnt1_2 | ]. 
  (* nt1 => NNil *) simpl. intro nt2.
    replace ((fix normNCmp_nt2 (nt0: NTrm): NTrm := NNil) nt2) 
      with (NNil) by (destruct nt2; reflexivity).
    reflexivity.
  (* nt1 => NCons nt1_1 nt1_2 *) simpl. intro nt2.
    replace ((fix normNCmp_nt2 (nt0: NTrm): NTrm := 
      NCons (normNCmp nt1_1 nt0) (normNCmp nt1_2 nt0)) nt2) 
      with (NCons (normNCmp nt1_1 nt2) (normNCmp nt1_2 nt2)) 
      by (destruct nt2; reflexivity).
    simpl. intro v.
    rewrite IHnt1_1. rewrite IHnt1_2. reflexivity.
  (* nt1 => NSelCmp sels1 *) simpl. intros nt2 v.
    replace ((fix normNCmp_nt2 (nt0: NTrm): NTrm := 
      normSelsNCmp sels1 nt0) nt2) 
      with (normSelsNCmp sels1 nt2)  
      by (destruct nt2; reflexivity).
    rewrite evalT_sels2trm.
    apply normSelsNCmpPreservesEval.
  (* nt1 => NIfNil sels1 nt1_1 nt1_2 *) 
    induction nt2 as [ | nt2_1 IHnt2_1 nt2_2 IHnt2_2 |
      sels2 | sels2 nt2_1 IHnt2_1 nt2_2 IHnt2_2 | ];
      try (simpl; intro v; rewrite normNIfPreservesEvalT;
        rewrite normSelsNCmpPreservesEvalT;
        rewrite IHnt1_1; rewrite IHnt1_2;
        rewrite evalT_sels2trm;
        reflexivity).
    (* n2 => NSelCmp sels2 *)
      simpl. intro v.
      rewrite evalT_sels2trm. rewrite evalT_sels2trm. rewrite evalT_sels2trm.
      rewrite evalSelsAppend. 
      fold (evalNT (normNCmpSels nt1_1 sels2) v).
      fold (evalNT (normNCmpSels nt1_2 sels2) v).
      rewrite normNCmpSelsPreservesEval.
      rewrite normNCmpSelsPreservesEval.
      unfold evalNT.
      reflexivity.
    (* n2 => NIfNil sels2 nt2_1 nt2_2 *)
      intro v.
      rewrite normNCmpIfIf. 
      unfold ntrm2trm at 1. fold ntrm2trm.
      unfold evalT at 1. fold evalT.
      rewrite IHnt2_1. rewrite IHnt2_2.
      rewrite evalT_sels2trm.
      unfold ntrm2trm at 6. fold ntrm2trm.
      unfold evalT at 6. fold evalT.
      unfold ntrm2trm at 5. fold ntrm2trm.
      unfold evalT at 5. fold evalT.
      rewrite evalT_sels2trm.
      rewrite evalT_sels2trm.
      unfold ntrm2trm at 1. fold ntrm2trm.
      unfold evalT at 1. fold evalT.
      rewrite evalT_sels2trm.
      unfold ntrm2trm at 6. fold ntrm2trm.
      unfold evalT at 6. fold evalT.
      rewrite evalT_sels2trm.
      destruct (evalSels sels2 v) as [|v1 v2|] _eqn: Heq; 
        try reflexivity.
      (* (evalSels sels2 v) => VBottom *)
        rewrite evalSelsVBottom. reflexivity.
  (* n1 => NBottom *) simpl. intro nt2.
    replace ((fix normNCmp_nt2 (nt0: NTrm): NTrm := NBottom) nt2)
      with (NBottom) by (destruct nt2; reflexivity).
    reflexivity.
(* end hide *)
Qed.

(** The last lemma is a bit tricky to prove: as [normNCmp] is defined using
nested lexicographic recursion, we must use nested induction in the proof and
apply rewritings using the previously proved lemmas. *)

(** Finally, the stage is set for the conversion of arbitrary expressions into
normal form: *)

Fixpoint normConv (t: Trm) {struct t} :NTrm :=
  match t with
  | Nil => NNil
  | Cons t1 t2 => NCons (normConv t1) (normConv t2)
  | Sel sel => NSelCmp (sel::nil)
  | Id => NSelCmp nil
  | Cmp t1 t2 => normNCmp (normConv t1) (normConv t2)
  | IfNil t1 t2 t3 => normNIf (normConv t1) (normConv t2) (normConv t3)
  | Bottom => NBottom
  end.

(** With all this in place, the 
main theorem establishing the correctness of normalization can be proved
by straightforward induction on the expression structure: 
*)

Theorem normConvPreservesEval: forall (t: Trm) (v: Val), 
  evalNT (normConv t) v = evalT t v.
Proof.
(* begin hide *)
  unfold evalNT.
  induction t as 
    [ | t1 IHt1 t2 IHt2 | sel | | t1 IHt1 t2 IHt2 | t1 IHt1 t2 IHt2 t3 IHt3 | ];
    try reflexivity.
    (* t => Cons t1 t2 *)
      simpl. intro v.
      rewrite IHt1. rewrite IHt2. reflexivity.
    (* t => Cmp t1 t2 *)
      simpl. intro v.
      fold (evalNT (normNCmp (normConv t1) (normConv t2)) v).
      rewrite normNCmpPreservesEval.
      rewrite <- IHt2. apply IHt1.
    (* t => IfNil t1 t2 t3 *) 
      simpl. intro v.
      rewrite normNIfPreservesEvalT.
      rewrite IHt1. rewrite IHt2. rewrite IHt3. reflexivity.
(* end hide *)
Qed.

(** We can see on an example, that [normConv] not only brings expressions into
normal form, but also achieves some optimizations like deforestation: 
*)

Eval compute in (ntrm2trm (normConv ((IfNil Hd ((Tl $ Tl) # (Hd $ Tl)) Tl) $ (Nil # Id)))).
(** 
<<
  = Tl # Hd : Trm
>>     

As we have seen in the introduction, however, normalization by itself 
does not eliminate redundant tests.
*)


(** ** Emulating Substitutions %\label{subsec:replaceAt}% *) 

(** Before we tackle positive information propagation, we need to make a small
detour and show how substitutions can be emulated inside our language, giving
a simple form of explicit substitutions %\cite{DBLP:journals/jfp/AbadiCCL91}%.
Let's first note
that we can replace a set of values, denoted by variables, with a list
structure built from pairs (e.g. %\cite{Jones:97:ComputabilityComplexity}%).
Variables in this case
can be replaced by positions in the list structure, represented by lists of
pair selectors. 
For example, the expression [IfNil x1 x2 x3], has three free variables. We can
pack their values into a list -- [x1 # x2 # x3] -- and replace their
references inside the expression with the corresponding list positions:
[IfNil Hd (Hd $ Tl) (Tl $ Tl)], as the following clearly holds:
[(IfNil Hd (Hd $ Tl) (Tl $ Tl)) $ (x1 # x2 # x3) = IfNil x1 x2 x3]. 
We can define an operation, [replaceAt], 
which for a given tree position (represented with a list
of selectors [pos]) and two normal-form expressions, generates a new expression, which
has the result of the second expression pushed at position [pos] in the 
result of the first expression. *)

Fixpoint replaceAt (pos: list Selector) (t trep: NTrm) {struct pos}: NTrm :=
  match pos with
    | nil => trep
    | sel::sels => match sel with
      | HD => NCons (replaceAt sels (normSelNCmp HD t) trep)
                    (normSelNCmp TL t)
      | TL => NCons (normSelNCmp HD t) 
                    (replaceAt sels (normSelNCmp TL t) trep)
    end
  end.

(** The action of this function is best illustrated with a couple of examples. 
If we have 2 values packed in a pair as input -- say [x1 # x2] -- we can fix 
the value of [x1] to [Nil # Nil] in the following way:
*)

Eval compute in (ntrm2trm (replaceAt (HD::nil) (normConv Id) (normConv (Nil # Nil)))).

(**
<<
  = (Nil # Nil) # Tl : Trm
>>
*)
(** We can substitute not only constant values but also arbitrary expressions
with [replaceAt] and [normNCmp]. If we consider again the expression 
[IfNil x1 x2 x3] with the given encoding of variables ([x1 # x2 # x3]), 
we can substitute [Tl $ Hd $ Tl # Hd $ Hd $ Tl] for [x2] thusly:
*)

Eval compute in (let nt1 := normConv (IfNil Hd (Hd $ Tl) (Tl $ Tl)) in
  let nt2 := normConv (Tl $ Hd $ Tl # Hd $ Hd $ Tl) in
  ntrm2trm (normNCmp nt1 (replaceAt (TL::HD::nil) (normConv Id) nt2))).

(**
<< 
  = IfNil Hd (Tl $ Hd $ Tl # Hd $ Hd $ Tl) (Tl $ Tl) : Trm 
>>
*)

(** We now establish some properties of [replaceAt] that will prove useful
later. *)

(* * %\begin{small}% *)
Lemma replaceAt_id: forall sels: list Selector, forall t trep: NTrm,
  normSelsNCmp sels (replaceAt sels t trep) = trep.
Proof.
(* begin hide *)
  induction sels; miniCrush;
  match goal with
    [|- context [ if ?X then _ else _ ] ] => destruct X end;
  miniCrush.
(* end hide *)
Qed.

Lemma replaceAt_app: forall (sels1 sels2: list Selector) (nt ntrepl: NTrm),
  replaceAt (sels1 ++ sels2) nt ntrepl
  = replaceAt sels1 nt (replaceAt sels2 (normSelsNCmp sels1 nt) ntrepl).
Proof.
(* begin hide *)
  induction sels1 as [|sel1 sels1']; try reflexivity.
  (* :: *) simpl. destruct sel1;
    try (intros sels2 nt ntrepl; rewrite IHsels1'; reflexivity).
(* end hide *)
Qed.
(* * %\end{small}% *)

(** For the next property, we need to compute the common prefix and the
different suffixes of 2 lists. We shall need also to compute
equivalence of selectors. *)

(* * %\begin{small}% *)
Definition Sel_eq_dec (sel1 sel2: Selector) : {sel1 = sel2} + {sel1 <> sel2}.
(* begin show *) 
  decide equality. 
(* end show *) 
Defined.
(* * %\end{small}% *)

(** This is just a nice trick to let Coq deduce the equality predicate for us. 
The type [{sel1 = sel2} + {sel1 <> sel2}] is a sum type than not only gives
the outcome of the test, but also contains a proof of the corresponding
equality/inequality. For simplicity, we can cast this result to a simple [bool],
using the fact that Coq if expressions apply generically to any type with
2 constructors:
*)

(* * %\begin{small}% *)
Definition eqSel sel1 sel2 := if Sel_eq_dec sel1 sel2 then true else false.

Lemma eqSel_reflx: forall sel, eqSel sel sel = true.
Proof.
(* begin hide *)
  unfold eqSel. intro sel.
  match goal with [|- context[if ?X then _ else _]] => destruct X end;
  miniCrush.
(* end hide *)
Qed.

Fixpoint commonPrefix (X: Set) (eqX: X -> X -> bool) (l1 l2: list X)
  {struct l1} : (list X) * (list X) * (list X) := match l1, l2 with
  | nil, _ => (nil, nil, l2)
  | _, nil => (nil, l1, nil)
  | x::xs, y::ys => if eqX x y then 
      let cp := commonPrefix X eqX xs ys in let pr := fst (fst cp) in
      let l1a := snd (fst cp) in let l2a := snd cp in (x::pr, l1a, l2a)
    else (nil, l1, l2)
  end.

Lemma commonPrefix_X_XappY: forall X: Set, forall eqX: X -> X -> bool,
  (forall x: X, eqX x x = true) -> forall xs ys: list X,
  commonPrefix X eqX xs (xs ++ ys) = (xs, nil, ys).
Proof.
(* begin hide *)
  induction xs; miniCrush. 
(* end hide *)
Qed.

Lemma normSelsNCmp_ReplaceAt: forall (sels1 sels2: list Selector),
  forall (nt ntrepl: NTrm), normSelsNCmp sels1 (replaceAt sels2 nt ntrepl) = 
  let cp := commonPrefix _ eqSel sels1 sels2 in let csels := fst (fst cp) in
  let usels1 := snd (fst cp) in let usels2 := snd cp in
  normSelsNCmp usels1 (replaceAt usels2 (normSelsNCmp csels nt) ntrepl).
Proof.
(* begin hide *)
  (*  
  normSelsNCmp sels1 (replaceAt sels2 nt ntrepl)
  = normSelsNCmp sels1 (replaceAt (common ++ uniqsels2) nt ntrepl)
  = normSelsNCmp sels1 (replaceAt common nt 
      (replaceAt uniqsels2 (normSelsNCmp common nt) ntrepl))
  = normSelsNCmp uniqsels1 (normSelsNCmp common (replaceAt common nt 
      (replaceAt uniqsels2 (normSelsNCmp common nt) ntrepl)))
  = normSelsNCmp uniqsels1 
      (replaceAt uniqsels2 (normSelsNCmp common nt) ntrepl)
  *)
  induction sels1 as [|sel1 sels1']; try reflexivity.
  (* :: *) destruct sels2 as [|sel2 sels2']; try reflexivity.
    (* :: *) simpl. destruct sel2.
      (* true *) simpl. destruct sel1; try reflexivity;
        try (simpl; intros nt ntrepl;
          rewrite IHsels1'; reflexivity).
      (* false *) simpl. destruct sel1; try reflexivity;
        try (simpl; intros nt ntrepl;
          rewrite IHsels1'; reflexivity).
(* end hide *)
Qed.

Lemma replaceAt_NSelCmp: forall (sels1 sels2: list Selector) (nt: NTrm),
  replaceAt sels1 (NSelCmp sels2) nt 
  = normSelsNCmp sels2 (replaceAt (sels2 ++ sels1) (NSelCmp nil) nt).
Proof.
(* begin hide *)
  (*
  induction sels2; miniCrush.
  match goal with
    [|- context [ if ?X then _ else _ ] ] => destruct X end;
  miniCrush.
  *)
  intros sels1 sels2 nt.
  replace (replaceAt sels1 (NSelCmp sels2) nt)
    with (normSelsNCmp nil (replaceAt sels1 (NSelCmp sels2) nt))
    by reflexivity.
  replace (NSelCmp sels2) with (normSelsNCmp sels2 (NSelCmp nil))
    by (rewrite normSelsNCmp_NSelCmp; reflexivity).
  replace (normSelsNCmp nil (replaceAt sels1
            (normSelsNCmp sels2 (NSelCmp nil)) nt))
    with (let cp := commonPrefix _ eqSel sels2 (sels2 ++ sels1) in
          let common := fst (fst cp) in
          let uniqsels1 := snd (fst cp) in
          let uniqsels2 := snd cp in
          normSelsNCmp uniqsels1 (replaceAt uniqsels2
            (normSelsNCmp common (NSelCmp nil)) nt)).
  rewrite <- normSelsNCmp_ReplaceAt. reflexivity.
  (* replace proof *) rewrite commonPrefix_X_XappY. reflexivity.
    apply eqSel_reflx.
(* end hide *)
Qed.
(* * %\end{small}% *)



(** ** Positive Information Propagation %\label{subsec:propagate}% *)

(** We can use object-level substitution, as implemented by [replaceAt] 
and [normNCmp], to
propagate information about the test result inside the branches of a 
conditional expressions. This transformation is one of
the key differences that distinguish supercompilation from weaker
optimizations like classical partial evaluation and deforestation 
%\cite{GlueckKlimov:93,sorm98b}%.
The definition is greatly simplified by the fact that normal-form tests
can only take the form of selector compositions.
*)

Definition setNilAt (sels: list Selector): NTrm := 
  replaceAt sels (NSelCmp nil) NNil.

Definition setConsAt (sels: list Selector) : NTrm := 
  replaceAt sels (NSelCmp nil) 
    (NCons (NSelCmp (sels ++ HD::nil)) (NSelCmp (sels ++ TL::nil))).

(** Once we have an expression encoding the substitution of the test result,
what remains is to compose it with the corresponding if-branch, as in our case
substitution composition is replaced by simple function composition.
*)

Fixpoint propagateIfCond (nt: NTrm) {struct nt} : NTrm :=
  match nt with
  | NCons nt1 nt2 => NCons (propagateIfCond nt1) (propagateIfCond nt2)
  | NIfNil sels nt1 nt2 =>
    let nt1a := propagateIfCond nt1 in let nt2a := propagateIfCond nt2 in
    let nt1b := normNCmp nt1a (setNilAt sels) in
    let nt2b := normNCmp nt2a (setConsAt sels) in NIfNil sels nt1b nt2b
  | _ => nt
  end.

(** Establishing the correctness of [propagateIfCond] is once again decomposed
into a sequence of lemmas. 
*)

(* * %\begin{small}% *)
Lemma setNilAtPreservesEvalAux: forall (sels1 sels2: list Selector), 
  replaceAt sels1 (NSelCmp sels2) NNil
  = normNCmpSels (replaceAt sels1 (NSelCmp nil) NNil) sels2.
Proof.
(* begin hide *)
  induction sels1 as [|sel1 sels1'].
  (* nil *) simpl. auto.
  (* :: *) simpl. destruct sel1.
    (* HD *) simpl. intro sels2. f_equal. 
      rewrite IHsels1'.
      symmetry. rewrite IHsels1'.
      rewrite <- normNCmpSels_app. 
      reflexivity.
    (* TL *) simpl. intro sels2. f_equal.
      rewrite IHsels1'.
      symmetry. rewrite IHsels1'.
      rewrite <- normNCmpSels_app. 
      reflexivity.
(* end hide *)
Qed.

Lemma setConsAtPreservesEvalAux: forall (sels1 sels2: list Selector), 
  replaceAt sels1 (NSelCmp sels2) (NCons (NSelCmp 
    (sels2++sels1++HD::nil)) (NSelCmp (sels2++sels1++TL::nil)))
  = normNCmpSels (replaceAt sels1 (NSelCmp nil) (NCons 
    (NSelCmp (sels1++HD::nil)) (NSelCmp (sels1++TL::nil)))) sels2.
Proof.
(* begin hide *)
  induction sels1 as [|sel1 sels1'].
  (* nil *) simpl. reflexivity.
  (* :: *) simpl. destruct sel1.
    (* HD *) simpl. intro sels2. f_equal.
      replace (sels2 ++ HD::sels1' ++ HD::nil) 
        with ((sels2 ++ HD::nil) ++ sels1' ++ HD::nil)
        by (rewrite app_ass; reflexivity). 
      replace (sels2 ++ HD::sels1' ++ TL::nil) 
        with ((sels2 ++ HD::nil) ++ sels1' ++ TL::nil)
        by (rewrite app_ass; reflexivity). 
      rewrite IHsels1'.
      symmetry.
      replace (HD::sels1' ++ HD::nil) 
        with ((HD::nil) ++ sels1' ++ HD::nil) by reflexivity.
      replace (HD::sels1' ++ TL::nil) 
        with ((HD::nil) ++ sels1' ++ TL::nil) by reflexivity.
      rewrite IHsels1'.
      rewrite <- normNCmpSels_app. 
      reflexivity.
    (* TL *) simpl. intro sels2. f_equal.
      replace (sels2 ++ TL::sels1' ++ HD::nil) 
        with ((sels2 ++ TL::nil) ++ sels1' ++ HD::nil)
        by (rewrite app_ass; reflexivity). 
      replace (sels2 ++ TL::sels1' ++ TL::nil) 
        with ((sels2 ++ TL::nil) ++ sels1' ++ TL::nil)
        by (rewrite app_ass; reflexivity). 
      rewrite IHsels1'.
      symmetry. 
      replace (TL::sels1' ++ HD::nil) 
        with ((TL::nil) ++ sels1' ++ HD::nil) by reflexivity.
      replace (TL::sels1' ++ TL::nil) 
        with ((TL::nil) ++ sels1' ++ TL::nil) by reflexivity.
      rewrite IHsels1'.
      rewrite <- normNCmpSels_app. 
      reflexivity.
(* end hide *)
Qed.

Lemma setNilAtPreservesEvalAux2: forall (v: Val), forall (sels1 sels2: list Selector),
  evalSels sels1 (evalNT (setNilAt (sels1++sels2)) v)
  = evalNT (setNilAt sels2) (evalSels sels1 v).
Proof.
(* begin hide *)
  unfold setNilAt.
  intros.
  rewrite <- normNCmpSelsPreservesEval.
  rewrite replaceAt_app.
  rewrite <- normSelsNCmpPreservesEval.
  rewrite replaceAt_id.
  rewrite normSelsNCmp_NSelCmp.
  simpl.
  f_equal.
  apply setNilAtPreservesEvalAux.
(* end hide *)
Qed.

Lemma setConsAtPreservesEvalAux2: forall (v: Val), forall (sels1 sels2: list Selector),
  evalSels sels1 (evalNT (setConsAt (sels1++sels2)) v)
  = evalNT (setConsAt sels2) (evalSels sels1 v).
Proof.
(* begin hide *)
  unfold setConsAt.
  intros.
  rewrite <- normNCmpSelsPreservesEval.
  rewrite replaceAt_app.
  rewrite <- normSelsNCmpPreservesEval.
  rewrite replaceAt_id.
  rewrite normSelsNCmp_NSelCmp.
  simpl.
  f_equal.
  rewrite app_ass. rewrite app_ass.
  apply setConsAtPreservesEvalAux.
(* end hide *)
Qed.

Lemma setNilAtPreservesEval: forall sels: list Selector, forall v: Val,
  evalSels sels v = VNil -> evalNT (setNilAt sels) v = v.
Proof.
(* begin hide *)
  intros sels v.
  generalize dependent sels.
  induction v.
  (* VNil *) destruct sels as [|sel sels'].
    (* nil *) unfold setNilAt. unfold evalNT. simpl. auto.
    (* :: *) simpl. rewrite evalSelsVBottom. 
      intro contra. inversion contra.
  (* VCons v1 v2 *) destruct sels as [|sel sels'].
    (* nil *) unfold setNilAt. unfold evalNT. simpl. auto.
    (* :: *) unfold setNilAt. unfold evalNT. simpl.
      destruct sel.
      (* HD *) intro H. simpl.
        f_equal. 
        rewrite replaceAt_NSelCmp.
        unfold app. rewrite normSelsNCmpPreservesEvalT.
        replace (HD::sels') with ((HD::nil)++sels') by reflexivity.
        fold (setNilAt ((HD::nil)++sels')).
        fold (evalNT (setNilAt ((HD::nil)++sels')) (VCons v1 v2)).
        rewrite setNilAtPreservesEvalAux2.
        simpl.
        apply IHv1. apply H.
      (* TL *) intro H. simpl.
        f_equal. 
        rewrite replaceAt_NSelCmp.
        unfold app. rewrite normSelsNCmpPreservesEvalT.
        replace (TL::sels') with ((TL::nil)++sels') by reflexivity.
        fold (setNilAt ((TL::nil)++sels')).
        fold (evalNT (setNilAt ((TL::nil)++sels')) (VCons v1 v2)).
        rewrite setNilAtPreservesEvalAux2.
        simpl.
        apply IHv2. apply H.
  (* VBottom *) intro sels. rewrite evalSelsVBottom. 
    intro contra. inversion contra.
(* end hide *)
Qed.

Lemma setConsAtPreservesEval: forall sels: list Selector, forall v v1 v2: Val,
  evalSels sels v = VCons v1 v2 -> evalNT (setConsAt sels) v = v.
Proof.
(* begin hide *)
  intros sels v.
  generalize dependent sels.
  induction v.
  (* VNil *) destruct sels as [|sel sels'].
    (* nil *) unfold setConsAt. unfold evalNT. simpl. 
      intros v1 v2 contra. inversion contra.
    (* :: *) simpl. rewrite evalSelsVBottom. 
      intros v1 v2 contra. inversion contra.
  (* VCons v3 v4 *) destruct sels as [|sel sels'].
    (* nil *) unfold setConsAt. unfold evalNT. simpl. auto.
    (* :: *) unfold setConsAt. unfold evalNT. simpl.
      destruct sel.
      (* HD *) intros v3 v4 H. simpl.
        f_equal.
        rewrite replaceAt_NSelCmp.
        rewrite normSelsNCmpPreservesEvalT.
        replace (HD::sels' ++ HD::nil) 
          with ((HD::nil) ++ sels' ++ HD::nil) by reflexivity.
        replace (HD::sels' ++ TL::nil) 
          with ((HD::nil) ++ sels' ++ TL::nil) by reflexivity.
        rewrite <- app_ass. rewrite <- app_ass.
        fold (setConsAt ((HD::nil)++sels')).
        fold (evalNT (setConsAt ((HD::nil)++sels')) (VCons v1 v2)).
        rewrite setConsAtPreservesEvalAux2.
        simpl.
        apply IHv1 with (v2:=v3)(v3:=v4). apply H.
      (* TL *) intros v3 v4 H. simpl.
        f_equal.
        rewrite replaceAt_NSelCmp.
        rewrite normSelsNCmpPreservesEvalT.
        replace (TL::sels' ++ HD::nil) 
          with ((TL::nil) ++ sels' ++ HD::nil) by reflexivity.
        replace (TL::sels' ++ TL::nil) 
          with ((TL::nil) ++ sels' ++ TL::nil) by reflexivity.
        rewrite <- app_ass. rewrite <- app_ass.
        fold (setConsAt ((TL::nil)++sels')).
        fold (evalNT (setConsAt ((TL::nil)++sels')) (VCons v1 v2)).
        rewrite setConsAtPreservesEvalAux2.
        simpl.
        apply IHv2 with (v1:=v3)(v3:=v4). apply H.
  (* VBottom *) intros sels v1 v2. rewrite evalSelsVBottom. 
    intro contra. inversion contra.
(* end hide *)
Qed.

Lemma condPropagatorsPreserveEval: forall (sels: list Selector) (nt1 nt2: NTrm),
  forall (v: Val), evalNT (NIfNil sels (normNCmp nt1 (setNilAt sels)) 
    (normNCmp nt2 (setConsAt sels))) v = evalNT (NIfNil sels nt1 nt2) v.
Proof.
(* begin hide *)
  simpl. intros sels nt1 nt2 v.
  unfold evalNT. simpl. rewrite evalT_sels2trm.
  destruct (evalSels sels v) as [|v1 v2|] _eqn: evalSelsEqn.
    (* VNil *) fold (evalNT (normNCmp nt1 (setNilAt sels)) v).
      rewrite normNCmpPreservesEval. rewrite setNilAtPreservesEval.
      unfold evalNT. reflexivity. apply evalSelsEqn.
    (* VCons v1 v2 *) 
      fold (evalNT (normNCmp nt2 (setConsAt sels)) v).
      rewrite normNCmpPreservesEval. 
      rewrite setConsAtPreservesEval with (v1:=v1)(v2:=v2).
      unfold evalNT. reflexivity. apply evalSelsEqn.
    (* VBottom *) reflexivity.
(* end hide *)
Qed.
(* * %\end{small}% *)

(** The proofs of these lemmas involve some tricky rewrites, using the 
established properties of [replaceAt]. Details can be found in the actual
Coq sources. The main theorem can now be proved easily by induction, using the 
last lemma [condPropagatorsPreserveEval].
*)

Theorem propagateIfCondPreservesEval: forall nt: NTrm, forall v: Val,
  evalNT (propagateIfCond nt) v = evalNT nt v.
Proof.
(* begin hide *)
  induction nt as [ | nt1 IHnt1 nt2 IHnt2 |
    sels | sels nt1 IHnt1 nt2 IHnt2 | ];
    try reflexivity.
  (* nt => NCons nt1 nt2 *) simpl. intro v.
    unfold evalNT. simpl.
    unfold evalNT in IHnt1.
    unfold evalNT in IHnt2.
    rewrite IHnt1. rewrite IHnt2. reflexivity.
  (* nt => NIfNil sels *) 
    unfold propagateIfCond. fold propagateIfCond.
    intro v.
    rewrite condPropagatorsPreserveEval.
    unfold evalNT in IHnt1.
    unfold evalNT in IHnt2.
    unfold evalNT. 
    simpl. rewrite IHnt1. rewrite IHnt2. reflexivity.
(* end hide *)
Qed.

(** We can combine the first two stages -- normalization and positive information
propagation -- into a single function, and trivially establish its correctness.
*)

Definition norm (t: Trm) := propagateIfCond (normConv t).

Theorem normPreservesEval: forall t v, evalNT (norm t) v = evalT t v.
Proof.
(* begin hide *)
  intros. unfold norm. 
  rewrite propagateIfCondPreservesEval.
  apply normConvPreservesEval.
(* end hide *)
Qed.

(** Recalling the example from the introduction, we can see that [norm]
also eliminates redundant tests, besides other reductions: 
*)

Eval compute in (ntrm2trm (norm (IfNil Hd (Nil # Nil) (IfNil Hd Nil Tl)))).
(** 
<<
  = IfNil Hd (Nil # Nil) Tl : Trm
>>
*)

(** * A Turing-complete Imperative Language %\label{sec:SWhile}%

While our simple expression language has helped us to successfully 
study some key aspects of supercompilation, it is obvious that we cannot 
write many interesting programs in it.  Not only it is far from being 
Turing-complete, but it even lacks full-blown primitive recursion. However, 
we can build upon this language to obtain a larger, Turing-complete one. 
For example, we can embed the language of simple expressions inside a small 
imperative language with assignments and while-loops (called here SWhile):
*)

Inductive SWhileStmt: Set :=
  | Assign: Trm -> SWhileStmt
  | Seq: SWhileStmt -> SWhileStmt -> SWhileStmt
  | While: Trm -> SWhileStmt -> SWhileStmt.

(** As a further simplification, we assume that the language has a single 
variable, similar to other research languages like I and LOOP 
%\cite{Jones:97:ComputabilityComplexity,hartmannjonessimonsen:optimalspec}%. 
This variable is implicitly used in assignments and while tests.
As this language is Turing-complete, we cannot
specify its evaluator directly as a total Coq function, like we did for
the language of simple expressions. We can specify its semantics as
a logical relation, which is encoded in Coq as a (dependent) inductive
family living in [Prop]:
*)

Inductive SWhileEvalRel: Val -> SWhileStmt -> Val -> Prop :=
  | SWhileEvalAssign: forall e v, SWhileEvalRel v (Assign e) (evalT e v) 
  | SWhileEvalSeq: forall st1 st2 v1 v2 v3,
    SWhileEvalRel v1 st1 v2 -> SWhileEvalRel v2 st2 v3 ->
    SWhileEvalRel v1 (Seq st1 st2) v3
  | SWhileEvalWhileNil: forall cond st v,
    evalT cond v = VNil -> SWhileEvalRel v (While cond st) v
  | SWhileEvalWhileBottom: forall cond st v,
    evalT cond v = VBottom -> SWhileEvalRel v (While cond st) VBottom
  | SWhileEvalWhileCons: forall cond st v1 v2 v3 vh vt,
    evalT cond v1 = VCons vh vt -> SWhileEvalRel v1 st v2 -> 
    SWhileEvalRel v2 (While cond st) v3 ->
    SWhileEvalRel v1 (While cond st) v3.

Hint Constructors SWhileEvalRel.

(** We can further simplify our task, by considering only
programs containing a single while loop. This can be seen as an analog
of Kleene's normal form (KNF) from recursion theory, and there are
well-known proofs (not repeated here) that limiting ourselves to
a single while loop implies no loss of generality
%\cite{DBLP:journals/cacm/Harel80}%. The "Kleene normal form" 
analog for SWhile programs can
be represented as a record of 4 simple expressions: *)

Record KNFProg : Set := MkKNFProg {
  initExp: Trm; condExp: Trm; bodyExp: Trm; finalExp: Trm }.

(** The meaning is obvious by the injection into the full syntax of
SWhile programs: *)

Definition KNFtoProg knf :=
  Seq (Assign (initExp knf))
  (Seq (While (condExp knf) (Assign (bodyExp knf)))
    (Assign (finalExp knf))).

Hint Transparent KNFtoProg.

(** We can introduce a bit of syntactic sugar for SWhile constructs (at
the expense of a conflict with the [Record] syntax). *)

Infix ";" := Seq (at level 65, right associativity).
Notation "'VAR' '<-' e" := (Assign e) (at level 64).
Notation "'WHILE' cond 'DO' body 'DONE'" := (While cond body) (at level 0).

(** As a simple example, here is a program that reverses its input (assuming 
the usual Lisp encoding of lists as binary trees).
*)

Definition revList_knf := MkKNFProg 
  (Id # Nil) Hd (Tl $ Hd # Hd $ Hd # Tl) Tl.
Eval compute in (KNFtoProg revList_knf).
(**
<<
= VAR  <- Id # Nil;
  WHILE Hd DO VAR  <- Tl $ Hd # Hd $ Hd # Tl DONE; 
  VAR  <- Tl : SWhileStmt
>>
We see here one important drawback of the simplifications we introduced: our
language is very difficult to program in, and very unreadable. 
To make the meaning of the code clearer, we can rewrite it by hand to a
version of SWhile with many variables; in our case 2 suffice --
[input] and [output]:
<<
  output  <- Nil;
  WHILE input DO 
    (input # output) <- (Tl $ input) # (Hd $ input # output) DONE; 
>>
*)

(** While the abstract syntax of SWhile permits arbitrary expressions
as while-loop conditions, many optimizing transformations that follow
are valid only if the condition of the loop is strict, according to the
following definition: *)

Definition strictTrm (t: Trm) := evalT t VBottom = VBottom.

(** We can easily see that strictness for our expression language
amounts to a simple syntactic check on the normal form of the
expression:
*)

Lemma strictTrm_SyntaxCriterion: forall (t: Trm), strictTrm t <-> 
  (match normConv t with | NNil | NCons _ _ => false | _ => true end) = true.
Proof.
(* begin hide *)
  intro t.
  unfold strictTrm.
  rewrite <- normConvPreservesEval.
  remember (normConv t) as nt.
  clear t Heqnt. unfold evalNT.
  miniCrush.
  (* -> *)
  revert H. induction nt; miniCrush.
  (* <- *)
  match goal with [H: context[match ?X with | NNil => _ | NCons _ _ => _
    | NSelCmp _ => _ | NIfNil _ _ _ => _ | NBottom => _ end] |- _]
    => destruct X as [|? ?|?|? ? ?|] _eqn: Heqn end;
  miniCrush;
  rewrite evalSelsVBottom;
  miniCrush.
(* end hide *)
Qed.

(** So it is obviously reasonable to consider only programs with strict loop conditions
as otherwise the loop degenerates to either an infinite or an empty one.

While the relational specification of SWhile semantics is elegant, it
is not executable (at least not inside Coq). We can build an
approximation to an evaluation function in Coq itself, using a standard
trick for modeling partial functions -- 
we add an extra parameter limiting the recursion depth,
and the definition of the evaluation function can be done by
structural recursion on that new parameter. We do so only for
the KNF special case.
*)

Fixpoint evalKNFCore (d: nat) (cond e: Trm) (v: Val) {struct d} 
  : option Val := match d with
  | O => None
  | S d' => match evalT cond v with
    | VNil => Some v
    | VBottom => Some VBottom
    | VCons _ _ => evalKNFCore d' cond e (evalT e v)
    end
  end.

Definition evalKNF (d: nat) (knf: KNFProg) (v: Val) : option Val := 
  match evalKNFCore d (condExp knf) (bodyExp knf)
   (evalT (initExp knf) v) with
  | None => None
  | Some v => Some (evalT (finalExp knf) v)
  end.

(** We can now execute the example program above on some input: *)

Definition listToVal vs := fold_right VCons VNil vs.
Eval vm_compute in (evalKNF 3 revList_knf 
  (listToVal (VNil::(VCons VNil VNil)::nil))).
(**
<<
  = Some (VCons (VCons VNil VNil) (VCons VNil VNil)) : option Val
>>
*)

(** In order to verify that the executable interpreter is correct with respect
to the relational semantics given above, we first establish, that the evaluation
of the loop by [evalKNFCore] respects the semantics, and then we prove the 
correctness of the main evaluation function -- [evalKNF]
*)

Lemma evalKNFCore_SWhileEvalRel: forall cond e v1 v2,
  SWhileEvalRel v1 (While cond (Assign e)) v2 <->
  exists d: nat, evalKNFCore d cond e v1 = Some v2.
Proof.
(* begin hide *)
  miniCrush.
  (* -> *)
  remember (WHILE cond DO VAR <- e DONE) as prg.
  induction H; try solve [exists 1; miniCrush].
  miniCrush.
  inversion H0; miniCrush.
  exists (S x). miniCrush.
  (* <- *)
  generalize dependent v2.
  revert cond e v1.
  induction x; miniCrush.
  match goal with [ H: context [ match ?X with
    | VNil => _ | VCons _ _ => _ | VBottom => _ end ] |- _ ] 
    => destruct X as [|? ?|] _eqn: CondEqn end;
  miniCrush.
  eauto.
(* end hide *)
Qed.

Theorem evalKNF_SWhileEvalRel: forall knf v1 v2,
  SWhileEvalRel v1 (KNFtoProg knf) v2 <-> 
  exists d: nat, evalKNF d knf v1 = Some v2.
Proof.
(* begin hide *)
  unfold evalKNF. unfold KNFtoProg.
  miniCrush.

  (* -> *)
  inversion H; miniCrush.
  inversion H3; miniCrush.
  inversion H5; miniCrush.
  inversion H7; miniCrush.
  apply -> evalKNFCore_SWhileEvalRel in H4.
  miniCrush.
  exists x. miniCrush.
  
  (* <- *)
  eapply SWhileEvalSeq. 
  miniCrush.
  match goal with [ H: context [ match ?X with
    | Some _ => _ | None => _ end ] |- _ ] 
    => destruct X as [?|] _eqn: optEqn end;
  miniCrush.
  apply SWhileEvalSeq with (v2:=v); miniCrush. 
  apply <- evalKNFCore_SWhileEvalRel.
  exists x. assumption.
(* end hide *)
Qed.


(** ** Loop Unrolling %\label{subsec:unroll}%

The principal additional optimization that we can perform on loop programs -- 
on the top of the already existing optimizations for the expression
sub-language -- is loop unrolling. We can study different forms of
while-loop unrolling; here we shall limit ourselves to one simple form of unrolling --
trying to execute the body of the loop once before entering the loop itself,
provided the condition of the loop holds. Of course, we cannot expect spectacular
optimizations from this form of unrolling; in the very least, it leaves the loop
itself unmodified. It is sufficient, however, to demonstrate the power of
positive information propagation in some simple cases. Later in the paper we discuss
possibilities for more powerful forms of loop unrolling.
*)

Definition unrollToInit knf := let nrm t := ntrm2trm (norm t) in
  let newInit := nrm ((IfNil (condExp knf) Id (bodyExp knf)) $ (initExp knf))
  in MkKNFProg newInit (condExp knf) (bodyExp knf) (finalExp knf).

(** We can verify that unrolling the loop once respects the semantics. 
It turns easier to use [evalKNFCore] and [evalKNF] as semantics
specifications; it is OK as we have already verified that they are 
faithful to the original specification by a logical relation.
*)

(* * %\begin{small}% *)
Lemma normPreservesEval': forall t v, evalT (ntrm2trm (norm t)) v = evalT t v.
Proof.
(* begin hide *)
  intros.
  fold (evalNT (norm t) v).
  apply normPreservesEval.
(* end hide *)
Qed.

(* begin hide *)
Hint Rewrite normPreservesEval' : miniCrushDb.
Hint Rewrite evalT_sels2trm : miniCrushDb.
(* end hide *)

Lemma evalKNFCore_Bottom: forall d cond e v, strictTrm cond -> 
  evalKNFCore d cond e VBottom = Some v -> v = VBottom.
Proof.
(* begin hide *)
  unfold strictTrm.
  induction d; miniCrush.
  rewrite H in H0. miniCrush.
(* end hide *)
Qed.

Lemma evalKNFCore_unrollToInit_fw: forall d knf v1 v2, strictTrm (condExp knf)
  -> evalKNFCore d (condExp knf) (bodyExp knf) v1 = Some v2 -> 
  exists d2: nat, evalKNFCore d2 (condExp knf) (bodyExp knf) (evalT 
    (IfNil (condExp knf) Id (bodyExp knf)) v1) = Some v2.
Proof.
(* begin hide *)
  unfold strictTrm.
  miniCrush.
  revert v1 v2 H0.
  induction d; miniCrush.
  match goal with [H: context[match ?X with | VNil => _ 
    | VCons _ _ => _ | VBottom => _ end] |- _] 
    => destruct X as [|? ?|] _eqn: Heqn end;
  miniCrush; try solve [exists 1; miniCrush].
  apply IHd in H0. miniCrush.
  match goal with [H: context[match ?X with | VNil => _ 
    | VCons _ _ => _ | VBottom => _ end] |- _] 
    => destruct X as [|? ?|] _eqn: Heqn2 end;
  miniCrush; eauto.
  exists (S x). miniCrush.
  exists 2. miniCrush.
  apply evalKNFCore_Bottom in H0; miniCrush.
(* end hide *)
Qed.
  
Lemma evalKNF_unrollToInit_fw: forall d knf v1 v2, strictTrm (condExp knf) 
  -> evalKNF d knf v1 = Some v2 ->
  exists d2: nat, evalKNF d2 (unrollToInit knf) v1 = Some v2.
Proof.
(* begin hide *)
  unfold strictTrm.
  unfold unrollToInit. unfold evalKNF. miniCrush.
  match goal with [H: context[match ?X with | Some _ => _ | None => _ end] |- _] 
    => destruct X as [?|] _eqn: optEqn end;
  miniCrush.
  apply evalKNFCore_unrollToInit_fw in optEqn; miniCrush.
  exists x. miniCrush.
(* end hide *)
Qed.

Lemma evalKNFCore_unrollToInit_bw: forall d knf v1 v2, strictTrm (condExp knf)
  -> evalKNFCore d (condExp knf) (bodyExp knf) (evalT 
    (IfNil (condExp knf) Id (bodyExp knf)) v1) = Some v2 ->
  exists d2: nat, evalKNFCore d2 (condExp knf) (bodyExp knf) v1 = Some v2.
Proof.
(* begin hide *)
  unfold strictTrm.
  miniCrush.
  revert v1 v2 H0.
  induction d; miniCrush.
  match goal with [H: context[match ?X with | VNil => _ 
    | VCons _ _ => _ | VBottom => _ end] |- _] 
    => destruct X as [|? ?|] _eqn: Heqn end;
  miniCrush;
  match goal with [H: context[match ?X with | VNil => _ 
    | VCons _ _ => _ | VBottom => _ end] |- _] 
    => destruct X as [|? ?|] _eqn: Heqn2 end;
  miniCrush; try solve [exists 2; miniCrush].
  
  replace (evalT (bodyExp knf) (evalT (bodyExp knf) v1))
  with (match evalT (condExp knf) (evalT (bodyExp knf) v1) with
    | VNil => (evalT (bodyExp knf) v1)
    | VCons _ _ => (evalT (bodyExp knf) (evalT (bodyExp knf) v1))
    | VBottom => VBottom
    end) in H0; 
  miniCrush.
  apply IHd in H0. miniCrush.
  exists (S x). miniCrush.
(* end hide *)
Qed.
  
Lemma evalKNF_unrollToInit_bw: forall d knf v1 v2, strictTrm (condExp knf)
  -> evalKNF d (unrollToInit knf) v1 = Some v2 -> 
  exists d2: nat, evalKNF d2 knf v1 = Some v2.
Proof.
(* begin hide *)
  unfold strictTrm.
  unfold unrollToInit. unfold evalKNF. miniCrush.
  match goal with [H: context[match ?X with | Some _ => _ | None => _ end] |- _] 
    => destruct X as [?|] _eqn: optEqn end;
  miniCrush.
  generalize evalKNFCore_unrollToInit_bw. miniCrush.
  apply H0 in optEqn; miniCrush.
  exists x. miniCrush.
(* end hide *)
Qed.
(* * %\end{small}% *)

(* begin hide *)
Hint Resolve evalKNF_unrollToInit_fw evalKNF_unrollToInit_bw.
(* end hide *)

Theorem evalKNF_unrollToInit: forall knf v1 v2, strictTrm (condExp knf) ->
  ((exists d: nat, evalKNF d knf v1 = Some v2) <->
   (exists d2: nat, evalKNF d2 (unrollToInit knf) v1 = Some v2)).
Proof.
(* begin hide *)
  unfold strictTrm.
  miniCrush; eauto.
(* end hide *)
Qed.

(** 
To deal with repeated unrollings and to lay the background for termination
verification of the whole supercompiler, we need streams (infinite sequences).
A simple function-based definition suffices for our purposes.
*)

Definition Stream A := nat -> A .

(** We define a couple of basic operations on streams -- the
well-known [map] and %\coqdocvar{unfold}% from the functional programming
repertoire.
*)

Definition streamMap A B (f: A -> B) (s: Stream A) : Stream B := 
  fun n => f (s n).
Implicit Arguments streamMap [A B].

Definition streamUnfold X (seed: X) (f: X -> X) : Stream X :=
  fix streamUnfold' (n: nat) {struct n} : X := match n with
  | O => seed | S n' => f (streamUnfold' n')  end.
Implicit Arguments streamUnfold [X].


(** ** Homeomorphic Embedding for Ensuring Termination %\label{subsec:homemb}%
The so-called "whistle" of our supercompiler uses the now-standard approach
of relying on homeomorphic embedding and the Kruskal's tree theorem
%\cite{sorm95a}% to ensure termination of the process. 
To formulate this theorem in its general form,
we introduce a type of arbitrary first-order terms. The Coq [Section]
mechanism allows to specify only once parameters 
common for a whole set of definitions -- in our case the types
for term variables and function symbols, as well as the fact that function symbols
have decidable equality. (Variables of first-order terms typically also have 
decidable equality, but it is not needed in the current development.) *)

Section FOTerms.

Variable V: Set. Variable F: Set.
Variable F_eq_dec: forall f g: F, {f = g} + {f <> g}.

(** We adopt a slightly non-standard definition
of first-order terms, which is however easier to work with in Coq: *)

Inductive FOTerm : Set :=
  | FOVar: V -> FOTerm
  | FOFun0: option F -> FOTerm
  | FOFun2: option F -> FOTerm -> FOTerm -> FOTerm.

Definition optionF_eq_dec (f1 f2: option F): {f1 = f2} + {f1 <> f2}.
(* begin show *)  
  decide equality.
(* end show *)
Defined.

(** Even with this definition of first-order terms, defining
an executable version of homeomorphic embedding in Coq is a little 
tricky -- we need two nested structural recursions, like in the case
of [normNCmp]. *)

Definition homemb (t1 t2: FOTerm) : bool :=
  (fix homemb1 (t1: FOTerm): FOTerm -> bool :=
  (fix homemb2 (t2: FOTerm): bool :=
  match t1 with 
  | FOVar _ => match t2 with | FOVar _ => true | _ => false end
  | FOFun0 f1 => match t2 with
    | FOFun0 f2 => if optionF_eq_dec f1 f2 then true else false
    | FOFun2 _ t21 t22 => orb (homemb2 t21) (homemb2 t22)
    | _ => false
    end
  | FOFun2 f1 t11 t12 => match t2 with
    | FOFun2 f2 t21 t22 => orb (if optionF_eq_dec f1 f2
        then andb (homemb1 t11 t21) (homemb1 t12 t22)
        else false) (orb (homemb2 t21) (homemb2 t22))
    | _ => false
    end
  end
  )) t1 t2.

(** printing < %\ensuremath{<}% *)

(** We can now give a formulation of Kruskal's theorem. It is 
beyond the scope of the current work to give a formal proof of this 
result, so we just take it as an assumption. *)

Theorem Kruskal: forall s: Stream FOTerm,
  exists i: nat, exists j: nat, i < j /\ homemb (s i) (s j) = true.
(* begin show *)
Admitted. 
(* end show *)

End FOTerms.

(** We mark some arguments as implicit so that they are inferred by the
Coq typechecker.*)

(* begin show *)
Implicit Arguments FOVar [V F].  Implicit Arguments FOFun0 [V F].
Implicit Arguments FOFun2 [V F]. Implicit Arguments homemb [V F].
(* end show *)

(** To use Kruskal's theorem for online termination, we need a few 
additional ingredients. Firstly, a function that actually computes (the
index of) the first of the two terms in a sequence, that are related by
homeomorphic embedding. For simplicity, we limit the search to
a finite initial fragment of the sequence and prove separately
that there is always such initial fragment
that will produce results.*)

Definition isNthEmbeddedBelow V F fn_eq_dec (n m: nat)
  (s: Stream (FOTerm V F)) : bool := 
  existsb (fun i => homemb fn_eq_dec (s n) (s i)) (seq (S n) (m - n)).
(* begin show *)
Implicit Arguments isNthEmbeddedBelow [V F].
(* end show *)

Definition firstEmbedded V F fn_eq_dec (n: nat) (s: Stream (FOTerm V F)) : option nat :=
  find (fun i => isNthEmbeddedBelow fn_eq_dec i n s) (seq 0 n).
(* begin show *)
Implicit Arguments firstEmbedded [V F].
(* end show *)

(** We use list functions from the standard library, like [existsb],
[find], [seq], with hopefully obvious meanings. Some of their useful properties
are missing from the library, and we have to
prove them first: *)

(* * %\begin{small}% *)
Lemma find_Some: forall X (f: X -> bool) x xs,
  In x xs -> f x = true -> exists y, find f xs = Some y.
Proof.
(* begin hide *)
  miniCrush. revert H H0.
  induction xs; miniCrush; eauto.
  destruct (f a); eauto.
(* end hide *)
Qed.

Lemma In_seq: forall n m l, In n (seq m l) <-> m <= n < m + l.
Proof.
(* begin hide *)
  intros. split.
  revert n m.
  induction l; miniCrush; apply IHl in H0; miniCrush.

  revert n m.
  induction l; miniCrush.
  inversion H0; miniCrush.
(* end hide *)
Qed.
(* * %\end{small}% *)

(** With these properties in addition to Kruskal's theorem, we easily establish
that [firstEmbedded] is total.
*)

Theorem firstEmbedded_total: forall V F F_eq_dec (s: Stream (FOTerm V F)), 
  exists n, exists m, firstEmbedded F_eq_dec n s = Some m.
Proof.
(* begin hide *)
  unfold firstEmbedded. unfold isNthEmbeddedBelow.
  miniCrush.
  generalize (Kruskal V F F_eq_dec s). miniCrush.
  exists (x0).
  apply find_Some with (x:=x).
  apply <- In_seq. miniCrush.
  rewrite existsb_exists.
  exists x0. split.
  apply <- In_seq. miniCrush.
  assumption.
(* end hide *)
Qed.

(** Another helper function we need is an injection from simple expressions into
first-order terms. We first define an enumeration of the constructors of expressions,
together with their decidable equality predicate. Then the definition of the
injection is straightforward.
*)

Inductive TrmCons: Set := | TCNil | TCCons | TCSelHd 
  | TCSelTl | TCId | TCCmp | TCIfNil | TCBottom.

Definition TrmCons_eq_dec (t1 t2: TrmCons) : {t1 = t2} + {t1 <> t2}.
(* begin show *)
  decide equality.
(* end show *)
Defined.

Fixpoint TrmToFOTerm (e: Trm) : FOTerm Empty_set TrmCons :=
  match e with
  | Nil => FOFun0 (Some TCNil)
  | Cons e1 e2 => FOFun2 (Some TCCons) 
      (TrmToFOTerm e1) (TrmToFOTerm e2)
  | Sel sel => if sel then FOFun0 (Some TCSelHd) 
       else FOFun0 (Some TCSelTl)
  | Id => FOFun0 (Some TCId)
  | Cmp e1 e2 => FOFun2 (Some TCCmp) 
      (TrmToFOTerm e1) (TrmToFOTerm e2)
  | IfNil e1 e2 e3 => FOFun2 (Some TCIfNil) (TrmToFOTerm e1) 
      (FOFun2 (Some TCCons) (TrmToFOTerm e2) (TrmToFOTerm e3))
  | Bottom => FOFun0 (Some TCBottom)
  end.

(** ** Simple Supercompiler using Loop Unrolling %\label{subsec:sscp}%

Now we can assemble all previously defined components into a finished basic supercompiler.
It first builds a stream of iterated unrollings of the program in KNF. Then it
looks for pairs of initializer expressions related by homeomorphic embedding in an initial
fragment of the stream (the length of this fragment being specified by an input
parameter -- [n]). We use only initializer expressions when checking for
termination, because they are the only KNF part changed by the simple loop unrolling used here.
To aid the experimentations on practical examples, there is also an input option, 
[alwaysSome], which can be used to force a result even if no homeomorphic embedding
is found in the specified initial stream segment.
*)

Definition sscpCore (alwaysSome: bool) unroll knf2trm n (knf: KNFProg) :=
  let knfs := streamUnfold knf unroll in
  let ts := streamMap (fun knf => TrmToFOTerm (knf2trm knf)) knfs in
  match firstEmbedded TrmCons_eq_dec n ts with
  | None => if alwaysSome then Some (knfs n) else None
  | Some m => Some (knfs m)
  end.

Definition sscp (alwaysSome: bool) n knf := 
  sscpCore alwaysSome unrollToInit initExp n knf.

(** Alternatively, we define a cut-down version, which uses [normConv] instead of
[norm] during loop unrolling. In essence it is a simple deforestation analog of
the simple supercompiler above:
*)

Definition unrollToInit' knf :=
  let nrm t := ntrm2trm (normConv t) in
  let newInit := nrm ((IfNil (condExp knf) Id (bodyExp knf)) $ (initExp knf))
  in MkKNFProg newInit (condExp knf) (bodyExp knf) (finalExp knf).

Definition sscp' (alwaysSome: bool) n knf := 
  sscpCore alwaysSome unrollToInit' initExp n knf.

(** Now we can see both methods at work,
demonstrating the usefulness of even this limited form
of supercompilation. Consider again the usual Lisp-like encoding of booleans and
lists in the domain of binary trees. The task of checking if an input list
of booleans contains at least one false value can be performed by the 
following program:*)

Definition listHasWFalse_knf := 
  let WFalse := Nil in let WTrue := Nil # Nil in MkKNFProg
  (Id # WFalse) Hd (IfNil (Hd $ Hd) (Nil # WTrue) ((Tl $ Hd) # Tl)) Tl.

Eval compute in (KNFtoProg listHasWFalse_knf).
(**
<<
  = VAR  <- Id # Nil;
    WHILE Hd DO 
      VAR  <- IfNil (Hd $ Hd) (Nil # Nil # Nil) (Tl $ Hd # Tl)
    DONE; 
    VAR  <- Tl : SWhileStmt
>>
*)
(** A few explanations are in order. We extend the computation state with a flag to hold
the final result -- at position [Tl] -- while keeping the original input list at
position [Hd]. Then we loop while the list is not empty, and test its head.
If it is [VNil], we make the list empty to force an exit of the loop, and set the
result to true, otherwise we remove the list head and continue.

Next, we introduce a specialized version of this program, which, if the input
list is not empty, adds a negated copy of the head of the list.
The idea is clearly that this specialized version should return true on all
non-empty lists, and false only on the empty list.*)

Definition modifyKNFinput knf modifierExp :=   MkKNFProg 
  ((initExp knf) $ modifierExp) (condExp knf) (bodyExp knf) (finalExp knf).

Definition listHasWFalse_knf_negdupHd := 
  let WFalse := Nil in let WTrue := Nil # Nil in
  let negate x := IfNil x WTrue WFalse in  
  modifyKNFinput listHasWFalse_knf (IfNil Id Id (negate Hd # Id)).

Eval vm_compute in (match sscp false 3 listHasWFalse_knf_negdupHd with
  | Some knf => Some (KNFtoProg knf) | None => None end).
(**
<<
  = Some (VAR <- IfNil Id (Nil # Nil) 
            (IfNil Hd (Nil # Nil # Nil) (Nil # Nil # Nil));
          WHILE Hd
          DO VAR  <- IfNil (Hd $ Hd) 
            (Nil # Nil # Nil) (Tl $ Hd # Tl) 
          DONE; VAR  <- Tl) : option SWhileStmt
>>

While the resulting program may not look simplified at first, if we 
remove by hand the second if-expression with equal branches, we can see
that the loop will never be entered. The final correct result will be
computed directly by the initializer expression. The combination
of deforestation, positive information propagation and simple loop unrolling
has resulted in an almost optimal specialized program in this case.

<<
  = Some (VAR <- IfNil Id (Nil # Nil) (Nil # Nil # Nil);
          WHILE Hd
          DO VAR  <- IfNil (Hd $ Hd) 
            (Nil # Nil # Nil) (Tl $ Hd # Tl) 
          DONE; VAR  <- Tl) : option SWhileStmt
>>

In contrast, if we remove just positive information propagation from the mix,
the end result is much less satisfactory:
*)

Eval vm_compute in (match sscp' false 2 listHasWFalse_knf_negdupHd with
  | Some knf => Some (KNFtoProg knf) | None => None end).
(**
%\begin{scriptsize}%
<<
  = Some (VAR  <- IfNil Id
            (IfNil Id (IfNil Id Id (IfNil Hd (Nil # Nil) Nil # Id) # Nil)
               (IfNil Id (IfNil Hd (Nil # Nil # Nil) (IfNil Id Tl Id # Nil))
                  (IfNil Hd (IfNil Id Tl Id # Nil) (Nil # Nil # Nil))))
            (IfNil Id (IfNil Hd (Nil # Nil # Nil) (IfNil Id Tl Id # Nil))
               (IfNil Hd (IfNil Id Tl Id # Nil) (Nil # Nil # Nil)));
          WHILE Hd
          DO VAR  <- IfNil (Hd $ Hd) (Nil # Nil # Nil) (Tl $ Hd # Tl) DONE;
          VAR  <- Tl) : option SWhileStmt
>>
%\end{scriptsize}%
*)

(** ** Proof of Correctness of the Full Supercompiler %\label{subsec:sscpCorrect}%

We consider two aspects of supercompiler correctness - totality and preservation
of semantics. Totality of the supercompiler function is a direct consequence
of totality of [firstEmbedded] ([Theorem firstEmbedded_total]).
*)

(* * %\begin{small}% *)
Lemma sscpCore_total: forall b unroll knf2trm knf, exists n, exists knf1, 
  sscpCore b unroll knf2trm n knf = Some knf1.
Proof.
(* begin hide *)
  unfold sscpCore. intros. 
  match goal with [|- context [firstEmbedded ?X _ ?Y]]
    => generalize (firstEmbedded_total _ _ X Y) end.
  miniCrush. 
  exists x.
  match goal with [ |- context [match ?X with
    | Some _ => _ | None => _ end] ] 
    => destruct X as [?|] _eqn: optEqn end;
  miniCrush. eauto.
(* end hide *)
Qed.
(* * %\end{small}% *)

Hint Resolve sscpCore_total.

Theorem sscp_total: forall b knf, exists n, exists knf1, sscp b n knf = Some knf1.
Proof.
  unfold sscp. miniCrush.
Qed.

(** Preservation of semantics, on the other hand, is established through a 
sequence of lemmas, essentially relying only on correctness of one-step
loop unrolling ([evalKNF_unrollToInit]). We can say that we have
achieved one of the main goals of this study - maximum modularity
in proving different aspects of supercompiler correctness. *)

(* * %\begin{small}% *)
Lemma condExp_unrollToInitStream: forall knf n,
  condExp (streamUnfold knf unrollToInit n) = condExp knf.
Proof.
(* begin hide *)
  induction n; miniCrush.
(* end hide *)
Qed.

Hint Rewrite condExp_unrollToInitStream : miniCrushDb.

Lemma unrollToInitStream_evalKNF_fw: forall knf v1 v2 n d1,
  strictTrm (condExp knf) -> evalKNF d1 knf v1 = Some v2 -> 
  exists d2, evalKNF d2 (streamUnfold knf unrollToInit n) v1 = Some v2.
Proof.
(* begin hide *)
  unfold strictTrm.
  miniCrush.
  revert d1 knf v1 v2 H H0.
  induction n; miniCrush; eauto.
  apply IHn in H0; miniCrush.
  apply -> evalKNF_unrollToInit; miniCrush. eauto.
(* end hide *)
Qed.

Lemma unrollToInitStream_evalKNF_bw: forall knf v1 v2 n d1, 
  strictTrm (condExp knf) -> evalKNF d1 (streamUnfold knf unrollToInit n)
  v1 = Some v2 -> exists d2, evalKNF d2 knf v1 = Some v2.
Proof.
(* begin hide *)
  unfold strictTrm.
  miniCrush.
  revert d1 knf v1 v2 H H0.
  induction n; miniCrush; eauto.
  apply evalKNF_unrollToInit_bw in H0; miniCrush.
  eauto.
(* end hide *)
Qed.

Lemma sscpCore_correct_fw: forall b knf knf1 n d1 v1 v2, strictTrm (condExp knf)
  -> sscpCore b unrollToInit initExp n knf = Some knf1 ->
  evalKNF d1 knf v1 = Some v2 -> exists d2, evalKNF d2 knf1 v1 = Some v2.
Proof.
(* begin hide *)
  unfold strictTrm.
  unfold sscpCore. miniCrush.
  match goal with [ H: context [match ?X with
    | Some _ => _ | None => _ end] |- _ ] 
    => destruct X (*as [?|] _eqn: optEqn*) end;
  miniCrush.
  apply unrollToInitStream_evalKNF_fw with (n:=n0) in H1; miniCrush.

  destruct b; miniCrush.
  apply unrollToInitStream_evalKNF_fw with (n:=n) in H1; miniCrush.
(* end hide *)
Qed.

Lemma sscpCore_correct_bw: forall b knf knf1 n d1 v1 v2, strictTrm (condExp knf)
  -> sscpCore b unrollToInit initExp n knf = Some knf1 ->
  evalKNF d1 knf1 v1 = Some v2 -> exists d2, evalKNF d2 knf v1 = Some v2.
Proof.
(* begin hide *)
  unfold strictTrm.
  unfold sscpCore. miniCrush.
  match goal with [ H: context [match ?X with
    | Some _ => _ | None => _ end] |- _ ] 
    => destruct X (*as [?|] _eqn: optEqn*) end;
  miniCrush.

  apply unrollToInitStream_evalKNF_bw with (n:=n0) in H1; miniCrush.

  destruct b; miniCrush.
  apply unrollToInitStream_evalKNF_bw with (n:=n) in H1; miniCrush.
(* end hide *)
Qed.

Hint Resolve sscpCore_correct_fw sscpCore_correct_bw.

Lemma sscpCore_correct: forall b knf knf1 n v1 v2, strictTrm (condExp knf)
  -> sscpCore b unrollToInit initExp n knf = Some knf1 ->
  ((exists d1, evalKNF d1 knf v1 = Some v2) <->
   (exists d2, evalKNF d2 knf1 v1 = Some v2)).
Proof.
(* begin hide *)
  miniCrush; eauto.
(* end hide *)
Qed.
(* * %\end{small}% *)

Theorem sscp_correct: forall b knf knf1 n v1 v2, 
  strictTrm (condExp knf) -> sscp b n knf = Some knf1 ->
  ((exists d1, evalKNF d1 knf v1 = Some v2) <->
   (exists d2, evalKNF d2 knf1 v1 = Some v2)).
Proof.
(* begin hide *)
  unfold sscp.
  apply sscpCore_correct; miniCrush.
(* end hide *)
Qed.



(* * * Conclusions - in main TeX file *)