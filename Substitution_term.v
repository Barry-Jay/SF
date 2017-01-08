(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(**********************************************************************)
(*                      SF-Calculus                                   *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *) 
(* Lambda Calculus from Project Coq                                   *) 
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                   Substitution_term.v                              *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(* adapted from Substitution.v of Project Coq  to act on boa-terms    *)
(**********************************************************************)

Require Import Arith.
Require Import Test.
Require Import General.
Require Import SF_Terms.
Require Import SF_Tactics.


(* Lifting lemmas *)

Lemma lift_rec_null_term : 
forall (U : SF)(n: nat), lift_rec U n 0 = U.
Proof. 
simple induction U; split_all.  
relocate_lt; auto.
Qed.

Lemma lift1 :
 forall (U : SF) (j i k : nat),
 lift_rec (lift_rec U i j) (j + i) k = lift_rec U i (j + k).
Proof.
simple induction U; simpl in |- *;  split_all. 
unfold relocate. 
elim (test i n); elim (test (j+i) (j+ n)); split_all; try noway. 
assert(k + (j + n) = j + k + n) by omega. congruence. 
elim (test (j + i) n); split_all; try noway. 
Qed. 

Lemma lift_lift_rec :
 forall (U : SF) (k p n i : nat),
 i <= n ->
 lift_rec (lift_rec U i p) (p + n) k = lift_rec (lift_rec U n k) i p.
Proof.
simple induction U; simpl in |- *;  split_all.
(* Ref *) 
unfold relocate.
elim(test i n); split_all; try noway. 
elim(test n0 n); split_all; try noway. 
elim(test (p+n0) (p+n)); split_all; try noway. 
elim(test i (k+n)); split_all; try noway. 
assert(k+(p+n) = p+ (k+n)) by omega. 
rewrite H0; auto. 
elim(test (p+n0) (p+n)); split_all; try noway. 
elim(test i n); split_all; try noway. 
elim(test n0 n); split_all; try noway. 
elim(test (p+n0) n); split_all; try noway. 
elim(test i n); split_all; try noway. 
(* Ap *)
rewrite H; split_all.  rewrite H0; split_all. 
Qed. 


Lemma lift_lift_term :
 forall (U : SF) (k p n : nat),
 lift_rec (lift p U) (p+ n) k = lift p (lift_rec U n k).
Proof.
unfold lift in |- *; intros; apply lift_lift_rec; trivial with arith.
Qed.

Lemma liftrecO : forall (U : SF) (n : nat), lift_rec U n 0 = U.
Proof.
simple induction U; simpl in |- *; intros; split_all; relocate_lt; congruence. 
Qed.

Lemma liftO : forall (U : SF) , lift 0 U = U.
Proof.
unfold lift in |- *; split_all; apply liftrecO.
Qed.

Lemma lift_rec_lift_rec :
 forall (U : SF) (n p k i : nat),
 k <= i + n ->
 i <= k -> lift_rec (lift_rec U i n) k p = lift_rec U i (p + n).

Proof.
simple induction U; split_all.
(* Ref *) 
unfold relocate. 
elim(test i n); split_all; try noway. 
elim(test k (n0 + n)); split_all; try noway. 
replace (p+(n0+n)) with (p + n0 + n) by omega. auto. 
elim(test k n); split_all; try noway. 
(* Ap *)
rewrite H; split_all; rewrite H0; split_all; split_all.
Qed. 

Lemma lift_rec_lift :
 forall (U : SF)  (n p k i : nat),
 k <= n -> lift_rec (lift  n U)  k p = lift (p + n) U.
Proof.
unfold lift in |- *; intros; rewrite lift_rec_lift_rec; trivial with arith.
Qed.



Lemma gt_plus : forall i m n : nat, i>m+n -> i> n.
Proof.
induction m.
simpl; tauto.
intros; apply (IHm); auto with arith.
Qed.

Lemma le_plus : forall i m n : nat, i +m <= n -> i<= n.
Proof.
induction m; intros. 
elim H;  auto with arith.
apply (IHm). 
apply le_trans with (i+S m).
auto with arith. trivial.

Qed.


Ltac lrlr_absurd p k n := 
absurd (p+S k> S n); [
apply le_not_gt;
replace (p+ S k) with (S (p+k)); auto with arith | trivial].


(* The three cases of substitution of U for (Ref n) *)

Lemma subst_eq :
 forall (M U : SF) (n : nat), subst_rec (Ref n) U n = lift n U. 
Proof.
simpl in |- *; unfold insert_Ref in |- *; split_all. 
elim (compare n n); intro P; try noway. 
elim P; intro Q; simpl in |- *; trivial with arith; try noway.
Qed.

Lemma subst_gt :
 forall (M U : SF) (n p : nat),
 n > p -> subst_rec (Ref n) U p = Ref (pred n).
Proof.
simpl in |- *; unfold insert_Ref in |- *.
intros; elim (compare p n); intro P.
elim P; intro Q; trivial with arith.
absurd (n > p); trivial with arith; rewrite Q; trivial with arith.
absurd (n > p); auto with arith.
Qed. 

Lemma subst_lt :
 forall (M U : SF) (n p : nat), p > n -> subst_rec (Ref n) U p = Ref n.
Proof.
simpl in |- *; unfold insert_Ref in |- *.
intros; elim (compare p n); intro P; trivial with arith.
absurd (p > n); trivial with arith; elim P; intro Q; auto with arith.
rewrite Q; trivial with arith.
Qed.

(* Substitution lemma *)

Lemma lift_rec_subst_rec :
 forall (V U : SF) (k p n : nat),
 lift_rec (subst_rec V U p) (p + n) k =
 subst_rec (lift_rec V (S (p + n)) k) (lift_rec U n k) p.
Proof.
simple induction V; split_all. 
(* 1 Ref *)
unfold insert_Ref, relocate in |- *.
elim (test (S(p + n0)) n); elim (compare p n); split_all.
elim a; elim(compare p (k+n)); split_all. 
unfold relocate. 
elim(test (p+n0) (pred n)); elim a1; split_all; try noway. 
replace (k + pred n) with (pred (k + n)) by omega; auto.
noway. 
noway. 
noway. 
noway. 
elim a; split_all.
unfold relocate. elim(test(p+n0) (pred n)); split_all. 
noway.
unfold lift.
rewrite lift_lift_rec; auto; omega. 
unfold relocate. 
elim(test (p+n0) n); split_all. 
noway.
Qed. 


Lemma lift_subst :
 forall (U V : SF) (k n : nat),
 lift_rec (subst U V) n k =
 subst (lift_rec U (S n) k) (lift_rec V n k).
Proof.
unfold subst in |- *; intros.
replace n with (0 + n).
rewrite lift_rec_subst_rec; trivial with arith.
auto. 
Qed.

Lemma subst_rec_lift_rec1 :
 forall (U V : SF) (n p k : nat),
 k <= n ->
 subst_rec (lift_rec U k p) V (p + n) =
 lift_rec (subst_rec U V n) k p.
Proof.
simple induction U; intros; simpl in |- *; split_all.
(* Ref *) 
unfold insert_Ref, relocate. 
elim(test k n); split_all. 
elim(compare n0 n); split_all; try noway. 
elim a0; split_all; try noway. 
elim(compare (p+n0) (p+n)); split_all. 
elim a2; split_all; try noway. 
unfold relocate. 
elim(test k (pred n)); split_all; try noway. 
assert(pred (p+n) = p + pred n) by omega. auto. 
noway. 
elim(compare (p+n0) (p+n)); split_all. 
elim a1; split_all; try noway. 
unfold lift. rewrite lift_rec_lift_rec; split_all; try omega.  
unfold lift. rewrite lift_rec_lift_rec; split_all; try omega.  
elim(compare (p+n0) (p+n)); split_all. 
elim a0; split_all; try noway. 
unfold relocate. 
elim(test k n); split_all; try noway. 
elim(compare (p+n0) n); split_all; try noway. 
elim a; split_all; try noway. 
elim(compare n0 n); split_all; try noway. 
elim a; split_all; try noway. 
unfold relocate. 
elim(test k n); split_all; try noway. 
(* 1 *) 
rewrite H; split_all.  rewrite H0; split_all. 
Qed. 

Lemma subst_rec_lift1 :
 forall (U V : SF) (n p : nat),
 subst_rec (lift p U) V (p + n) = lift p (subst_rec U V n).
Proof.
unfold lift in |- *; intros; rewrite subst_rec_lift_rec1;
 trivial with arith.
Qed.


Lemma subst_rec_lift_rec :
 forall (U V : SF) (p q n : nat),
 q <= p + n ->
 n <= q -> subst_rec (lift_rec U n (S p)) V q = lift_rec U n p.
Proof.
simple induction U; intros; simpl in |- *; split_all. 
unfold relocate. elim(test n0 n); split_all. 
unfold insert_Ref. 
elim(compare q (S(p+n))); split_all; try noway. 
elim a0; split_all; try noway. 
unfold insert_Ref. 
elim(compare q n); split_all; try noway. 
elim a; split_all; try noway. 

(* 1 *) 
rewrite H; split_all. 
rewrite H0; auto.
Qed.

(* subst_rec_subst_rec *)

Lemma subst_rec_subst_rec :
 forall (V U W : SF) (n p : nat),
 subst_rec (subst_rec V U p) W (p + n) =
 subst_rec (subst_rec V W (S (p + n))) (subst_rec U W n) p.
Proof.
simple induction V;  split_all.

unfold insert_Ref in |- *.
elim (compare p n); split_all. 
elim a; split_all. 
elim (compare (S (p + n0)) n); split_all. 
elim a1; split_all; try noway. 
unfold insert_Ref.
elim (compare (p+n0) (pred n)); split_all; try noway. 
elim a3; split_all; try noway.
elim (compare p (pred n)); split_all; try noway. 
elim a5; split_all; try noway.
unfold lift; split_all. 
unfold insert_Ref. 
elim (compare (p+n0) (pred n)); split_all; try noway. 
elim a2; split_all; try noway.
subst. unfold lift. 
rewrite subst_rec_lift_rec; split_all; try omega. 
unfold insert_Ref. 
elim(compare (p+n0) (pred n)); split_all; try noway. 
elim a1; split_all; try noway. 
elim(compare p n); split_all; try noway. 
elim a1; split_all; try noway. 
elim (compare (S (p + n0)) n); split_all; try noway. 
elim a0; split_all; try noway.
unfold insert_Ref. 
elim(compare p n); split_all; try noway. 
elim a0; split_all; try noway. 
unfold lift. 
subst. 
rewrite subst_rec_lift_rec1; split_all.  omega. 

unfold insert_Ref. 
elim(compare (p+n0) n); split_all; try noway. 
elim a; split_all; try noway.
elim(compare (S(p+n0)) n); split_all; try noway. 
elim a; split_all; try noway. 
unfold insert_Ref. 
elim(compare p n); split_all; try noway. 
elim a; split_all; try noway. 
Qed.


Lemma subst_rec_subst_0 :
 forall (U V W : SF) (n : nat),
 subst_rec (subst_rec V U 0) W n =
 subst_rec (subst_rec V W (S n)) (subst_rec U W n) 0.
Proof.
intros; pattern n at 1 3 in |- *.
replace n with (0 + n) by trivial with arith.
rewrite (subst_rec_subst_rec V U W n 0); trivial with arith.
Qed.

(**************************)
(* The Substitution Lemma *)
(**************************)

Lemma substitution :
 forall (U V W : SF) (n : nat),
 subst_rec (subst U V) W n =
 subst (subst_rec U W (S n)) (subst_rec V W n).
Proof.
unfold subst in |- *; intros; apply subst_rec_subst_0; trivial with arith.
Qed.

(* to show (\ t)0 -> t  *) 


Lemma lift_rec_null : 
forall (U : SF) (n: nat), lift_rec U n 0 = U.
Proof. simple induction U; split_all.
 rewrite relocate_null; congruence.
Qed.

Lemma subst_lift_null :
forall (W V : SF)(n : nat), subst_rec (lift_rec W n 1) V n = W.
Proof.
simple induction W; split_all. 
unfold insert_Ref. 
unfold relocate. 
elim(test n0 n); split_all. 
elim(compare n0 (S n)); split_all.
elim a0; split_all; noway. 
noway. 
elim(compare n0 n); split_all.
elim a; split_all. noway. 
noway.
Qed. 


(* more  Properties *) 

Lemma lift_rec_lift2 : 
forall M n k, lift_rec (lift 1 M) (S n) k = lift 1 (lift_rec M n k).
Proof.
split_all.
unfold lift. 
replace (S n) with (1+n) by omega.
rewrite lift_lift_rec; auto. 
omega.
Qed.

Lemma relocate_null2 :
forall n k, relocate 0 (S n) k = 0.
Proof. split_all. Qed. 

Lemma subst_rec_lift2 : 
forall M N n , subst_rec (lift 1 M) N (S n)  = lift 1 (subst_rec M N n).
Proof.
split_all.
unfold lift. 
replace (S n) with (1+n) by omega.
rewrite subst_rec_lift_rec1; auto. 
omega.
Qed.



Lemma insert_Ref_lt : forall M n k, n< k -> insert_Ref M n k = Ref n.
Proof.
induction M; unfold insert_Ref; split_all. 
elim (compare k n0); split_all. 
elim a; split_all; try noway. 
elim (compare k n); split_all. 
elim a; split_all; try noway. 
elim (compare k n); split_all. 
elim a; split_all; try noway. 
Qed. 

Lemma insert_Ref_eq : forall M n k, n= k -> insert_Ref M n k = lift k M.
Proof.
induction M; unfold insert_Ref; split_all. 
elim (compare k n0); split_all. 
elim a; split_all; try noway. 
unfold lift; unfold lift_rec. unfold relocate. elim(test 0 n); split_all; try noway. 
elim (compare k n); split_all. 
elim a; split_all; try noway. 
unfold lift; unfold lift_rec. unfold relocate. elim(test 0 n); split_all; try noway. 
elim (compare k n); split_all. 
elim a; split_all; try noway. 
noway.
Qed. 


Lemma insert_Ref_gt : forall M n k, n> k -> insert_Ref M n k = Ref (pred n).
Proof.
induction M; unfold insert_Ref; split_all. 
elim (compare k n0); split_all. 
elim a; split_all; try noway. 
noway. 
elim (compare k n); split_all. 
elim a; split_all; try noway. 
noway. 
elim (compare k n); split_all. 
elim a; split_all; try noway. 
noway.
Qed. 

Ltac insert_Ref_out := 
try (rewrite insert_Ref_lt; [|unfold relocate; split_all; omega]; insert_Ref_out); 
try (rewrite insert_Ref_eq; [|unfold relocate; split_all; omega]; insert_Ref_out); 
try (rewrite insert_Ref_gt; [|unfold relocate; split_all; omega]; insert_Ref_out); 
unfold lift; unfold lift_rec; fold lift_rec. 


Lemma fold_subst :  forall M1 M2 N, App (subst_rec M1 N 0) M2 = subst (App M1 (lift 1 M2)) N.
Proof.
  unfold subst, lift, subst_rec; split_all; fold subst_rec.
  rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null; auto.  
Qed.
