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
(*                   SF-Calculus                                      *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *)
(* Lambda Calculus from Project Coq                                   *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                   SF_tactics.v                                     *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith.
Require Import Test. 
Require Import General.
Require Import SF_Terms. 

Definition termred := SF -> SF -> Prop.

Definition preserve (R : termred) (P : SF -> Prop) :=
  forall x : SF, P x -> forall y : SF, R x y -> P y.


Inductive multi_step : termred -> termred :=
  | zero_red : forall red M, multi_step red M M
  | succ_red : forall (red: SF-> SF -> Prop) M N P, 
                   red M N -> multi_step red N P -> multi_step red M P
.

Inductive sequential : termred -> termred -> termred :=
  | seq_red : forall (red1 red2 : termred) M N P, 
                red1 M N -> red2 N P -> sequential red1 red2 M P.

Hint Resolve zero_red succ_red seq_red
.

Definition reflective red := forall (M: SF), red M M.

Lemma refl_multi_step : forall (red: termred), reflective (multi_step red).
Proof. red; split_all. Qed.

Lemma refl_seq : forall (red1 red2: termred),
                   reflective red1 -> reflective red2 -> reflective(sequential red1 red2).
Proof. red; split_all; eapply2 seq_red. Qed.


Ltac reflect := match goal with 
| |- reflective (multi_step _) => eapply2 refl_multi_step
| |- multi_step _ _ _ => try (eapply2 refl_multi_step)
| |- reflective (sequential _) => eapply2 refl_seq; reflect 
| |- sequential _ _ _ _ => try (eapply2 refl_seq)
| _ => split_all
end.


Ltac one_step := 
match goal with 
| |- multi_step _ _ ?N => apply succ_red with N; auto; try red; try reflect
end.

Ltac seq_l := 
match goal with 
| |- sequential _ _ ?M ?N => apply seq_red with N; auto; red; reflect
end.

Ltac seq_r := 
match goal with 
| |- sequential _ _ ?M ?N => apply seq_red with M; auto; red; reflect
end.


Definition transitive red := forall (M N P: SF), red M N -> red N P -> red M P. 

Lemma transitive_red : forall red, transitive (multi_step red). 
Proof. red; induction 1; split_all. 
apply succ_red with N; auto. 
Qed. 


Definition preserves_app (red : termred) := 
forall M M' N N', red M M' -> red N N' -> red (App M N) (App M' N').


Lemma preserves_app_multi_step : forall (red: termred), reflective red -> preserves_app red -> preserves_app (multi_step red). 
Proof.
red. induction 3; split_all. generalize H0; induction 1. 
reflect. 
apply succ_red with (App M N); auto.
assert( transitive (multi_step red)) by eapply2 transitive_red.  
apply X0 with (App N0 N); auto. 
one_step. 
Qed.

Lemma preserves_app_seq : forall (red1 red2: termred), preserves_app red1 -> preserves_app red2 -> preserves_app (sequential red1 red2). 
Proof.
red; split_all. 
inversion H1; inversion H2.
apply seq_red with (App N0 N1); auto.
Qed.

Hint Resolve preserves_app_multi_step preserves_app_seq .


Ltac eelim_for_equal := 
match goal with 
| H: forall _, _ = _ -> _  |- _ => eelim H; clear H; subst; eelim_for_equal
| _ => split_all 
end. 

Ltac inv1 prop := 
match goal with 
| H: prop (Ref _) |- _ => inversion H; clear H; inv1 prop
| H: prop (App  _ _) |- _ => inversion H; clear H; inv1 prop
| H: prop Op _ |- _ => inversion H; clear H; inv1 prop
| _ => split_all
 end.


Definition implies_red (red1 red2: termred) := forall M N, red1 M N -> red2 M N. 

Lemma implies_red_multi_step: forall red1 red2, implies_red red1  (multi_step red2) -> 
                                                implies_red (multi_step red1) (multi_step red2).
Proof. red. 
intros red1 red2 IR M N R; induction R; split_all. 
apply transitive_red with N; auto. 
Qed. 
Lemma implies_red_seq: 
 forall red1 red2 red3, 
  implies_red red1  (multi_step red3)  ->  
  implies_red red2 (multi_step red3) -> 
  implies_red (sequential red1 red2) (multi_step red3) .
Proof. 
red; split_all. inversion H1. apply transitive_red with N0; auto. 
Qed. 


Definition subst_preserves_l (red: termred) := 
forall (M M' N : SF), red M M' -> red  (subst M N) (subst M' N).

Definition subst_preserves_r (red: termred) := 
forall (M N N' : SF), red N N' -> red  (subst M N) (subst M N').

Definition subst_preserves (red: termred) := 
forall (M M' : SF), red M M' -> forall N N', red N N' -> 
red  (subst M N) (subst M' N').

Lemma subst_preserves_l_multi_step : 
forall (red: termred), subst_preserves_l red -> subst_preserves_l (multi_step red). 
Proof. unfold subst_preserves_l. 
 induction 2; split_all.  
apply succ_red with (subst N0 N); auto.
Qed.

Lemma subst_preserves_r_multi_step : 
forall (red: termred), subst_preserves_r red -> subst_preserves_r (multi_step red). 
Proof. unfold subst_preserves_r. 
 induction 2; split_all.  
apply succ_red with (subst M N); auto.
Qed. 

Lemma subst_preserves_multi_step : 
forall (red: termred), subst_preserves_l red -> subst_preserves_r red -> subst_preserves (multi_step red). 
Proof. 
unfold subst_preserves. split_all.
assert(transitive (multi_step red)) by eapply2 transitive_red. 
unfold transitive in *.
apply X with  (subst M' N); auto. 
eapply2 subst_preserves_l_multi_step.
eapply2 subst_preserves_r_multi_step.
Qed.



Ltac inv red := 
match goal with 
| H: multi_step red (App _ _) _ |- _ => inversion H; clear H; inv red
| H: multi_step red (Ref _) _ |- _ => inversion H; clear H; inv red
| H: multi_step red (Op _) _ |- _ => inversion H; clear H; inv red
| H: red (Ref _) _ |- _ => inversion H; clear H; inv red
| H: red (App _ _) _ |- _ => inversion H; clear H; inv red
| H: red (Op _) _ |- _ => inversion H; clear H; inv red
| H: multi_step red _ (Ref _) |- _ => inversion H; clear H; inv red
| H: multi_step red _ (App _ _) |- _ => inversion H; clear H; inv red
| H: multi_step red _ (Op _) |- _ => inversion H; clear H; inv red
| H: red _ (Ref _) |- _ => inversion H; clear H; inv red
| H: red _ (App _ _) |- _ => inversion H; clear H; inv red
| H: red _ (Op _) |- _ => inversion H; clear H; inv red
| _ => subst; split_all 
 end.



Definition diamond (red1 red2 : termred) := 
forall M N, red1 M N -> forall P, red2 M P -> exists Q, red2 N Q /\ red1 P Q. 

Lemma diamond_flip: forall red1 red2, diamond red1 red2 -> diamond red2 red1. 
Proof. unfold diamond; split_all. elim (H M P H1 N H0); split_all. exist x. Qed.

Lemma diamond_strip : 
forall red1 red2, diamond red1 red2 -> diamond red1 (multi_step red2). 
Proof. intros. 
eapply2 diamond_flip. 
red; induction 1; split_all.
exist P.
elim (H M P0 H2 N); split_all. 
elim(IHmulti_step H x); split_all. 
exist x0.
apply succ_red with x; auto. 
Qed. 


Definition diamond_star (red1 red2: termred) := forall  M N, red1 M N -> forall P, red2 M P -> 
  exists Q, red1 P Q /\ multi_step red2 N Q. 

Lemma diamond_star_strip: forall red1 red2, diamond_star red1 red2 -> diamond (multi_step red2) red1 .
Proof. 
red. induction 2; split_all. 
exist P.
elim(H M P0 H2 N H0); split_all. 
elim(IHmulti_step H x); split_all. 
exist x0.
apply transitive_red with x; auto. 
Qed. 

Lemma diamond_tiling : 
forall red1 red2, diamond red1 red2 -> diamond (multi_step red1) (multi_step red2).
Proof. 
red.  induction 2; split_all.
exist P.
elim(diamond_strip red red2 H M N H0 P0); split_all.
elim(IHmulti_step H x H4); split_all.
exist x0.
apply succ_red with x; auto.
Qed. 

Hint Resolve diamond_tiling. 

Lemma diamond_seq: forall red red1 red2, diamond red red1 -> diamond red red2 -> diamond red (sequential red1 red2). 
Proof. unfold diamond; split_all. 
inversion H2. 
elim(H M N H1 N0); split_all.
elim(H0 N0 x H11 P); split_all.
exist x0. 
apply seq_red with x; auto. 
Qed.

Lemma relocate_null :
forall (n n0 : nat), relocate n n0 0 = n.
Proof. split_all. unfold relocate. case (test n0 n); intro; auto with arith. Qed.

Lemma relocate_lessthan : forall m n k, m<=k -> relocate k m n = (n+k). 
Proof. split_all. unfold relocate. elim(test m k); split_all; try noway. Qed. 
Lemma relocate_greaterthan : forall m n k, m>k -> relocate k m n = k. 
Proof. split_all. unfold relocate. elim(test m k); split_all; try noway. Qed. 

Ltac relocate_lt := 
try (rewrite relocate_lessthan; [| omega]; relocate_lt); 
try (rewrite relocate_greaterthan; [| omega]; relocate_lt);
try(rewrite relocate_null). 


Lemma relocate_zero_succ :
forall n k, relocate 0 (S n) k = 0.
Proof.  split_all. Qed.

Lemma relocate_succ :
forall n n0 k, relocate (S n) (S n0) k = S(relocate n n0 k).
Proof. 
intros; unfold relocate. elim(test(S n0) (S n)); elim(test n0 n); split_all. 
noway. 
noway. 
Qed. 

Lemma relocate_mono : forall M N n k, relocate M n k = relocate N n k -> M=N. 
Proof. 
intros M N n k. 
unfold relocate.
elim(test n M); elim(test n N); split_all; omega. 
Qed. 



Fixpoint rank (M: SF) := 
match M with 
| Ref _ => 1
| Op _ => 1
| App M1 M2 => S((rank M1) + (rank M2))
end.

Lemma rank_positive: forall M, rank M > 0. 
Proof. 
induction M; split_all; try omega. 
Qed. 



Ltac rank_tac := match goal with 
| |- forall M, ?P  => 
cut (forall p M, p >= rank M -> P ); [ intros H M;  eapply2 H | 
intro p; induction p; intro M;  [ assert(rank M >0) by eapply2 rank_positive; noway |]
]
end .

