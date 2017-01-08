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
(*               Intensional Lambda Calculus                          *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation               *) 
(* of Lambda Calculus from Project Coq                                *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                   LamSF_Closed.v                                   *)
(*                                                                    *)
(*                      Barry Jay                                     *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith.
Require Import Test.
Require Import General. 
Require Import Max. 
Require Import SF_Terms.
Require Import SF_Tactics.
Require Import Substitution_term. 
Require Import SF_reduction.
Require Import SF_Normal.

(* closed terms *) 


Fixpoint maxvar (M: SF) := 
match M with 
| Ref i => S i
| Op o  => 0
| App M1 M2 => max (maxvar M1) (maxvar M2)
end.

Lemma lift_rec_closed: forall M n k, maxvar M = 0 -> lift_rec M n k = M. 
Proof. induction M; split_all. max_out. rewrite IHM1; auto;  rewrite IHM2; auto. Qed. 

Lemma subst_rec_closed: forall M N k, maxvar M <= k -> subst_rec M N k = M. 
Proof. 
induction M; split_all. 
unfold insert_Ref. elim(compare k n); split_all. elim a; split_all. noway. noway. 
assert (max (maxvar M1) (maxvar M2) >= maxvar M1) by eapply2 max_is_max. 
assert (max (maxvar M1) (maxvar M2) >= maxvar M2) by eapply2 max_is_max. 
rewrite IHM1; try omega;  rewrite IHM2; try omega. auto. 
Qed. 


Lemma subst_decreases_maxvar : 
forall M N,  max (pred (maxvar M)) (maxvar N) >= maxvar(subst M N).
Proof. 
unfold subst; induction M; split_all. 
unfold insert_Ref. 
case n; split_all. unfold lift. rewrite lift_rec_null_term. auto.
case (maxvar N); split_all. 
assert(max n0 n1  >= n0) by eapply2 max_is_max. 
omega. 
omega. 
(* 1 *) 
rewrite max_pred.
assert(max (max (pred (maxvar M1)) (pred (maxvar M2))) (maxvar N) >=
max (pred (maxvar M1)) (maxvar N)).
eapply2 max_monotonic. eapply2 max_is_max. 
assert(max (max (pred (maxvar M1)) (pred (maxvar M2))) (maxvar N) >=
max (pred (maxvar M2)) (maxvar N)).
eapply2 max_monotonic. eapply2 max_is_max. 
assert(max (max (pred (maxvar M1)) (pred (maxvar M2))) (maxvar N) >=
max(max (pred (maxvar M1)) (maxvar N)) (max (pred (maxvar M2)) (maxvar N))).
eapply2 max_max2. 
assert(max (max (pred (maxvar M1)) (maxvar N))
         (max (pred (maxvar M2)) (maxvar N))>= 
max (maxvar (subst_rec M1 N 0)) (maxvar (subst_rec M2 N 0))).
eapply2 max_monotonic. 
omega. 
Qed. 


Definition decreases  (rank: SF -> nat) (red:termred):= 
forall M N, red M N -> rank M >= rank N.

Lemma decreases_multi_step: 
forall rank red, decreases rank red -> decreases rank (multi_step red). 
Proof. 
red. intros rank red D M N R;  induction R; split_all. 
assert(rank M >= rank N) by eapply2 D. 
assert(rank N >= rank P) by eapply2 IHR. 
omega. 
Qed. 


Lemma subst_closed : forall M, maxvar M = 0 -> forall N, subst M N = M.
Proof.
induction M; split_all; subst.
max_out. unfold subst in *; simpl. rewrite IHM1; try omega; rewrite IHM2; try omega; split_all. 
Qed. 

Lemma left_component_preserves_maxvar : forall M, compound M -> 
maxvar(left_component M) <= maxvar M. 
Proof. 
split_all.
inversion H; split_all; try omega. 
eapply2 max_is_max.
Qed. 


Lemma right_component_preserves_maxvar : forall M, compound M -> 
maxvar(right_component M) <= maxvar M. 
Proof. split_all. inversion H; split_all; try omega. eapply2 max_is_max. 
Qed. 

Ltac max_l := 
match goal with 
| |- max ?m ?n >= ?p => 
assert(max m n >= m) by eapply2 max_is_max; 
cut(m >= p); split_all; try omega
end. 
Ltac max_r := 
match goal with 
| |- max ?m ?n >= ?p => 
assert(max m n >= n) by eapply2 max_is_max; 
cut(n >= p); split_all; try omega
end. 

Lemma closed_implies_passive : forall M, maxvar M = 0 -> status M = Passive. 
Proof. 
rank_tac. 
induction M; split_all; try omega.  clear IHM1 IHM2. 
generalize H H0; case M1; clear H H0; intros; try (auto; omega). 
simpl in *. gen_case H0 (maxvar M2). 
generalize H H0; case s; clear H H0; intros; try (auto; omega). 
simpl in *. gen_case H0 (maxvar s0); gen_case H0 (maxvar M2);    omega. 
generalize H H0; case s1; clear H H0; intros; try (auto; omega). 
simpl in *.  
gen_case H0 (maxvar s2); gen_case H0 (maxvar s0); gen_case H0 (maxvar M2).     
gen_case H o. 
eapply2 IHp.  omega. 
simpl in *. 
assert( max (max (maxvar s2) (maxvar s0)) (maxvar M2) >= maxvar s2). 
max_l. max_l. omega. 
eapply2 IHp. omega. 
assert(max (maxvar (App (App (App s3 s4) s2) s0)) (maxvar M2) >= 
maxvar (App (App (App s3 s4) s2) s0)) by max_l. omega. 
Qed. 

Lemma decreases_maxvar_sf_seqred1: decreases maxvar sf_seqred1.
(* 
forall M N, lamF_red1 M N -> maxvar N <= maxvar M. 
*) 
Proof. 
cut(forall M N, sf_seqred1 M N -> maxvar N <= maxvar M). 
split_all; red. 

intros M N R; induction R; split_all; eauto; try (repeat (eapply2 max_monotonic); fail); try omega; repeat (eapply2 max_max2); try (max_r; fail); try (repeat max_l; fail). 
(* 5 *) 
assert(max(maxvar M) (maxvar N) >= maxvar N) by max_r. 
assert(max (max (maxvar M) (maxvar N)) (maxvar P) >= (max (maxvar M) (maxvar N))) by max_l. 
omega. 
assert(max(maxvar M) (maxvar N) >= maxvar M) by max_l. omega. 
(* 2 *) 
max_l. max_l. eapply2 left_component_preserves_maxvar.
max_l. max_l. eapply2 right_component_preserves_maxvar.
Qed. 

Lemma decreases_maxvar_lamF_red : decreases maxvar sf_seqred.
Proof. eapply2 decreases_multi_step. eapply2 decreases_maxvar_sf_seqred1. Qed. 


Definition program M := normal M /\ maxvar M = 0. 



Lemma components_monotonic: 
forall M N, program M -> program N ->  
left_component M = left_component N -> 
right_component M = right_component N -> M = N. 
Proof. 
induction M; unfold program; split_all. 
(* 3 *) 
gen4_case H1 H2 H3 H4 N; try discriminate.  
subst. simpl in *. unfold abs_left in *. unfold s_op in *. inversion H3. simpl in *. discriminate. inversion H7. 
(* 1 *) 
subst. 
gen_case H0 N. unfold abs_left in *. unfold s_op in *. inversion H0. discriminate.  inversion H7. 
unfold abs_left in *. unfold s_op in *. inversion H0. discriminate.  inversion H7. 
Qed. 


Definition factorable M := (exists o, M = Op o) \/ compound M.

Theorem programs_are_factorable : forall M, program M  -> factorable M. 
Proof. 
rank_tac. 
unfold program, factorable; induction M;  split_all; eauto.  
right. 
assert((exists o : operator, M1 = Op o) \/ compound M1). eapply2 IHM1. 
omega. 
split_all. inversion H1; auto. 
assert(max(maxvar M1) (maxvar M2) >= maxvar M1) by max_l. omega. 
inversion H0; split_all; subst; eauto. 
inversion H3; subst; split_all. gen_case H1 o. inversion H1.  discriminate. inv1 compound. 
inversion H1; try inv1 compound; subst. 
inversion H8. 
assert(status M = Passive). eapply2 closed_implies_passive. 
simpl in *. 
assert(max (max (maxvar M) (maxvar N)) (maxvar M2) >= maxvar M). 
max_l. max_l. omega. 
rewrite H4 in H3; discriminate. 
Qed. 

