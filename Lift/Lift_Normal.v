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
(*                   Lift Lambda Calculus                             *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation               *) 
(* of Lambda Calculus  from Project Coq                               *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                      Lift_Normal.v                                 *)
(*                                                                    *)
(*                      Barry Jay                                     *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith.
Require Import "../General".
Require Import "../Test".
Require Import Lift_Terms.
Require Import Lift_Tactics.
Require Import Lift_reduction.




(* normal terms *) 

Inductive normal : lambda -> Prop := 
| nf_ref : forall n, normal (Ref n)
| nf_abs : forall M, normal M -> normal (Abs M)
| nf_active : forall M1 M2, normal M1 -> normal M2 -> 
                              status (App M1 M2) = Active -> normal (App M1 M2)  
.

Hint Constructors normal. 

Definition irreducible M (red:termred) := forall N, red M N -> False. 

Lemma ref_irreducible : forall n, irreducible (Ref n) seq_red1. 
Proof. intro n. red. split_all. inversion H; auto. Qed. 

Lemma abs_irreducible : 
forall M, irreducible M seq_red1 ->  irreducible (Abs M) seq_red1. 
Proof. red; split_all. inversion H0.  eapply2 H.  Qed. 



Lemma normal_is_irreducible: 
forall M, normal M -> irreducible M seq_red1. 
Proof. 
intros M nor; induction nor; split_all.  
eapply2 ref_irreducible. 
red; split_all. inversion H. eapply2 IHnor. 
intro. intro. inversion H0; subst; simpl in *; try discriminate. 
(* 2 *) 
eapply2 IHnor1. 
(* 1 *) 
eapply2 IHnor2. 
Qed. 

(* 
The basic progress result, that all irreducible terms are normal.
 *) 

Lemma beta_normal: forall M N, normal M -> exists P, seq_red1 (App (Abs M) N) P. 
Proof. 
induction M; split_all; eauto.  
(* 3 *) 
case n; split_all; eauto. 
(* 2 *)
inversion H; eauto.  
(* 1 *) 
inversion H; eauto.  
Qed. 


Lemma Lift_normal: forall M, normal M -> forall k, exists N, seq_red1 (Lift k M) N. 
Proof. 
induction M; split_all; eauto.  
(* 3 *) 
assert(n < k \/ n >= k) by omega. 
inversion H0; eauto. 
inversion H; subst. simpl in *; eauto. 
inversion H; eauto.  
Qed. 

Theorem lift_progress : forall (M : lambda), normal M \/ (exists N, seq_red1 M N) .
Proof. 
induction M; try (inversion IHM); subst; split_all; eauto.
(* 1 *)
inversion IHM1; split_all.  2: right; exist (App x M2). 
inversion IHM2; split_all.  2: right; exist (App M1 x). 
assert((status (App M1 M2) =  Active) \/ status (App M1 M2) = Passive). 
case (status (App M1 M2)); split_all. 
inversion H1; split_all.
inversion H2. 
gen2_case H H4 M1. inversion H; subst.  simpl in *. rewrite H4 in H8; discriminate. 
inversion H; subst. right. eapply2 beta_normal. 
inversion H; subst. 
(* 1 *)
right. eapply2 Lift_normal.   
Qed. 

Lemma irreducible_is_normal: 
forall M, irreducible M seq_red1 -> normal M. 
Proof. split_all. elim(lift_progress M); split_all. assert False by eapply2 H; noway. Qed. 

Theorem irreducible_iff_normal: forall M, irreducible M seq_red1 <-> normal M. 
Proof. split_all. eapply2 irreducible_is_normal. eapply2 normal_is_irreducible. Qed. 

Corollary normal_decidable: forall M, normal M \/ not (normal M). 
Proof. 
induction M; split_all.
(* 3 *) 
inversion IHM1. inversion IHM2.
(* 5 *)  
gen_case H M1.  
inversion H; left; eapply2 nf_active. 
right. intro. inversion H1; simpl in *. discriminate. 
inversion H; left; eapply2 nf_active. 
(* 4 *) 
right; intro. inversion H1. eapply2 H0. 
(* 3 *) 
right; intro. inversion H0. eapply2 H. 
(* 2 *) 
assert(normal M \/ exists N, seq_red1 M N) by  eapply2 lift_progress. 
inversion H; inversion IHM. left; auto.  assert False by eapply2 H1; noway. 
split_all. split_all. right.  intro. inversion H0.  
assert(irreducible M seq_red1) by eapply2 normal_is_irreducible. 
eapply2 H5. 
(* 1 *) 
right;  intro; inversion H; auto. 
Qed. 
