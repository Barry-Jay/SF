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
(* of Lambda Calculus  from Project Coq                               *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                      Normal.v                                      *)
(*                                                                    *)
(*                      Barry Jay                                     *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith.
Require Import General.
Require Import Max. 
Require Import Test.
Require Import SF_Terms.
Require Import SF_Tactics.
Require Import Substitution_term.
Require Import SF_reduction.


Inductive status_val := 
| Active : status_val 
| Passive : status_val
.

Fixpoint status M := 
match M with 
| Ref _ => Active  
| Op _ => Passive
| App (App (App (Op Fop) M1) _ ) _ => status M1 
| App M1 _ => status M1 
end. 


Lemma lift_rec_preserves_status: 
forall M n k, status (lift_rec M n k) = status M.
Proof.
rank_tac. 
induction M; split_all.
rewrite IHM1. 2: omega. 
gen_case H M1. gen_case H s. gen_case H s1. gen_case H o. eapply2 IHp. omega. 
Qed. 

(* normal terms *) 

Inductive normal : SF -> Prop := 
| nf_ref : forall n, normal (Ref n)
| nf_op : forall o, normal (Op o)
| nf_active : forall M1 M2, normal M1 -> normal M2 -> 
                              status (App M1 M2) = Active -> 
                              normal (App M1 M2)  
| nf_compound : forall M1 M2, normal M1 -> normal M2 -> 
                              compound (App M1 M2) -> normal (App M1 M2)
.

Hint Constructors normal. 



Lemma lift_rec_preserves_normal: forall M n k, normal M -> normal (lift_rec M n k).
Proof. induction M; intros. split_all. split_all. 
inversion H. apply nf_active; fold lift_rec; auto.
replace  (App (lift_rec M1 n k) (lift_rec M2 n k)) 
with (lift_rec (App M1 M2) n k) by auto. 
rewrite lift_rec_preserves_status. auto. 
simpl. eapply2 nf_compound. 
replace  (App (lift_rec M1 n k) (lift_rec M2 n k)) 
with (lift_rec (App M1 M2) n k) by auto. 
eapply2 lift_rec_preserves_compound. 
Qed. 

Definition irreducible M (red:termred) := forall N, red M N -> False. 

Lemma ref_irreducible : forall n, irreducible (Ref n) sf_seqred1. 
Proof. intro n. red. split_all. inversion H; auto. Qed. 

Lemma normal_is_irreducible: 
forall M, normal M -> irreducible M sf_seqred1. 
Proof. 
intros M nor; induction nor; split_all.  
eapply2 ref_irreducible. 
red; split_all. inversion H. 
intro. intro. inversion H0; subst; simpl in *; try discriminate. 
(* 4 *) 
eapply2 IHnor1. 
(* 3 *) 
eapply2 IHnor2. 
(* 2 *) 
gen2_case H4 H P; subst; inv1 compound; subst; split_all; discriminate.  
(* 1 *) 
intro. intro. inversion H0; subst; simpl in *; try (inversion H; fail).
eapply2 IHnor1. 
eapply2 IHnor2. 
Qed. 


(* 
The basic progress result, that all irreducible terms are normal.
 *) 

Theorem SF_progress : forall (M : SF), normal M \/ (exists N, sf_seqred1 M N) .
Proof. 
induction M; try (inversion IHM); subst; split_all; eauto.
(* 1 *)
inversion IHM1; split_all.  2: right; exist (App x M2). 
inversion IHM2; split_all.  2: right; exist (App M1 x). 
gen_case H M1. inversion H.
left; auto. 
eapply2 nf_active. gen_case H5 s. gen_case H5 s1. 
subst. 
gen2_case H3 H5 s.
gen2_case H3 H5 s1. 
gen2_case H3 H5 o.
right; eauto. 
inversion H3; try discriminate. subst.   
inversion H7. 
left; eauto. 
right; eauto. 
left; eapply2 nf_active. 
subst. 
right; eauto. 
inversion H5. 
Qed. 

