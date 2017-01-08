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
(*                      Eval.v                                        *)
(*                                                                    *)
(*                      Barry Jay                                     *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith.
Require Import Max. 
Require Import Test.
Require Import General. 
Require Import Terms.
Require Import Lambda_tactics.
Require Import Substitution_term.
Require Import SF_reduction.
Require Import LamSF_reduction.
Require Import Normal.
Require Import Closed.


Ltac lamSF_normal := 
match goal with 
| H: lamSF_red ?M ?N |- _ => 
  ((assert(N = M) by (eapply2 normal_is_stable); subst) || generalize H); clear H; lamSF_normal
| _ => split_all
end. 


Ltac lamF_red_same := 
match goal with 
| H1 : lamSF_red ?M ?N1, H2:  lamSF_red ?M ?N2 |- _ => elim(diamond_lamSF_red M N1 H1 N2); split_all; lamSF_normal
| _ => split_all
end. 


 (* restore 

Ltac lamSF_compound := unfold_op; 
match goal with 
| H : lamSF_red ?M ?N |- _ => 
try (assert(compound M) by auto; 
elim(preserves_compound_lamSF_red M N)); generalize H; clear H; inv1 compound; lamSF_compound
| H : lamSF_eq ?M ?N |- _ => 
try (assert(compound M) by auto; 
assert(compound N) by auto; 
elim(preserves_compound_lamSF_eq M N)); generalize H; clear H; inv1 compound
| _ => inv1 compound; lamSF_normal
end. 

*) 


Definition eval_app M N := 
match M with 
| App (App (Op Sop) M1) M2  => App (App M1 N) (App M2 N)
| App (App (Op Fop) (Op _)) M2  => M2
| App (App (Op Fop) (App (Op o) M1)) _ => App (App N (Op o)) M1
| App (App (Op Fop) (App (App (Op o) M1) M2)) _ => App (App N (App (Op o) M1)) M2
| App (App (Op Fop) (Abs (Ref 0))) _ => App (App N abs_left) (star (Ref 0))
| App (App (Op Fop) (Abs (Op o))) _ => App (App N abs_left) (star (Op o))
| Abs M2 => subst N M2
| x => App x N
end.


Lemma eval_app_from_lamSF : forall M N, lamSF_red (App M N) (eval_app M N).
Proof. 
induction M; split_all. 
gen_case IHM1 M1. 
gen_case IHM1 l. 
gen_case IHM1 o. 
gen_case IHM1 l0. 
gen_case IHM1 l1. 
gen_case IHM1 n. 
red; one_step. eapply2 f_compound_lamSF_red. 
red; one_step. eapply2 f_compound_lamSF_red. 
gen_case IHM1 l1. 
red; one_step. eapply2 f_compound_lamSF_red. 
gen_case IHM1 l3. 
red; one_step. eapply2 f_compound_lamSF_red. 
Qed. 


Fixpoint eval0 (M: lamSF) :=
match M with 
| Ref i => Ref i 
| Op o => Op o
| Abs M0 => Abs M0
| App (Op Fop) M11 => App (Op Fop) (eval0 M11)
| App M1 M11 => eval_app (eval0 M1) M11
end. 

Lemma eval0_from_lamSF : forall M, lamSF_red M (eval0 M).
Proof. 
induction M; split_all.
apply transitive_red with (App (eval0 M1) M2); app_lamSF. 
apply transitive_red with (eval_app (eval0 M1) M2). 
eapply2 eval_app_from_lamSF. 
gen_case IHM1 M1. 
gen_case IHM1 o. 
eapply2 preserves_app_lamSF_red. 
Qed. 


Ltac eval_lamSF0 := unfold_op; 
match goal with 
| |-  lamSF_red ?M _ => red; eval_lamSF0
| |-  multi_step lamSF_red1 ?M _ =>
  (apply transitive_red with (eval0 M); 
[eapply2 eval0_from_lamSF |  
  unfold eval0, eval_app;  unfold subst; split_all])
| _ => auto
end.


(* Boolean operations *) 

Definition not M := App (App M (App k_op i_op)) k_op.

Lemma not_true : lamSF_red (not k_op) (App k_op i_op).
Proof. unfold not; eval_lamSF0. Qed. 

Lemma not_false : lamSF_red (not (App k_op i_op)) k_op.
Proof. eval_lamSF0. one_step.   Qed. 

Definition  iff M N := App (App M N) (not N). 

Lemma true_true : lamSF_red (iff k_op k_op) k_op. 
Proof. unfold iff; unfold not; eval_lamSF0; split_all. Qed. 
Lemma true_false : lamSF_red (iff k_op (App k_op i_op)) (App k_op i_op). 
Proof. unfold iff; unfold not; eval_lamSF0; split_all. Qed. 
Lemma false_true : lamSF_red (iff (App k_op i_op) k_op) (App k_op i_op). 
Proof. unfold iff; unfold not; eval_lamSF0; eval_lamSF0; eval_lamSF0; eval_lamSF0; split_all. Qed. 
Lemma false_false : lamSF_red (iff (App k_op i_op) (App k_op i_op)) k_op.
Proof. 
unfold iff, not. unfold_op. repeat eval_lamSF0. Qed. 

(* Fixpoints *) 

Definition little_omega := Abs (Abs (App (Ref 0) (App (App (Ref 1) (Ref 1)) (Ref 0)))).
Definition fix1 := 
(* 
\l f . S(S(Kf)(S(S(K\omega)(K\omega))(Kf)))I
*) 
Abs(App (App s_op 
             (App (App s_op 
                       (App k_op (Ref 0))) 
                  (App (App s_op 
                            (App (App s_op 
                                      (App k_op little_omega)) 
                                 (App k_op little_omega))) 
                       (App k_op (Ref 0))))) 
        i_op). 



Definition fixpoint := App little_omega little_omega. 


Lemma fix1_check: forall M N, lamSF_red (App (App fix1 M) N) 
                                        (App (App M (App (App little_omega little_omega) M)) N). 
Proof. 
split_all. unfold fix1. eval_lamSF0. insert_Ref_out.  eval_lamSF0. rewrite lift_rec_null.
eapply2 preserves_app_lamSF_red.
2:  eval_lamSF0; eval_lamSF0.
fold little_omega. 
match goal with 
| |- lamSF_red (App (App (App (App (Op Fop) (Op Fop)) M) N) ?P) _ => 
apply transitive_red with (App M P)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eval_lamSF0. eval_lamSF0.
match goal with 
| |- multi_step lamSF_red1 (App (App (App (App (App (Op Fop) (Op Fop)) little_omega) N) ?P) ?Q) _ => 
apply transitive_red with (App (App little_omega P) Q)
end. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
Qed. 



Lemma fixpoint_closed : maxvar fixpoint = 0. 
Proof. unfold fixpoint; split_all. Qed. 

Lemma fixes : forall f, lamSF_red (App fixpoint f) (App f (App fixpoint f)).
Proof.
split_all.
unfold fixpoint. unfold little_omega at 1. 
eval_lamSF0. unfold subst; split_all.
insert_Ref_out.  
relocate_lt. 
rewrite lift_rec_null; auto. 
Qed. 



Ltac fixtac :=
match goal with 
| |- lamSF_red (App (App fixpoint ?M) ?N) _ =>  
apply transitive_red with (App (App M (App fixpoint M)) N); [ 
eapply2 preserves_app_lamSF_red; 
eapply2 fixes|]
| |- lamSF_red (App (App (App fixpoint ?M) ?N) ?P) _ =>  
apply transitive_red with (App (App (App M (App fixpoint M)) N) P); [ 
eapply2 preserves_app_lamSF_red; 
eapply2 preserves_app_lamSF_red; 
eapply2 fixes|]
| |- lamSF_red (App (App (App (App fixpoint ?M) ?N) ?P) ?Q) _ =>  
apply transitive_red with (App (App (App (App M (App fixpoint M)) N) P) Q); [ 
eapply2 preserves_app_lamSF_red; 
eapply2 preserves_app_lamSF_red; 
eapply2 preserves_app_lamSF_red; 
eapply2 fixes|]
end. 



Ltac eval_lamSF1 := 
eval_lamSF0; relocate_lt; unfold insert_Ref; unfold lift; try (rewrite lift_rec_closed); split_all. 

(* restore if needed 

Ltac lamSF_eq_eval_l := 
match goal with 
| |- lamSF_eq ?M ?N  => 
apply transitive_lamSF_eq with (eval0 M);
[is_lamSF; eapply2 eval0_from_lamSF | ]
end; 
unfold eval0; unfold subst, lift; split_all; insert_Ref_out. 

*) 
