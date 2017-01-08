(**********************************************************************)
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

(**********************************************************************)
(*                  LambdaFactor Calculus                             *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *) 
(* Lambda Calculus  from Project Coq                                  *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                           General.v                                *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)

Require Import Omega.
Require Import ArithRing. 

(* some general-purpose tactics *) 

Ltac eapply2 H := eapply H; eauto.


Ltac split_all := simpl; intros; 
match goal with 
| H : _ /\ _ |- _ => inversion_clear H; split_all
| H : if ?b then False else False |-_=> generalize H; clear H; case b; split_all
| |- if ?b then True else True => case b; auto
| H : false = true |-_=> inversion H
| H : exists _, _ |- _ => inversion H; clear H; split_all 
| _ =>  try (split; split_all); try contradiction
end; try congruence; auto.

Ltac noway := intros; assert False by omega; contradiction. 

Ltac exist x := exists x; split_all. 

Ltac gen_case H W := 
  generalize H; clear H; case W; split_all. 

Ltac gen2_case H0 H1 W := 
  generalize H0 H1; clear H0 H1; case W; split_all.

Ltac gen3_case H0 H1 H2 W := 
  generalize H0 H1 H2; clear H0 H1 H2; case W; split_all.

Ltac gen4_case H0 H1 H2 H3 W := 
  generalize H0 H1 H2 H3; clear H0 H1 H2 H3; case W; split_all.

Ltac gen_inv H W := 
  generalize H; clear H; inversion W; split_all. 

Ltac gen2_inv H0 H1 W := 
  generalize H0 H1; clear H0 H1; inversion W; split_all.

Ltac gen3_inv H0 H1 H2 W := 
  generalize H0 H1 H2; clear H0 H1 H2; inversion W; split_all.

Ltac gen4_inv H0 H1 H2 H3 W := 
  generalize H0 H1 H2 H3; clear H0 H1 H2 H3; inversion W; split_all.


Ltac gen_case_inv H M := gen_case H M; inversion H; auto.

Ltac invsub := match goal with | H : _ = _ |- _ => inversion H; subst; clear H; invsub | _ => split_all end. 


(* some arithmetic *) 

Ltac dropS := 
match goal with 
| |- S ?m <= S?n => cut(m<= n); [split_all; omega |]  
| |- S ?m < S?n => cut(m< n); [split_all; omega |] 
| |- S ?m >= S?n => cut(m>= n); [split_all; omega |]  
| |- S ?m > S?n => cut(m> n); [split_all; omega |] 
end. 


Lemma times_distributive : forall m n p, (m+n) * p = m*p + n * p. 
Proof. split_all. ring. Qed. 

Lemma times_distributive2 : 
forall m n p q, (m+n) * (p+q) = m*p + n * p + m*q + n*q. 
Proof. split_all. ring. Qed. 

Lemma times_positive: forall m n, m>0 -> n>0 -> m*n >0 . 
Proof. 
split_all. gen_case H m; gen_case H0 n; split_all; try noway. 
case (n1 + n0 * S n1); split_all; omega. 
Qed. 



Lemma  times_monotonic:  forall m1 m2 n1 n2, 0< m1 -> 0 < m2 -> m1 < n1 -> m2 < n2 -> m1 * m2 < n1 * n2. 
Proof. 
split_all.  
replace n1 with (n1 - m1 + m1) by omega. 
replace n2 with (n2 - m2 + m2) by omega. 
rewrite times_distributive2. 
cut(0 < (n1 - m1) * (n2 - m2) + m1 * (n2 - m2) + (n1 - m1) * m2). 
split_all; omega. 
replace m1 with (1+ (pred m1)) by omega. 
replace (n2 - m2) with (1+ (pred (n2 - m2))) by omega. 
rewrite times_distributive2. 
simpl. 
case((pred m1 * 1 + (pred (n2 - m2) + 0) + pred m1 * pred (n2 - m2))); 
case((n1 - S (pred m1)) * S (pred (n2 - m2))); 
case((n1 - S (pred m1)) * m2); split_all; omega. 
Qed. 

Lemma  times_monotonic2:  forall m1 m2 n1 n2, 0< m1 -> 0 < m2 -> m1 <= n1 -> m2 < n2 -> m1 * m2 < n1 * n2. 
Proof. 
split_all.  
replace n1 with (n1 - m1 + m1) by omega. 
replace n2 with (n2 - m2 + m2) by omega. 
rewrite times_distributive2. 
assert(0 < (n1 - m1) * (n2 - m2) + m1 * (n2 - m2) + (n1 - m1) * m2). 
replace m1 with (1+ (pred m1)) by omega. 
replace (n2 - m2) with (1+ (pred (n2 - m2))) by omega. 
rewrite times_distributive2. 
simpl. 
case((pred m1 * 1 + (pred (n2 - m2) + 0) + pred m1 * pred (n2 - m2))); 
case((n1 - S (pred m1)) * S (pred (n2 - m2))); 
case((n1 - S (pred m1)) * m2); split_all; omega. 
gen_case H3 ((n1 - m1) * (n2 - m2) + m1 * (n2 - m2) + (n1 - m1) * m2); split_all; try noway.  omega. 
Qed. 


Fixpoint exp (m n:nat) {struct n}: nat :=
match n with
| O => 1
| S n => m * exp m n
end.

Notation "x ^ y" := (exp x y).

Lemma exp_positive: forall n m, m>0 -> exp m n >0 .
Proof. 
induction n; split_all. 
assert(m^n >0) by eapply2 IHn.
eapply2 times_positive.  
Qed. 


Lemma max_is_max : forall m n, max m n >= m /\ max m n >= n.
Proof. 
double induction m n; split_all; try omega. 
elim (H0 n); split_all; omega. 
elim (H0 n); split_all; omega. 
Qed. 


Lemma max_succ: forall m n, S (max m n) = max (S m) (S n). 
Proof. double induction m n; split_all.  Qed. 

Lemma max_pred: forall m n, pred (max m n) = max (pred m) (pred n). 
Proof. double induction m n; split_all. case n; split_all. Qed. 

Lemma max_max : forall m n p, m >= max n p -> m>= n /\ m>= p.
Proof. 
induction m; intros n p. case n; case p; split_all; subst; try noway; try omega. 
intros. 
assert(m >= pred (max n p)) by omega. 
rewrite max_pred in H0. 
elim (IHm (pred n) (pred p)); split_all; omega. 
Qed. 

Lemma max_max2 : forall m n k, k>= m -> k>= n -> k>= max m n. 
Proof. 
double induction m n; split_all. 
assert(pred k >= max n1 n) .  eapply2 H0. omega. omega. omega. 
Qed. 

Lemma max_zero : forall m, max m 0 = m. 
Proof. induction m; split_all. Qed.

Lemma max_plus: forall m n k, max m n +k = max (m+k) (n+k). 
Proof.
double induction m n; split_all. 
induction k; split_all.  
assert(max k (S (n0+k)) >= S(n0+k)) by eapply2 max_is_max.  
assert(S(n0+k) >= max k (S(n0+k))) . eapply2 max_max2. 
omega. 
omega. 
case k; split_all. 
assert(max (n+S n1) n1 >= n+ S n1) by  eapply2 max_is_max.  
assert(n+ S n1 >= max (n+S n1) n1) . eapply2 max_max2. 
omega. 
omega. 
Qed. 

Lemma max_minus: forall m n k, max m n -k = max (m-k) (n-k). 
Proof.
double induction m n; split_all.
case k; split_all. 
rewrite max_zero. omega.
case k; split_all. 
Qed. 

Lemma max_monotonic : forall m1 m2 n1 n2, m1 >= n1 -> m2 >= n2 -> max m1 m2 >= max n1 n2. 
Proof. 
double induction m1 m2; split_all. 
assert (n1 = 0) by omega; subst. 
assert (n2 = 0) by omega; subst. 
split_all. 
assert (n1 = 0) by omega; subst. split_all. 
assert (n2 = 0) by omega; subst. 
assert(max n1 0 = n1) . case n1; split_all. 
rewrite H2; auto.  
assert(n0 >= pred n1) by omega.
cut(max n0 n >= pred (max n1 n2)).  
intro.  
omega. 
rewrite max_pred. 
eapply2 H0. 
omega. 
Qed. 

Lemma max_succ_zero : forall k n, max k (S n) = 0 -> False .
Proof. split_all. assert(max k (S n) >= S n) by eapply2 max_is_max. noway. Qed. 
Ltac max_out := 
match goal with 
| H : max _ (S _) = 0  |- _ => assert False by (eapply2 max_succ_zero); noway
| H : max ?m ?n = 0 |- _ => 
assert (m = 0) by (assert (max m n >= m) by eapply2 max_is_max; omega);
assert (n = 0) by (assert (max m n >= n) by eapply2 max_is_max; omega);
clear H; try omega; try noway
| H : max ?m ?n <= 0 |- _ => 
assert (m = 0) by (assert (max m n >= m) by eapply2 max_is_max; omega);
assert (n = 0) by (assert (max m n >= n) by eapply2 max_is_max; omega);
clear H; try omega; try noway
end. 



Lemma min_is_min : forall m n, min m n <= m /\ min m n <= n.
Proof. 
double induction m n; split_all; try omega. 
elim (H0 n); split_all; omega. 
elim (H0 n); split_all; omega. 
Qed. 


Lemma min_succ: forall m n, S (min m n) = min (S m) (S n). 
Proof. double induction m n; split_all.  Qed. 

Lemma min_pred: forall m n, pred (min m n) = min (pred m) (pred n). 
Proof. double induction m n; split_all. case n; split_all. Qed. 

Lemma min_zero : forall m, min m 0 = 0. 
Proof. induction m; split_all. Qed.

Lemma min_min : forall m n p, m <= min n p -> m<= n /\ m<= p.
Proof. 
induction m; split_all; try omega. 
gen_case H n; gen_case H p; try noway. 
assert(m<= min n0 n1) by omega. 
assert(m<= n0 /\ m<= n1) by eapply2 IHm; split_all; omega. 
gen_case H p; try noway.
rewrite min_zero in *. 
noway. 
assert(m<= pred (min n (S n0))) by omega. 
rewrite min_pred in H0. 
simpl in *. 
elim (IHm (pred n) n0); split_all. 
omega. 
Qed. 

Lemma min_min2 : forall m n k, k<= m -> k<= n -> k<= min m n. 
Proof. 
double induction m n; split_all. 
assert(pred k <= min n1 n) .  eapply2 H0. omega. omega. omega. 
Qed. 


Lemma min_plus: forall m n k, min m n +k = min (m+k) (n+k). 
Proof.
double induction m n; split_all. 
induction k; split_all.  
assert(min k (S (n0+k)) <= k) by eapply2 min_is_min.  
assert(k <= min k (S(n0+k))) . eapply2 min_min2. 
omega. 
omega. 
case k; split_all. 
assert(min (n+S n1) n1 <= n1) by  eapply2 min_is_min.  
assert(n1 <= min (n+S n1) n1) . eapply2 min_min2. 
omega. 
omega. 
Qed. 

Lemma min_minus: forall m n k, min m n -k = min (m-k) (n-k). 
Proof.
double induction m n; split_all.
case k; split_all. 
rewrite min_zero. omega.
case k; split_all. 
Qed. 

Lemma min_monotonic : forall m1 m2 n1 n2, m1 <= n1 -> m2 <= n2 -> min m1 m2 <= min n1 n2. 
Proof. 
double induction m1 m2; split_all; try omega.
gen_case H1 n1; try noway. 
gen_case H2 n2; try noway. 
assert(min n0 n <= min n3 n4). 
eapply2 H0; try omega. 
omega. 
Qed. 


Lemma decidable_nats : forall (m n: nat), m=n \/ m<>n. 
Proof. 
 double induction m n. 
left; split_all. 
split_all; right; congruence. 
split_all; right; congruence. 
split_all. 
elim(H0 n); split_all. 
Qed. 

