From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path.
Require Import Eqdep.
From HTT
Require Import pred prelude idynamic ordtype pcm finmap unionmap heap.
Require Import ZArith.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section ZOrd.

Open Scope Z_scope.

Lemma eqZP : Equality.axiom Z_eq_dec.
Proof.
move => x y.
by apply: (iffP idP); case Z_eq_dec.
Qed.

Canonical Z_eqMixin := EqMixin eqZP.
Canonical Z_eqType := Eval hnf in EqType Z Z_eqMixin.

Lemma ZltP :
  forall x y, reflect (x < y) (Z_lt_dec x y).
Proof.
by move => x y; apply: (iffP idP); case Z_lt_dec.
Qed.

Lemma irr_Z_lt_dec : irreflexive Z_lt_dec.
Proof.
move => x.
apply/ZltP.
exact: Z.lt_irrefl.
Qed.

Lemma trans_Z_lt_dec : transitive Z_lt_dec.
Proof.
move => x y z.
move/ZltP => H_lt1.
move/ZltP => H_lt2.
apply/ZltP.
move: H_lt1 H_lt2.
exact: Z.lt_trans.
Qed.

Lemma total_Z_lt_dec : forall x y, [|| Z_lt_dec x y, x == y | Z_lt_dec y x].
Proof.
move => x y.
case (Z_dec x y) => H_dec.
- case: H_dec => H_dec.
  * apply/orP.
    left.
    by apply/ZltP.
  * apply/orP.
    right.
    apply/orP.
    right.
    apply/ZltP.
    by auto with zarith.
- apply/orP.
  right.
  apply/orP.
  left.
  by apply/eqZP.
Qed.

Definition Z_ordMixin := OrdMixin irr_Z_lt_dec trans_Z_lt_dec total_Z_lt_dec.
Canonical Structure Z_ordType := OrdType Z Z_ordMixin.

End ZOrd.
