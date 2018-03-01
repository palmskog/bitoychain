From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path.
Require Import Eqdep.
From HTT
Require Import pred prelude idynamic ordtype pcm finmap unionmap heap.
From Toychain
Require Import Chains Blocks Forests.
Require Import ZArith.
From Bitoychain
Require Import Zord SHA256.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Bitcoin : BLOCKCHAIN.

Definition Timestamp : Type := nat.
Definition Hash : ordType := [ordType of seq Z].

Definition VProof : eqType := [eqType of nat].
Definition Transaction : eqType := [eqType of nat].
Definition Address : finType := [finType of 'I_5].

Definition block := @Block Hash Transaction VProof.

Definition GenesisBlock : block := mkB [:: Z0] [::] 0.

Definition Blockchain := seq block.

Definition BlockTree := union_map Hash block.

Definition TxPool := seq Transaction.

Definition hashT (tx:Transaction) : Hash := [:: Z0].

Definition hashB (b:block) : Hash := [:: Z0].

Definition genProof (a : Address) (bc :Blockchain) (txs : TxPool) (ts : Timestamp) : option VProof := None.

Definition VAF (vp:VProof) (ts:Timestamp) (bc:Blockchain) (txs:TxPool) : bool :=
  false.

Definition FCR (bc1:Blockchain) (bc2: Blockchain) : bool :=
  gtn (size bc1) (size bc2).

Definition txValid (tx:Transaction) (bc:Blockchain) : bool :=
  true.

Definition tpExtend (txs:TxPool) (bt: BlockTree) (tx:Transaction) : TxPool :=
  txs ++ [:: tx].

Notation "A > B" := (FCR A B).
Notation "A >= B" := (A = B \/ A > B).
Notation "# b" := (hashB b) (at level 20).

Definition bcLast (bc : Blockchain) := last GenesisBlock bc.

Definition subchain (bc1 bc2 : Blockchain) := exists p q, bc2 = p ++ bc1 ++ q.

Lemma init_hash : prevBlockHash GenesisBlock = #GenesisBlock.
Proof. by []. Qed.

Lemma init_tx : txs GenesisBlock = [::].
Proof. by []. Qed.

Lemma txValid_nil : forall t, txValid t [::].
Proof. by []. Qed.

Lemma hashB_inj : injective hashB.
Proof.
Admitted.

Lemma hashT_inj : injective hashT.
Proof.
Admitted.

Lemma VAF_nocycle : forall (b : block) ts (bc : Blockchain),
  VAF (proof b) ts bc (txs b) -> b \notin bc.
Proof. by []. Qed.

Lemma FCR_subchain :
  forall bc1 bc2, subchain bc1 bc2 -> bc2 >= bc1.
Proof.
Admitted.

Lemma FCR_ext : forall (bc : Blockchain) (b : block) (ext : seq block),
    bc ++ (b :: ext) > bc.
Proof.
Admitted.

Lemma FCR_rel : forall (A B : Blockchain),
    A = B \/ A > B \/ B > A.
Proof.
elim => //=.
- case => //=; first by left.
  move => b bc.
  by right; right.
- move => b1 bc1 IH.
  case => //=; first by right; left.
  move => b2 bc2.
Admitted.

Lemma FCR_nrefl : forall (bc : Blockchain), bc > bc -> False.
Proof. by elim. Qed.

Lemma FCR_trans :
  forall (A B C : Blockchain), A > B -> B > C -> A > C.
Proof.
Admitted.

Variable h : Hash.

Check SHA_256 h.

End Bitcoin.
