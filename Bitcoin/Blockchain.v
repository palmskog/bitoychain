From mathcomp.ssreflect
Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq fintype path prime.
Require Import Eqdep.
From HTT
Require Import pred prelude idynamic ordtype pcm finmap unionmap heap.
From Toychain
Require Import Chains Blocks Forests.
Require Import ZArith.
Require String.
From Bitoychain
Require Import Zord SHA256 functional_prog.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* https://en.bitcoin.it/wiki/Block_hashing_algorithm *)
(* https://blockexplorer.com/block/000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f *)
(* https://bitcoin.stackexchange.com/questions/2859/how-are-transaction-hashes-calculated *)
(* https://grisha.org/blog/2017/10/10/postgre-as-a-full-node/ *)
(* https://bitcoin.stackexchange.com/questions/10479/what-is-the-merkle-root *)
(* https://bitcoin.stackexchange.com/questions/17545/what-does-prev-out-and-n-mean-in-blockchain-infos-api-data *)
(* https://blockchain.info/tx/017ee876b7078170066da40894b291e496dc09b7fb3edff4e2e7e8262545c7b1?format=json *)
(* https://www.siliconian.com/blog/16-bitcoin-blockchain/22-deconstructing-bitcoin-transactions *)
(* https://blockchain.info/block-index/14849/000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f?format=json *)

Section GenesisBlockConstants.

Open Scope string_scope.

Definition GenesisBlockTx_version_str :=
 "01000000".

Definition GenesisBlockTx_version :=
 hexstring_to_Zlist GenesisBlockTx_version_str.

Definition GenesisBlockTxIn_n_str :=
 "01".

Definition GenesisBlockTxIn_n :=
 hexstring_to_Zlist GenesisBlockTxIn_n_str.

Definition GenesisBlockTxIn_prevout_hash_str :=
 "0000000000000000000000000000000000000000000000000000000000000000".

Definition GenesisBlockTxIn_prevout_hash :=
 hexstring_to_Zlist GenesisBlockTxIn_prevout_hash_str.

Definition GenesisBlockTxIn_prevout_n_str :=
 "ffffffff".

Definition GenesisBlockTxIn_prevout_n :=
 hexstring_to_Zlist GenesisBlockTxIn_prevout_n_str.

Definition GenesisBlockTxIn_scriptsig_str :=
 "4d04ffff001d0104455468652054696d65732030332f4a616e2f32303039204368616e63656c6c6f72206f6e206272696e6b206f66207365636f6e64206261696c6f757420666f722062616e6b73".

Definition GenesisBlockTxIn_scriptsig :=
 hexstring_to_Zlist GenesisBlockTxIn_scriptsig_str.

Definition GenesisBlockTxIn_sequence_str :=
 "ffffffff".

Definition GenesisBlockTxIn_sequence :=
 hexstring_to_Zlist GenesisBlockTxIn_sequence_str.

Definition GenesisBlockTxOut_n_str :=
 "01".

Definition GenesisBlockTxOut_n :=
 hexstring_to_Zlist GenesisBlockTxOut_n_str.

Definition GenesisBlockTxOut_value_str :=
 "00f2052a01000000". (* 5000000000 *)

Definition GenesisBlockTxOut_value :=
 hexstring_to_Zlist GenesisBlockTxOut_value_str.

Definition GenesisBlockTxOut_scriptpubkey_str :=
 "434104678afdb0fe5548271967f1a67130b7105cd6a828e03909a67962e0ea1f61deb649f6bc3f4cef38c4f35504e51ec112de5c384df7ba0b8d578a4c702b6bf11d5fac".

Definition GenesisBlockTxOut_scriptpubkey :=
 hexstring_to_Zlist GenesisBlockTxOut_scriptpubkey_str.

Definition GenesisBlockTx_locktime_str :=
 "00000000".

Definition GenesisBlockTx_locktime :=
 hexstring_to_Zlist GenesisBlockTx_locktime_str.

Definition GenesisBlockTxIn_hashdata :=
 GenesisBlockTxIn_n ++ GenesisBlockTxIn_prevout_hash ++ GenesisBlockTxIn_prevout_n ++ GenesisBlockTxIn_scriptsig ++ GenesisBlockTxIn_sequence.
Definition GenesisBlockTxOut_hashdata :=
 GenesisBlockTxOut_n ++ GenesisBlockTxOut_value ++ GenesisBlockTxOut_scriptpubkey.

Definition GenesisBlockTx_hashdata :=
 GenesisBlockTx_version ++ GenesisBlockTxIn_hashdata ++ GenesisBlockTxOut_hashdata ++ GenesisBlockTx_locktime.

Definition GenesisBlockTx_SHA_256_once := SHA_256' GenesisBlockTx_hashdata.

Definition GenesisBlockTx_SHA_256_twice := SHA_256' GenesisBlockTx_SHA_256_once.

Definition GenesisBlockTx_hashed_rev := rev (SHA_256' (SHA_256' GenesisBlockTx_hashdata)).
Definition GenesisBlockTx_hashed := SHA_256' (SHA_256' GenesisBlockTx_hashdata).

Lemma checkTx_computed_once_hash :
  listZ_eq GenesisBlockTx_SHA_256_once (hexstring_to_Zlist "27362e66e032c731c1c8519f43063fe0e5d070db1c0c3552bb04afa18a31c6bf").
Proof.
vm_compute.
reflexivity.
Qed.

Lemma checkTx_computed_twice_hash : 
  listZ_eq GenesisBlockTx_SHA_256_twice (hexstring_to_Zlist "3ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a").
Proof.
vm_compute.
reflexivity.
Qed.

Definition GenesisBlockPr_hash_merkle_root_str :=
 "4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b".

Definition GenesisBlockPr_hash_merkle_root :=
 hexstring_to_Zlist GenesisBlockPr_hash_merkle_root_str.

Lemma checkTx_hashed : 
  listZ_eq GenesisBlockTx_hashed (rev (hexstring_to_Zlist GenesisBlockPr_hash_merkle_root_str)).
Proof.
vm_compute.
reflexivity.
Qed.

Definition GenesisBlockPr_version_str :=
 "01000000".

Definition GenesisBlockPr_version :=
 hexstring_to_Zlist GenesisBlockPr_version_str.

Definition GenesisBlock_hashPrevBlock_str :=
 "0000000000000000000000000000000000000000000000000000000000000000".

Definition GenesisBlock_hashPrevBlock :=
 hexstring_to_Zlist GenesisBlock_hashPrevBlock_str.

Definition GenesisBlockPr_time_str :=
  "29ab5f49". (* 1231006505 *)
(*  "495fab29". *)  

Definition GenesisBlockPr_time :=
 hexstring_to_Zlist GenesisBlockPr_time_str.

Definition GenesisBlockPr_bits_str :=
  "ffff001d". (* 486604799 *)
(*  "1d00ffff". *)

Definition GenesisBlockPr_bits :=
 hexstring_to_Zlist GenesisBlockPr_bits_str.

Definition GenesisBlockPr_nonce_str :=
 "1dac2b7c". (* 2083236893 *)
(* "7c2bac1d".*)

Definition GenesisBlockPr_nonce :=
 hexstring_to_Zlist GenesisBlockPr_nonce_str.

Definition GenesisBlock_hashdata :=
  GenesisBlockPr_version ++ GenesisBlock_hashPrevBlock ++ GenesisBlockTx_hashed ++
  GenesisBlockPr_time ++ GenesisBlockPr_bits ++ GenesisBlockPr_nonce.

Definition GenesisBlock_hash_str :=
 "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f".

Definition GenesisBlock_hash :=
  rev (hexstring_to_Zlist GenesisBlock_hash_str).

Definition GenesisBlock_SHA_256_once := SHA_256' GenesisBlock_hashdata.

Definition GenesisBlock_SHA_256_twice := SHA_256' GenesisBlock_SHA_256_once.

Definition GenesisBlock_hashed := SHA_256' (SHA_256' GenesisBlock_hashdata).

Lemma checkBlock_hashed : 
  listZ_eq (rev GenesisBlock_hashed) (hexstring_to_Zlist GenesisBlock_hash_str).
Proof.
vm_compute.
reflexivity.
Qed.

End GenesisBlockConstants.

(* http://blockexplorer.com/block/00000000000000001e8d6829a8a21adc5d38d0a473b144b6765798e61f98bd1d *)

Section ExampleBlock.

Open Scope string_scope.

Definition ExampleBlockPr_version_str :=
 "01000000".

Definition ExampleBlockPr_version :=
 hexstring_to_Zlist ExampleBlockPr_version_str.

Definition ExampleBlock_prevBlockHash_str :=
 "00000000000008a3a41b85b8b29ad444def299fee21793cd8b9e567eab02cd81".

Definition ExampleBlock_hashPrevBlock :=
 rev (hexstring_to_Zlist GenesisBlock_hashPrevBlock_str).

Definition ExampleBlock_Tx0_hash_str :=
 "51d37bdd871c9e1f4d5541be67a6ab625e32028744d7d4609d0c37747b40cd2d".

Definition ExampleBlock_Tx0_hash :=
 rev (hexstring_to_Zlist ExampleBlock_Tx0_hash_str).

Definition ExampleBlock_Tx1_hash_str :=
 "60c25dda8d41f8d3d7d5c6249e2ea1b05a25bf7ae2ad6d904b512b31f997e1a1".

Definition ExampleBlock_Tx1_hash :=
 rev (hexstring_to_Zlist ExampleBlock_Tx1_hash_str).

Definition ExampleBlock_Tx2_hash_str :=
 "01f314cdd8566d3e5dbdd97de2d9fbfbfd6873e916a00d48758282cbb81a45b9".

Definition ExampleBlock_Tx2_hash :=
 rev (hexstring_to_Zlist ExampleBlock_Tx2_hash_str).

Definition ExampleBlock_Tx3_hash_str :=
 "b519286a1040da6ad83c783eb2872659eaf57b1bec088e614776ffe7dc8f6d01".

Definition ExampleBlock_Tx3_hash :=
 rev (hexstring_to_Zlist ExampleBlock_Tx3_hash_str).

Definition ExampleBlock_Tx0_Tx1_hash_str :=
  ExampleBlock_Tx0_hash ++ ExampleBlock_Tx1_hash.

Definition ExampleBlock_Tx0_Tx1_hash :=
  SHA_256' (SHA_256' ExampleBlock_Tx0_Tx1_hash_str).

Definition ExampleBlock_Tx2_Tx3_hash_str :=
  ExampleBlock_Tx2_hash ++ ExampleBlock_Tx3_hash.

Definition ExampleBlock_Tx2_Tx3_hash :=
  SHA_256' (SHA_256' ExampleBlock_Tx2_Tx3_hash_str).

Definition ExampleBlock_Tx01_Tx23_hash_str :=
  ExampleBlock_Tx0_Tx1_hash ++ ExampleBlock_Tx2_Tx3_hash.

Definition ExampleBlock_Tx01_Tx23_hash :=
  SHA_256' (SHA_256' ExampleBlock_Tx01_Tx23_hash_str).

Definition ExampleBlock_hash_merkle_root_str :=
  "2b12fcf1b09288fcaff797d71e950e71ae42b91e8bdb2304758dfcffc2b620e3".

Definition ExampleBlock_hash_merkle_root_hash :=
  rev (hexstring_to_Zlist ExampleBlock_hash_merkle_root_str).

Lemma ExampleBlock_hash_check :
  listZ_eq ExampleBlock_Tx01_Tx23_hash ExampleBlock_hash_merkle_root_hash.
Proof.
vm_compute.
reflexivity.
Qed.

Definition ExampleBlockTx0_version_str :=
 "01000000".

Definition ExampleBlockTx0_version :=
 hexstring_to_Zlist ExampleBlockTx0_version_str.

Definition ExampleBlockTx0In_n_str :=
 "01".

End ExampleBlock.

Module Bitcoin : BLOCKCHAIN.

(*Open Scope Z_scope.*)

Definition Timestamp : Type := seq Z.
Definition Hash : ordType := [ordType of seq Z].

Record Pr :=
  mkPr { proof_version : seq Z;
         proof_time : Timestamp;
         proof_bits : seq Z;
         proof_nonce : seq Z
       }.

Definition eq_Pr (p p' : Pr) :=
match p, p' with
| mkPr v1 ts1 n1 b1, mkPr v2 ts2 n2 b2 =>
  (v1 == v2) && (ts1 == ts2) && (n1 == n2) && (b1 == b2)
end.

Lemma eq_PrP : Equality.axiom eq_Pr.
Proof.
case => v1 ts1 n1 b1; case => v2 ts2 n2 b2; rewrite /eq_Pr.
case H2: (v1 == v2); [move/eqP: H2=>?; subst v2| constructor];
  last by case => H_eq; subst v2; rewrite eqxx in H2.
case H3: (ts1 == ts2); [move/eqP: H3=>?; subst ts2| constructor];
  last by case=>?; subst ts2;rewrite eqxx in H3.
case H4: (n1 == n2); [move/eqP: H4=>?; subst n2| constructor];
  last by case=>?; subst n2;rewrite eqxx in H4.
case H5: (b1 == b2); [move/eqP: H5=>?; subst b2| constructor];
  last by case=>?; subst b2;rewrite eqxx in H5.
by constructor.
Qed.

Definition Pr_eqMixin := EqMixin eq_PrP.
Canonical Pr_eqType := Eval hnf in EqType Pr Pr_eqMixin.

Record txIn :=
  mkTxIn
    { in_n : seq Z;
      in_prevout_hash : seq Z;
      in_prevout_n : seq Z;
      in_scriptsig : seq Z;
      in_sequence : seq Z
    }.

Definition eq_txIn (ti ti' : txIn) :=
match ti, ti' with
| mkTxIn n1 prevout_hash1 prevout_n1 scriptsig1 sequence1, mkTxIn n2 prevout_hash2 prevout_n2 scriptsig2 sequence2 =>
  (n1 == n2) && (prevout_hash1 == prevout_hash2) && (prevout_n1 == prevout_n2) && (scriptsig1 == scriptsig2) && (sequence1 == sequence2)
end.

Lemma eq_txInP : Equality.axiom eq_txIn.
Proof.
case => n1 prevout_hash1 prevout_n1 scriptsig1 sequence1; case => n2 prevout_hash2 prevout_n2 scriptsig2 sequence2; rewrite /eq_txIn.
case H2: (n1 == n2); [move/eqP: H2=>?; subst n2| constructor];
  last by case => H_eq; subst n2; rewrite eqxx in H2.
case H3: (prevout_hash1 == prevout_hash2); [move/eqP: H3=>?; subst prevout_hash2| constructor];
  last by case=>?; subst prevout_hash2;rewrite eqxx in H3.
case H4: (prevout_n1 == prevout_n2); [move/eqP: H4=>?; subst prevout_n2| constructor];
  last by case=>?; subst prevout_n2;rewrite eqxx in H4.
case H5: (scriptsig1 == scriptsig2); [move/eqP: H5=>?; subst scriptsig2| constructor];
  last by case=>?; subst scriptsig2;rewrite eqxx in H5.
case H6: (sequence1 == sequence2); [move/eqP: H6=>?; subst sequence2| constructor];
  last by case=>?; subst sequence2;rewrite eqxx in H6.
by constructor.
Qed.

Definition txIn_eqMixin := EqMixin eq_txInP.
Canonical txIn_eqType := Eval hnf in EqType txIn txIn_eqMixin.

Inductive txOut :=
  mkTxOut
    { out_n : seq Z;
      out_value : seq Z;
      out_scriptpubkey : seq Z
    }.

Definition eq_txOut (ti ti' : txOut) :=
match ti, ti' with
| mkTxOut n1 value1 scriptpubkey1, mkTxOut n2 value2 scriptpubkey2 =>
  (n1 == n2) && (value1 == value2) && (scriptpubkey1 == scriptpubkey2)
end.

Lemma eq_txOutP : Equality.axiom eq_txOut.
Proof.
case => n1 value1 scriptpubkey1; case => n2 value2 scriptpubkey2; rewrite /eq_txOut.
case H2: (n1 == n2); [move/eqP: H2=>?; subst n2| constructor];
  last by case => H_eq; subst n2; rewrite eqxx in H2.
case H3: (value1 == value2); [move/eqP: H3=>?; subst value2| constructor];
  last by case=>?; subst value2;rewrite eqxx in H3.
case H4: (scriptpubkey1 == scriptpubkey2); [move/eqP: H4=>?; subst scriptpubkey2| constructor];
  last by case=>?; subst scriptpubkey2;rewrite eqxx in H4.
by constructor.
Qed.

Definition txOut_eqMixin := EqMixin eq_txOutP.
Canonical txOut_eqType := Eval hnf in EqType txOut txOut_eqMixin.

Inductive Tx :=
  mkTx
    { tx_version : seq Z;
      tx_ins : seq txIn;
      tx_outs : seq txOut;
      tx_locktime : seq Z
    }.

Definition eq_Tx (tx tx' : Tx) :=
match tx, tx' with
| mkTx version1 locktime1 ins1 outs1, mkTx version2 locktime2 ins2 outs2 =>
  (version1 == version2) && (locktime1 == locktime2) && (ins1 == ins2) && (outs1 == outs2)
end.

Lemma eq_TxP : Equality.axiom eq_Tx.
Proof.
case => version1 locktime1 ins1 outs1; case => version2 locktime2 ins2 outs2; rewrite /eq_Tx.
case H2: (version1 == version2); [move/eqP: H2=>?; subst version2| constructor];
  last by case => H_eq; subst version2; rewrite eqxx in H2.
case H3: (locktime1 == locktime2); [move/eqP: H3=>?; subst locktime2| constructor];
  last by case=>?; subst locktime2;rewrite eqxx in H3.
case H4: (ins1 == ins2); [move/eqP: H4=>?; subst ins2| constructor];
  last by case=>?; subst ins2;rewrite eqxx in H4.
case H5: (outs1 == outs2); [move/eqP: H5=>?; subst outs2| constructor];
  last by case=>?; subst outs2;rewrite eqxx in H5.
by constructor.
Qed.

Definition Tx_eqMixin := EqMixin eq_TxP.
Canonical Tx_eqType := Eval hnf in EqType Tx Tx_eqMixin.

Definition VProof : eqType := [eqType of Pr].
Definition Transaction : eqType := [eqType of Tx].
Definition Address : finType := [finType of 'I_5].

Definition block := @Block Hash Transaction VProof.

Definition GenesisBlockTxIn :=
 mkTxIn GenesisBlockTxIn_n GenesisBlockTxIn_prevout_hash GenesisBlockTxIn_prevout_n GenesisBlockTxIn_scriptsig GenesisBlockTxIn_sequence.

Definition GenesisBlockTxOut :=
 mkTxOut GenesisBlockTxOut_n GenesisBlockTxOut_value GenesisBlockTxOut_scriptpubkey.

Definition GenesisBlockTx :=
 mkTx GenesisBlockTx_version [:: GenesisBlockTxIn] [:: GenesisBlockTxOut] GenesisBlockTx_locktime.

Definition GenesisBlockPr :=
  mkPr GenesisBlockPr_version GenesisBlockPr_time GenesisBlockPr_bits GenesisBlockPr_nonce.

Definition GenesisBlock : block := mkB GenesisBlock_hash [:: GenesisBlockTx] GenesisBlockPr.
Definition GenesisBlock' : block := mkB GenesisBlock_hashPrevBlock [:: GenesisBlockTx] GenesisBlockPr.

Definition Blockchain := seq block.

Definition BlockTree := union_map Hash block.

Definition TxPool := seq Transaction.

Definition hashdataTxIn (ti: txIn) : seq Z :=
 in_n ti ++ in_prevout_hash ti ++ in_prevout_n ti ++ in_scriptsig ti ++ in_sequence ti.

Definition hashdataTxOut (to: txOut) : seq Z :=
 out_n to ++ out_value to ++ out_scriptpubkey to.

Definition hashdataT (tx : Transaction) : seq Z :=
  tx_version tx ++
  foldl (fun s i => s ++ hashdataTxIn i) [::] (tx_ins tx) ++
  foldl (fun s i => s ++ hashdataTxOut i) [::] (tx_outs tx) ++
  tx_locktime tx.

Definition hashT (tx:Transaction) : Hash :=
  SHA_256' (SHA_256' (hashdataT tx)).

(*
Open Scope string_scope.
Lemma hashT_GenesisBlock_eq :
  listZ_eq (hashT GenesisBlockTx) (rev (hexstring_to_Zlist "4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b")).
Proof.
vm_compute.
reflexivity.
Qed.
*)

(* trunc_log p m == the largest e such that p ^ e <= m, or 0 if p or m is 0. *)

Definition ceil_log2 (n : nat) :=
  let lg := trunc_log 2 n in
  if n == 2 ^ lg then lg else lg.+1.

Fixpoint merkle_tree_pass (hs : seq Hash) : seq Hash :=
match hs with
| [::] => [::]
| [:: h] => [:: SHA_256' (SHA_256' (h ++ h))]
| [:: h1, h2 & hs'] => SHA_256' (SHA_256' (h1 ++ h2)) :: merkle_tree_pass hs'
end.

Fixpoint merkle_tree_hash (txs : seq Transaction) : Hash :=
let fix loop hs k : Hash :=
 match k with
 | 0 =>
   match hs with
   | [:: h] => h
   | _ => [::]
   end
 | k'.+1 =>
   loop (merkle_tree_pass hs) k'
end in
let hs := map hashT txs in
let passes := ceil_log2 (size hs) in
loop hs passes.

Definition hashdataB (b : block) : seq Z :=
  proof_version (proof b) ++
  prevBlockHash b ++
  merkle_tree_hash (txs b) ++
  proof_time (proof b) ++
  proof_bits (proof b) ++
  proof_nonce (proof b).

Lemma merkle_tree_eq :
  listZ_eq (merkle_tree_hash (txs GenesisBlock')) GenesisBlockTx_hashed.
Proof.
vm_compute.
reflexivity.
Qed.

Lemma hashB_GenesisBlock_eq :
  listZ_eq (SHA_256' (SHA_256' (hashdataB GenesisBlock'))) GenesisBlock_hash.
Proof.
vm_compute.
reflexivity.
Qed.

Definition hashB (b:block) : Hash :=
  if b == GenesisBlock then prevBlockHash b
  else SHA_256' (SHA_256' (hashdataB b)).

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
