Require Import Coq.Strings.String.
Require Import Bitoychain.SHA256.

Definition SHA_256_text text := SHA_256 (str_to_Z text).

Open Scope string_scope.

Require Import Bitoychain.functional_prog.

Definition check_SHA_256_text text digest :=
  listZ_eq (SHA_256_text text) (hexstring_to_Zlist digest) = true.

Goal check "dssdssd" "F4D60BB31D59EF346973DBF0E8656E98EE070B7B94CBD09622EF612E5B6E4BD8".
vm_compute. reflexivity.
Qed.

(* http://csrc.nist.gov/groups/ST/toolkit/documents/Examples/SHA256.pdf *)

Definition FIPS_test_str := "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".
Definition FIPS_test_hexstr := "6162636462636465636465666465666765666768666768696768696a68696a6b696a6b6c6a6b6c6d6b6c6d6e6c6d6e6f6d6e6f706e6f70718".
Definition FIPS_test_hash := "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1".

Lemma check_FIPS_test :
  listZ_eq (hexstring_to_Zlist FIPS_test_hash) (SHA_256' (hexstring_to_Zlist FIPS_test_hexstr)) = true.
Proof.
vm_compute.
reflexivity.
Qed.
