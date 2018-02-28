Require Import Coq.Strings.String.
Require Import Bitoychain.SHA256.

Definition SHA_256_text text := SHA_256 (str_to_Z text).

Require Import Bitoychain.functional_prog.

Definition check_SHA_256_text text digest :=
  listZ_eq (SHA_256_text text) (hexstring_to_Zlist digest) = true.

Goal check "dssdssd" "F4D60BB31D59EF346973DBF0E8656E98EE070B7B94CBD09622EF612E5B6E4BD8".
vm_compute. reflexivity.
Qed.
