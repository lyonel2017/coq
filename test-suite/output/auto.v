(* testing info_*/debug auto/eauto *)

Goal False \/ (True -> True).
Succeed info_auto.
Succeed debug auto.
Succeed info_eauto.
debug eauto.
Qed.

Goal True.
info_trivial.
Qed.
