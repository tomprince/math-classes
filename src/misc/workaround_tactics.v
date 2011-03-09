Global Ltac posed_rewrite t := let TEMP:=fresh in pose proof t as TEMP; simpl TEMP; rewrite TEMP; clear TEMP.
  (* Workaround around Coq bug, probably same as #2185. *)
Global Ltac apply_simplified x := generalize x; simpl; intro HHH; apply HHH; clear HHH.
Tactic Notation "posed_rewrite" "<-" constr(t) := let TEMP:= fresh in pose proof t as TEMP; simpl TEMP; rewrite <-TEMP; clear TEMP.
