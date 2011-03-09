Ltac hyp_rewrite := match goal with
  | [ H : _ |- _ ] => rewrite H
end.
Ltac hyp_apply := match goal with
  | [ H : _ |- _ ] => apply H
end.

Require Import RelationClasses abstract_algebra.

Ltac prove_equivalence := match goal with
| |- Setoid ?s => constructor; unfold equiv; prove_equivalence
| |- Equivalence ?e => constructor; prove_equivalence
| |- Reflexive ?e => unfold e; intro a; intuition reflexivity
| |- Symmetric ?e => unfold e; intros a b Hab; intuition (hyp_rewrite; reflexivity)
| |- Transitive ?e => unfold e; intros a b c Hab Hbc; intuition (hyp_rewrite; hyp_apply)
end.
