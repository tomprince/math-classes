Require Import
    Morphisms RelationClasses Equivalence Setoid
    abstract_algebra interfaces.functors categories
    extra_tactics.

Section Square.

Context `{Category C}.

Class Square {a b x y: C} (i: a⟶b) (p: x⟶y) (f: a⟶x) (g: b⟶y) := square : g◎i = p◎f.

Section Transpose.
Context `{Square a b x y i p f g}.
Lemma transpose_square : Square f g i p.
Proof. red; symmetry; trivial. Qed.
End Transpose.

Section comp_square.
Context `{Square a b u v i j f g} `{Square u v x y j k f' g'}.
Global Instance: Square i k (f'◎f) (g'◎g).
Proof.
red.
rewrite <- comp_assoc; hyp_rewrite.
repeat rewrite comp_assoc; hyp_rewrite.
reflexivity.
Qed.
End comp_square.
(*
Section comp_square2.
Context `{Square a b u v i j f g} `{Square b x v y i' j' g h}.
Global Instance: Square (i' ◎ i) (j' ◎ j) f hr. (* := TransosedSquare. *)
Admitted.
End comp_square2.
*)

Section id_square.
Context `{i:a⟶b}.
Global Instance: Square i i cat_id cat_id.
Proof. red; rewrite left_identity, right_identity; reflexivity. Qed.

(* Global Instance: Square cat_id cat_id i i := TransposedSquare. *)
End id_square.

Section SquareProper.
Context {a b x y: C}.
Global Instance: Proper (equiv ==> equiv ==> equiv ==> equiv ==> equiv) (@Square a b x y).
Proof. repeat intro; unfold Square; do 4 hyp_rewrite; reflexivity. Qed.
End SquareProper.

End Square.

(*** Fixme: this goes where? ***)

Section Comma.
Context `{Category L} `{Category R} `{Category C}.
Context (F: L->C) `{!Functor (F: L->C) F_fmap} (G: R->C) `{!Functor (G: R->C) G_fmap}.

Class Comma (left_object: L) (right_object: R) := comma: F left_object ⟶ G right_object.

End Comma.
