Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import p015_string_sequence.
Require Import p015_string_sequence.
Local Open Scope sac.
Require Import char_array_strategy_goal.
Require Import char_array_strategy_proof.

(*----- Function p015_string_sequence -----*)

Definition p015_string_sequence_safety_wit_1 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre n_pre ) ” 
  &&  “ (sequence_output_bound n_pre ) ”
  &&  ((( &( "cap" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (((12 * (n_pre + 1 ) ) + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((12 * (n_pre + 1 ) ) + 1 )) ”
.

Definition p015_string_sequence_safety_wit_2 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre n_pre ) ” 
  &&  “ (sequence_output_bound n_pre ) ”
  &&  ((( &( "cap" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((12 * (n_pre + 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (12 * (n_pre + 1 ) )) ”
.

Definition p015_string_sequence_safety_wit_3 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre n_pre ) ” 
  &&  “ (sequence_output_bound n_pre ) ”
  &&  ((( &( "cap" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ ((n_pre + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + 1 )) ”
.

Definition p015_string_sequence_safety_wit_4 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre n_pre ) ” 
  &&  “ (sequence_output_bound n_pre ) ”
  &&  ((( &( "cap" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (12 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 12) ”
.

Definition p015_string_sequence_safety_wit_5 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre n_pre ) ” 
  &&  “ (sequence_output_bound n_pre ) ”
  &&  ((( &( "cap" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p015_string_sequence_safety_wit_6 := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre n_pre ) ” 
  &&  “ (sequence_output_bound n_pre ) ”
  &&  ((( &( "cap" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p015_string_sequence_safety_wit_7 := 
forall (n_pre: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre n_pre ) ” 
  &&  “ (sequence_output_bound n_pre ) ”
  &&  ((( &( "k" ) )) # Int  |->_)
  **  (CharArray.undef_full retval ((12 * (n_pre + 1 ) ) + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cap" ) )) # Int  |-> ((12 * (n_pre + 1 ) ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p015_string_sequence_safety_wit_8 := 
forall (n_pre: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre n_pre ) ” 
  &&  “ (sequence_output_bound n_pre ) ”
  &&  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval ((12 * (n_pre + 1 ) ) + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cap" ) )) # Int  |-> ((12 * (n_pre + 1 ) ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p015_string_sequence_safety_wit_9 := 
forall (n_pre: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre n_pre ) ” 
  &&  “ (sequence_output_bound n_pre ) ”
  &&  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval ((12 * (n_pre + 1 ) ) + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cap" ) )) # Int  |-> ((12 * (n_pre + 1 ) ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p015_string_sequence_safety_wit_10 := 
forall (n_pre: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre n_pre ) ” 
  &&  “ (sequence_output_bound n_pre ) ”
  &&  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  (CharArray.undef_full retval ((12 * (n_pre + 1 ) ) + 1 ) )
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cap" ) )) # Int  |-> ((12 * (n_pre + 1 ) ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition p015_string_sequence_safety_wit_11 := 
forall (n_pre: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre n_pre ) ” 
  &&  “ (sequence_output_bound n_pre ) ”
  &&  (CharArray.undef_seg retval (0 + 1 ) ((12 * (n_pre + 1 ) ) + 1 ) )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 0)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cap" ) )) # Int  |-> ((12 * (n_pre + 1 ) ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p015_string_sequence_safety_wit_12 := 
forall (n_pre: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre n_pre ) ” 
  &&  “ (sequence_output_bound n_pre ) ”
  &&  ((( &( "t" ) )) # Int  |->_)
  **  (CharArray.undef_seg retval (0 + 1 ) ((12 * (n_pre + 1 ) ) + 1 ) )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 1)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cap" ) )) # Int  |-> ((12 * (n_pre + 1 ) ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p015_string_sequence_safety_wit_13 := 
forall (n_pre: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre n_pre ) ” 
  &&  “ (sequence_output_bound n_pre ) ”
  &&  ((( &( "digits" ) )) # Int  |->_)
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  (CharArray.undef_seg retval (0 + 1 ) ((12 * (n_pre + 1 ) ) + 1 ) )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 1)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cap" ) )) # Int  |-> ((12 * (n_pre + 1 ) ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p015_string_sequence_safety_wit_14 := 
forall (n_pre: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre n_pre ) ” 
  &&  “ (sequence_output_bound n_pre ) ”
  &&  ((( &( "j" ) )) # Int  |->_)
  **  ((( &( "digits" ) )) # Int  |-> 0)
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  (CharArray.undef_seg retval (0 + 1 ) ((12 * (n_pre + 1 ) ) + 1 ) )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 1)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cap" ) )) # Int  |-> ((12 * (n_pre + 1 ) ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p015_string_sequence_safety_wit_15 := 
forall (n_pre: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre n_pre ) ” 
  &&  “ (sequence_output_bound n_pre ) ”
  &&  ((( &( "fill" ) )) # Int  |->_)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "digits" ) )) # Int  |-> 0)
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  (CharArray.undef_seg retval (0 + 1 ) ((12 * (n_pre + 1 ) ) + 1 ) )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 1)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cap" ) )) # Int  |-> ((12 * (n_pre + 1 ) ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p015_string_sequence_safety_wit_16 := 
forall (n_pre: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre n_pre ) ” 
  &&  “ (sequence_output_bound n_pre ) ”
  &&  ((( &( "fill" ) )) # Int  |-> 0)
  **  ((( &( "j" ) )) # Int  |-> 0)
  **  ((( &( "digits" ) )) # Int  |-> 0)
  **  ((( &( "t" ) )) # Int  |-> 0)
  **  (CharArray.undef_seg retval (0 + 1 ) ((12 * (n_pre + 1 ) ) + 1 ) )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
  **  ((( &( "i" ) )) # Int  |-> 1)
  **  ((( &( "k" ) )) # Int  |-> 1)
  **  ((( &( "out" ) )) # Ptr  |-> retval)
  **  ((( &( "cap" ) )) # Int  |-> ((12 * (n_pre + 1 ) ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p015_string_sequence_safety_wit_17 := 
forall (out: Z) (cap: Z) (k: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) (n: Z) (i: Z) ,
  “ (i <= n) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n + 1 )) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < cap) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "t" ) )) # Int  |-> i)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (sequence_prefix (i)) )
  **  (CharArray.undef_seg out k cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p015_string_sequence_safety_wit_18 := 
forall (out: Z) (i: Z) (cap: Z) (k: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) ,
  “ (0 <= t) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < cap) ”
  &&  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (sequence_prefix (i)) )
  **  (CharArray.undef_seg out k cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p015_string_sequence_safety_wit_19 := 
forall (out: Z) (i: Z) (cap: Z) (k: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) ,
  “ (t > 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < cap) ”
  &&  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (sequence_prefix (i)) )
  **  (CharArray.undef_seg out k cap )
|--
  “ ((digits + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (digits + 1 )) ”
.

Definition p015_string_sequence_safety_wit_20 := 
forall (out: Z) (i: Z) (cap: Z) (k: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) ,
  “ (t > 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < cap) ”
  &&  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (sequence_prefix (i)) )
  **  (CharArray.undef_seg out k cap )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p015_string_sequence_safety_wit_21 := 
forall (out: Z) (i: Z) (cap: Z) (k: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) ,
  “ (t > 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < cap) ”
  &&  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "digits" ) )) # Int  |-> (digits + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (sequence_prefix (i)) )
  **  (CharArray.undef_seg out k cap )
|--
  “ ((t <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition p015_string_sequence_safety_wit_22 := 
forall (out: Z) (i: Z) (cap: Z) (k: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) ,
  “ (t > 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < cap) ”
  &&  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "digits" ) )) # Int  |-> (digits + 1 ))
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (sequence_prefix (i)) )
  **  (CharArray.undef_seg out k cap )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition p015_string_sequence_safety_wit_23 := 
forall (out: Z) (i: Z) (cap: Z) (k: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) ,
  “ (t <= 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < cap) ”
  &&  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (sequence_prefix (i)) )
  **  (CharArray.undef_seg out k cap )
|--
  “ (32 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 32) ”
.

Definition p015_string_sequence_safety_wit_24 := 
forall (out: Z) (i: Z) (cap: Z) (k: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) ,
  “ (0 <= k) ” 
  &&  “ (t <= 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < cap) ”
  &&  (CharArray.full out (k + 1 ) (app ((sequence_prefix (i))) ((cons (32) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) cap )
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((k + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + 1 )) ”
.

Definition p015_string_sequence_safety_wit_25 := 
forall (out: Z) (i: Z) (cap: Z) (k: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) ,
  “ (0 <= k) ” 
  &&  “ (t <= 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < cap) ”
  &&  (CharArray.full out (k + 1 ) (app ((sequence_prefix (i))) ((cons (32) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) cap )
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p015_string_sequence_safety_wit_26 := 
forall (out: Z) (i: Z) (cap: Z) (k: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) ,
  “ (0 <= k) ” 
  &&  “ (t <= 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < cap) ”
  &&  (CharArray.full out (k + 1 ) (app ((sequence_prefix (i))) ((cons (32) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) cap )
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "k" ) )) # Int  |-> (k + 1 ))
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p015_string_sequence_safety_wit_27 := 
forall (out: Z) (i: Z) (cap: Z) (k: Z) (fill: Z) (t: Z) (digits: Z) (j: Z) ,
  “ (j < digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= digits) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + j ) < cap) ”
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (k + j ) (app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) ((repeat_Z (0) (j)))) )
  **  (CharArray.undef_seg out (k + j ) cap )
|--
  “ ((k + j ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + j )) ”
.

Definition p015_string_sequence_safety_wit_28 := 
forall (out: Z) (i: Z) (cap: Z) (k: Z) (fill: Z) (t: Z) (digits: Z) (j: Z) ,
  “ (j < digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= digits) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + j ) < cap) ”
  &&  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (k + j ) (app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) ((repeat_Z (0) (j)))) )
  **  (CharArray.undef_seg out (k + j ) cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p015_string_sequence_safety_wit_29 := 
forall (out: Z) (i: Z) (cap: Z) (k: Z) (fill: Z) (t: Z) (digits: Z) (j: Z) ,
  “ (0 <= (k + j )) ” 
  &&  “ (j < digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= digits) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + j ) < cap) ”
  &&  (CharArray.full out ((k + j ) + 1 ) (app ((app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) ((repeat_Z (0) (j))))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out ((k + j ) + 1 ) cap )
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
|--
  “ ((j + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (j + 1 )) ”
.

Definition p015_string_sequence_safety_wit_30 := 
forall (out: Z) (i: Z) (t: Z) (out_digits: (@list Z)) (cap: Z) (k: Z) (j: Z) (digits: Z) (fill: Z) ,
  “ (0 <= fill) ” 
  &&  “ (fill <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + digits ) < cap) ” 
  &&  “ (base_fill_full_state i 10 t fill out_digits ) ”
  &&  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (k + digits ) (app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) (out_digits)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p015_string_sequence_safety_wit_31 := 
forall (out: Z) (i: Z) (t: Z) (out_digits: (@list Z)) (cap: Z) (k: Z) (j: Z) (digits: Z) (fill: Z) ,
  “ (t > 0) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (fill <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + digits ) < cap) ” 
  &&  “ (base_fill_full_state i 10 t fill out_digits ) ”
  &&  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (k + digits ) (app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) (out_digits)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  “ ((fill - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (fill - 1 )) ”
.

Definition p015_string_sequence_safety_wit_32 := 
forall (out: Z) (i: Z) (t: Z) (out_digits: (@list Z)) (cap: Z) (k: Z) (j: Z) (digits: Z) (fill: Z) ,
  “ (t > 0) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (fill <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + digits ) < cap) ” 
  &&  “ (base_fill_full_state i 10 t fill out_digits ) ”
  &&  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (k + digits ) (app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) (out_digits)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition p015_string_sequence_safety_wit_33 := 
forall (out: Z) (i: Z) (t: Z) (out_digits: (@list Z)) (cap: Z) (k: Z) (j: Z) (digits: Z) (fill: Z) ,
  “ (t > 0) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (fill <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + digits ) < cap) ” 
  &&  “ (base_fill_full_state i 10 t fill out_digits ) ”
  &&  ((( &( "fill" ) )) # Int  |-> (fill - 1 ))
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (k + digits ) (app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) (out_digits)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  “ ((k + (fill - 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + (fill - 1 ) )) ”
.

Definition p015_string_sequence_safety_wit_34 := 
forall (out: Z) (i: Z) (t: Z) (out_digits: (@list Z)) (cap: Z) (k: Z) (j: Z) (digits: Z) (fill: Z) ,
  “ (t > 0) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (fill <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + digits ) < cap) ” 
  &&  “ (base_fill_full_state i 10 t fill out_digits ) ”
  &&  ((( &( "fill" ) )) # Int  |-> (fill - 1 ))
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (k + digits ) (app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) (out_digits)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  “ ((48 + (t % ( 10 ) ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (48 + (t % ( 10 ) ) )) ”
.

Definition p015_string_sequence_safety_wit_35 := 
forall (out: Z) (i: Z) (t: Z) (out_digits: (@list Z)) (cap: Z) (k: Z) (j: Z) (digits: Z) (fill: Z) ,
  “ (t > 0) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (fill <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + digits ) < cap) ” 
  &&  “ (base_fill_full_state i 10 t fill out_digits ) ”
  &&  ((( &( "fill" ) )) # Int  |-> (fill - 1 ))
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (k + digits ) (app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) (out_digits)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  “ ((t <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition p015_string_sequence_safety_wit_36 := 
forall (out: Z) (i: Z) (t: Z) (out_digits: (@list Z)) (cap: Z) (k: Z) (j: Z) (digits: Z) (fill: Z) ,
  “ (t > 0) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (fill <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + digits ) < cap) ” 
  &&  “ (base_fill_full_state i 10 t fill out_digits ) ”
  &&  ((( &( "fill" ) )) # Int  |-> (fill - 1 ))
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (k + digits ) (app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) (out_digits)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  “ (48 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 48) ”
.

Definition p015_string_sequence_safety_wit_37 := 
forall (out: Z) (i: Z) (t: Z) (out_digits: (@list Z)) (cap: Z) (k: Z) (j: Z) (digits: Z) (fill: Z) ,
  “ (t > 0) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (fill <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + digits ) < cap) ” 
  &&  “ (base_fill_full_state i 10 t fill out_digits ) ”
  &&  ((( &( "fill" ) )) # Int  |-> (fill - 1 ))
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (k + digits ) (app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) (out_digits)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition p015_string_sequence_safety_wit_38 := 
forall (out: Z) (i: Z) (t: Z) (out_digits: (@list Z)) (cap: Z) (k: Z) (j: Z) (digits: Z) (fill: Z) ,
  “ (0 <= (k + digits )) ” 
  &&  “ (t > 0) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (fill <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + digits ) < cap) ” 
  &&  “ (base_fill_full_state i 10 t fill out_digits ) ”
  &&  (CharArray.full out (k + digits ) (replace_Znth ((k + (fill - 1 ) )) ((signed_last_nbits ((48 + (t % ( 10 ) ) )) (8))) ((app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) (out_digits)))) )
  **  ((( &( "fill" ) )) # Int  |-> (fill - 1 ))
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  “ ((t <> (INT_MIN)) \/ (10 <> (-1))) ” 
  &&  “ (10 <> 0) ”
.

Definition p015_string_sequence_safety_wit_39 := 
forall (out: Z) (i: Z) (t: Z) (out_digits: (@list Z)) (cap: Z) (k: Z) (j: Z) (digits: Z) (fill: Z) ,
  “ (0 <= (k + digits )) ” 
  &&  “ (t > 0) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (fill <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + digits ) < cap) ” 
  &&  “ (base_fill_full_state i 10 t fill out_digits ) ”
  &&  (CharArray.full out (k + digits ) (replace_Znth ((k + (fill - 1 ) )) ((signed_last_nbits ((48 + (t % ( 10 ) ) )) (8))) ((app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) (out_digits)))) )
  **  ((( &( "fill" ) )) # Int  |-> (fill - 1 ))
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  “ (10 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 10) ”
.

Definition p015_string_sequence_safety_wit_40 := 
forall (out: Z) (i: Z) (t: Z) (out_digits: (@list Z)) (cap: Z) (k: Z) (j: Z) (digits: Z) (fill: Z) ,
  “ (t <= 0) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (fill <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + digits ) < cap) ” 
  &&  “ (base_fill_full_state i 10 t fill out_digits ) ”
  &&  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (k + digits ) (app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) (out_digits)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  “ ((k + digits ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (k + digits )) ”
.

Definition p015_string_sequence_safety_wit_41 := 
forall (out: Z) (i: Z) (t: Z) (out_digits: (@list Z)) (cap: Z) (k: Z) (j: Z) (digits: Z) (fill: Z) ,
  “ (t <= 0) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (fill <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + digits ) < cap) ” 
  &&  “ (base_fill_full_state i 10 t fill out_digits ) ”
  &&  ((( &( "fill" ) )) # Int  |-> fill)
  **  ((( &( "digits" ) )) # Int  |-> digits)
  **  ((( &( "j" ) )) # Int  |-> j)
  **  ((( &( "k" ) )) # Int  |-> (k + digits ))
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "t" ) )) # Int  |-> t)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out (k + digits ) (app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) (out_digits)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition p015_string_sequence_safety_wit_42 := 
forall (out: Z) (cap: Z) (k: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) (n: Z) (i: Z) ,
  “ (i > n) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n + 1 )) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < cap) ”
  &&  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "n" ) )) # Int  |-> n)
  **  ((( &( "k" ) )) # Int  |-> k)
  **  ((( &( "cap" ) )) # Int  |-> cap)
  **  ((( &( "out" ) )) # Ptr  |-> out)
  **  (CharArray.full out k (sequence_prefix (i)) )
  **  (CharArray.undef_seg out k cap )
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition p015_string_sequence_entail_wit_1 := 
forall (n_pre: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre n_pre ) ” 
  &&  “ (sequence_output_bound n_pre ) ”
  &&  (CharArray.undef_seg retval (0 + 1 ) ((12 * (n_pre + 1 ) ) + 1 ) )
  **  (((retval + (0 * sizeof(CHAR) ) )) # Char  |-> 48)
|--
  “ (1 <= 1) ” 
  &&  “ (1 <= (n_pre + 1 )) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 < ((12 * (n_pre + 1 ) ) + 1 )) ”
  &&  (CharArray.full retval 1 (sequence_prefix (1)) )
  **  (CharArray.undef_seg retval 1 ((12 * (n_pre + 1 ) ) + 1 ) )
.

Definition p015_string_sequence_entail_wit_2 := 
forall (out: Z) (cap: Z) (k: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) (n: Z) (i: Z) ,
  “ (i <= n) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n + 1 )) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < cap) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  (CharArray.full out k (sequence_prefix (i)) )
  **  (CharArray.undef_seg out k cap )
|--
  “ (0 <= i) ” 
  &&  “ (0 <= 0) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < cap) ”
  &&  (CharArray.full out k (sequence_prefix (i)) )
  **  (CharArray.undef_seg out k cap )
.

Definition p015_string_sequence_entail_wit_3 := 
forall (out: Z) (i: Z) (cap: Z) (k: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) ,
  “ (t > 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < cap) ”
  &&  (CharArray.full out k (sequence_prefix (i)) )
  **  (CharArray.undef_seg out k cap )
|--
  “ (0 <= (t ÷ 10 )) ” 
  &&  “ (0 <= (digits + 1 )) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < cap) ”
  &&  (CharArray.full out k (sequence_prefix (i)) )
  **  (CharArray.undef_seg out k cap )
.

Definition p015_string_sequence_entail_wit_4 := 
forall (out: Z) (i: Z) (cap: Z) (k: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) ,
  “ (0 <= k) ” 
  &&  “ (t <= 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < cap) ”
  &&  (CharArray.full out (k + 1 ) (app ((sequence_prefix (i))) ((cons (32) (nil)))) )
  **  (CharArray.undef_seg out (k + 1 ) cap )
|--
  “ (0 <= 0) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= (k + 1 )) ” 
  &&  “ (((k + 1 ) + 0 ) < cap) ”
  &&  (CharArray.full out ((k + 1 ) + 0 ) (app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) ((repeat_Z (0) (0)))) )
  **  (CharArray.undef_seg out ((k + 1 ) + 0 ) cap )
.

Definition p015_string_sequence_entail_wit_5 := 
forall (out: Z) (i: Z) (cap: Z) (k: Z) (fill: Z) (t: Z) (digits: Z) (j: Z) ,
  “ (0 <= (k + j )) ” 
  &&  “ (j < digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= digits) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + j ) < cap) ”
  &&  (CharArray.full out ((k + j ) + 1 ) (app ((app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) ((repeat_Z (0) (j))))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out ((k + j ) + 1 ) cap )
|--
  “ (0 <= (j + 1 )) ” 
  &&  “ ((j + 1 ) <= digits) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + (j + 1 ) ) < cap) ”
  &&  (CharArray.full out (k + (j + 1 ) ) (app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) ((repeat_Z (0) ((j + 1 ))))) )
  **  (CharArray.undef_seg out (k + (j + 1 ) ) cap )
.

Definition p015_string_sequence_entail_wit_6 := 
forall (out: Z) (i: Z) (cap: Z) (k: Z) (fill: Z) (t: Z) (digits: Z) (j: Z) ,
  “ (j >= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= digits) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + j ) < cap) ”
  &&  (CharArray.full out (k + j ) (app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) ((repeat_Z (0) (j)))) )
  **  (CharArray.undef_seg out (k + j ) cap )
|--
  EX (out_digits: (@list Z)) ,
  “ (0 <= digits) ” 
  &&  “ (digits <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + digits ) < cap) ” 
  &&  “ (base_fill_full_state i 10 i digits out_digits ) ”
  &&  (CharArray.full out (k + digits ) (app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) (out_digits)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
.

Definition p015_string_sequence_entail_wit_7 := 
forall (out: Z) (i: Z) (t: Z) (out_digits_2: (@list Z)) (cap: Z) (k: Z) (j: Z) (digits: Z) (fill: Z) ,
  “ (0 <= (k + digits )) ” 
  &&  “ (t > 0) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (fill <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + digits ) < cap) ” 
  &&  “ (base_fill_full_state i 10 t fill out_digits_2 ) ”
  &&  (CharArray.full out (k + digits ) (replace_Znth ((k + (fill - 1 ) )) ((signed_last_nbits ((48 + (t % ( 10 ) ) )) (8))) ((app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) (out_digits_2)))) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  EX (out_digits: (@list Z)) ,
  “ (0 <= (fill - 1 )) ” 
  &&  “ ((fill - 1 ) <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + digits ) < cap) ” 
  &&  “ (base_fill_full_state i 10 (t ÷ 10 ) (fill - 1 ) out_digits ) ”
  &&  (CharArray.full out (k + digits ) (app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) (out_digits)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
.

Definition p015_string_sequence_entail_wit_8 := 
forall (out: Z) (i: Z) (t: Z) (out_digits: (@list Z)) (cap: Z) (k: Z) (j: Z) (digits: Z) (fill: Z) ,
  “ (t <= 0) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (fill <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + digits ) < cap) ” 
  &&  “ (base_fill_full_state i 10 t fill out_digits ) ”
  &&  (CharArray.full out (k + digits ) (app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) (out_digits)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  EX (n: Z) ,
  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (n + 1 )) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= (k + digits )) ” 
  &&  “ ((k + digits ) < cap) ”
  &&  ((( &( "n" ) )) # Int  |-> n)
  **  (CharArray.full out (k + digits ) (sequence_prefix ((i + 1 ))) )
  **  (CharArray.undef_seg out (k + digits ) cap )
.

Definition p015_string_sequence_return_wit_1 := 
forall (n_pre: Z) (out: Z) (cap_2: Z) (k_2: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) (n: Z) (i: Z) ,
  “ (0 <= k_2) ” 
  &&  “ (i > n) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n + 1 )) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k_2) ” 
  &&  “ (k_2 < cap_2) ”
  &&  (CharArray.full out (k_2 + 1 ) (app ((sequence_prefix (i))) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (k_2 + 1 ) cap_2 )
|--
  EX (cap: Z)  (out_l: (@list Z))  (len: Z) ,
  “ forall (k: Z) , (((0 <= k) /\ (k < len)) -> ((Znth (k) (out_l) (0)) <> 0)) ” 
  &&  “ (cap = ((12 * (n_pre + 1 ) ) + 1 )) ” 
  &&  “ (len = (Zlength (out_l))) ” 
  &&  “ (problem_15_spec n_pre out_l ) ”
  &&  (CharArray.full out (len + 1 ) (app (out_l) ((cons (0) (nil)))) )
  **  (CharArray.undef_seg out (len + 1 ) cap )
.

Definition p015_string_sequence_partial_solve_wit_1_pure := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre n_pre ) ” 
  &&  “ (sequence_output_bound n_pre ) ”
  &&  ((( &( "out" ) )) # Ptr  |->_)
  **  ((( &( "cap" ) )) # Int  |-> ((12 * (n_pre + 1 ) ) + 1 ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
|--
  “ (((12 * (n_pre + 1 ) ) + 1 ) > 0) ”
.

Definition p015_string_sequence_partial_solve_wit_1_aux := 
forall (n_pre: Z) ,
  “ (0 <= n_pre) ” 
  &&  “ (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre n_pre ) ” 
  &&  “ (sequence_output_bound n_pre ) ”
  &&  emp
|--
  “ (((12 * (n_pre + 1 ) ) + 1 ) > 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre n_pre ) ” 
  &&  “ (sequence_output_bound n_pre ) ”
  &&  emp
.

Definition p015_string_sequence_partial_solve_wit_1 := p015_string_sequence_partial_solve_wit_1_pure -> p015_string_sequence_partial_solve_wit_1_aux.

Definition p015_string_sequence_partial_solve_wit_2 := 
forall (n_pre: Z) (retval: Z) ,
  “ (retval <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre n_pre ) ” 
  &&  “ (sequence_output_bound n_pre ) ”
  &&  (CharArray.undef_full retval ((12 * (n_pre + 1 ) ) + 1 ) )
|--
  “ (retval <> 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (((12 * (n_pre + 1 ) ) + 1 ) < INT_MAX) ” 
  &&  “ (problem_15_pre n_pre ) ” 
  &&  “ (sequence_output_bound n_pre ) ”
  &&  (((retval + (0 * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i retval 0 0 ((12 * (n_pre + 1 ) ) + 1 ) )
.

Definition p015_string_sequence_partial_solve_wit_3 := 
forall (out: Z) (i: Z) (cap: Z) (k: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) ,
  “ (t <= 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < cap) ”
  &&  (CharArray.full out k (sequence_prefix (i)) )
  **  (CharArray.undef_seg out k cap )
|--
  “ (0 <= k) ” 
  &&  “ (t <= 0) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < cap) ”
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out k k cap )
  **  (CharArray.full out k (sequence_prefix (i)) )
.

Definition p015_string_sequence_partial_solve_wit_4 := 
forall (out: Z) (i: Z) (cap: Z) (k: Z) (fill: Z) (t: Z) (digits: Z) (j: Z) ,
  “ (j < digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= digits) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + j ) < cap) ”
  &&  (CharArray.full out (k + j ) (app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) ((repeat_Z (0) (j)))) )
  **  (CharArray.undef_seg out (k + j ) cap )
|--
  “ (0 <= (k + j )) ” 
  &&  “ (j < digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (j <= digits) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + j ) < cap) ”
  &&  (((out + ((k + j ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out (k + j ) (k + j ) cap )
  **  (CharArray.full out (k + j ) (app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) ((repeat_Z (0) (j)))) )
.

Definition p015_string_sequence_partial_solve_wit_5 := 
forall (out: Z) (i: Z) (t: Z) (out_digits: (@list Z)) (cap: Z) (k: Z) (j: Z) (digits: Z) (fill: Z) ,
  “ (t > 0) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (fill <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + digits ) < cap) ” 
  &&  “ (base_fill_full_state i 10 t fill out_digits ) ”
  &&  (CharArray.full out (k + digits ) (app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) (out_digits)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
|--
  “ (0 <= (k + digits )) ” 
  &&  “ (t > 0) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (fill <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (1 <= k) ” 
  &&  “ ((k + digits ) < cap) ” 
  &&  “ (base_fill_full_state i 10 t fill out_digits ) ”
  &&  (((out + ((k + (fill - 1 ) ) * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.missing_i out (k + (fill - 1 ) ) 0 (k + digits ) (app ((app ((sequence_prefix (i))) ((cons (32) (nil))))) (out_digits)) )
  **  (CharArray.undef_seg out (k + digits ) cap )
.

Definition p015_string_sequence_partial_solve_wit_6 := 
forall (out: Z) (cap: Z) (k: Z) (fill: Z) (j: Z) (digits: Z) (t: Z) (n: Z) (i: Z) ,
  “ (i > n) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n + 1 )) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < cap) ”
  &&  (CharArray.full out k (sequence_prefix (i)) )
  **  (CharArray.undef_seg out k cap )
|--
  “ (0 <= k) ” 
  &&  “ (i > n) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (n + 1 )) ” 
  &&  “ (0 <= t) ” 
  &&  “ (0 <= digits) ” 
  &&  “ (0 <= j) ” 
  &&  “ (0 <= fill) ” 
  &&  “ (1 <= k) ” 
  &&  “ (k < cap) ”
  &&  (((out + (k * sizeof(CHAR) ) )) # Char  |->_)
  **  (CharArray.undef_missing_i out k k cap )
  **  (CharArray.full out k (sequence_prefix (i)) )
.

Module Type VC_Correct.

Include char_array_Strategy_Correct.

Axiom proof_of_p015_string_sequence_safety_wit_1 : p015_string_sequence_safety_wit_1.
Axiom proof_of_p015_string_sequence_safety_wit_2 : p015_string_sequence_safety_wit_2.
Axiom proof_of_p015_string_sequence_safety_wit_3 : p015_string_sequence_safety_wit_3.
Axiom proof_of_p015_string_sequence_safety_wit_4 : p015_string_sequence_safety_wit_4.
Axiom proof_of_p015_string_sequence_safety_wit_5 : p015_string_sequence_safety_wit_5.
Axiom proof_of_p015_string_sequence_safety_wit_6 : p015_string_sequence_safety_wit_6.
Axiom proof_of_p015_string_sequence_safety_wit_7 : p015_string_sequence_safety_wit_7.
Axiom proof_of_p015_string_sequence_safety_wit_8 : p015_string_sequence_safety_wit_8.
Axiom proof_of_p015_string_sequence_safety_wit_9 : p015_string_sequence_safety_wit_9.
Axiom proof_of_p015_string_sequence_safety_wit_10 : p015_string_sequence_safety_wit_10.
Axiom proof_of_p015_string_sequence_safety_wit_11 : p015_string_sequence_safety_wit_11.
Axiom proof_of_p015_string_sequence_safety_wit_12 : p015_string_sequence_safety_wit_12.
Axiom proof_of_p015_string_sequence_safety_wit_13 : p015_string_sequence_safety_wit_13.
Axiom proof_of_p015_string_sequence_safety_wit_14 : p015_string_sequence_safety_wit_14.
Axiom proof_of_p015_string_sequence_safety_wit_15 : p015_string_sequence_safety_wit_15.
Axiom proof_of_p015_string_sequence_safety_wit_16 : p015_string_sequence_safety_wit_16.
Axiom proof_of_p015_string_sequence_safety_wit_17 : p015_string_sequence_safety_wit_17.
Axiom proof_of_p015_string_sequence_safety_wit_18 : p015_string_sequence_safety_wit_18.
Axiom proof_of_p015_string_sequence_safety_wit_19 : p015_string_sequence_safety_wit_19.
Axiom proof_of_p015_string_sequence_safety_wit_20 : p015_string_sequence_safety_wit_20.
Axiom proof_of_p015_string_sequence_safety_wit_21 : p015_string_sequence_safety_wit_21.
Axiom proof_of_p015_string_sequence_safety_wit_22 : p015_string_sequence_safety_wit_22.
Axiom proof_of_p015_string_sequence_safety_wit_23 : p015_string_sequence_safety_wit_23.
Axiom proof_of_p015_string_sequence_safety_wit_24 : p015_string_sequence_safety_wit_24.
Axiom proof_of_p015_string_sequence_safety_wit_25 : p015_string_sequence_safety_wit_25.
Axiom proof_of_p015_string_sequence_safety_wit_26 : p015_string_sequence_safety_wit_26.
Axiom proof_of_p015_string_sequence_safety_wit_27 : p015_string_sequence_safety_wit_27.
Axiom proof_of_p015_string_sequence_safety_wit_28 : p015_string_sequence_safety_wit_28.
Axiom proof_of_p015_string_sequence_safety_wit_29 : p015_string_sequence_safety_wit_29.
Axiom proof_of_p015_string_sequence_safety_wit_30 : p015_string_sequence_safety_wit_30.
Axiom proof_of_p015_string_sequence_safety_wit_31 : p015_string_sequence_safety_wit_31.
Axiom proof_of_p015_string_sequence_safety_wit_32 : p015_string_sequence_safety_wit_32.
Axiom proof_of_p015_string_sequence_safety_wit_33 : p015_string_sequence_safety_wit_33.
Axiom proof_of_p015_string_sequence_safety_wit_34 : p015_string_sequence_safety_wit_34.
Axiom proof_of_p015_string_sequence_safety_wit_35 : p015_string_sequence_safety_wit_35.
Axiom proof_of_p015_string_sequence_safety_wit_36 : p015_string_sequence_safety_wit_36.
Axiom proof_of_p015_string_sequence_safety_wit_37 : p015_string_sequence_safety_wit_37.
Axiom proof_of_p015_string_sequence_safety_wit_38 : p015_string_sequence_safety_wit_38.
Axiom proof_of_p015_string_sequence_safety_wit_39 : p015_string_sequence_safety_wit_39.
Axiom proof_of_p015_string_sequence_safety_wit_40 : p015_string_sequence_safety_wit_40.
Axiom proof_of_p015_string_sequence_safety_wit_41 : p015_string_sequence_safety_wit_41.
Axiom proof_of_p015_string_sequence_safety_wit_42 : p015_string_sequence_safety_wit_42.
Axiom proof_of_p015_string_sequence_entail_wit_1 : p015_string_sequence_entail_wit_1.
Axiom proof_of_p015_string_sequence_entail_wit_2 : p015_string_sequence_entail_wit_2.
Axiom proof_of_p015_string_sequence_entail_wit_3 : p015_string_sequence_entail_wit_3.
Axiom proof_of_p015_string_sequence_entail_wit_4 : p015_string_sequence_entail_wit_4.
Axiom proof_of_p015_string_sequence_entail_wit_5 : p015_string_sequence_entail_wit_5.
Axiom proof_of_p015_string_sequence_entail_wit_6 : p015_string_sequence_entail_wit_6.
Axiom proof_of_p015_string_sequence_entail_wit_7 : p015_string_sequence_entail_wit_7.
Axiom proof_of_p015_string_sequence_entail_wit_8 : p015_string_sequence_entail_wit_8.
Axiom proof_of_p015_string_sequence_return_wit_1 : p015_string_sequence_return_wit_1.
Axiom proof_of_p015_string_sequence_partial_solve_wit_1_pure : p015_string_sequence_partial_solve_wit_1_pure.
Axiom proof_of_p015_string_sequence_partial_solve_wit_1 : p015_string_sequence_partial_solve_wit_1.
Axiom proof_of_p015_string_sequence_partial_solve_wit_2 : p015_string_sequence_partial_solve_wit_2.
Axiom proof_of_p015_string_sequence_partial_solve_wit_3 : p015_string_sequence_partial_solve_wit_3.
Axiom proof_of_p015_string_sequence_partial_solve_wit_4 : p015_string_sequence_partial_solve_wit_4.
Axiom proof_of_p015_string_sequence_partial_solve_wit_5 : p015_string_sequence_partial_solve_wit_5.
Axiom proof_of_p015_string_sequence_partial_solve_wit_6 : p015_string_sequence_partial_solve_wit_6.

End VC_Correct.
