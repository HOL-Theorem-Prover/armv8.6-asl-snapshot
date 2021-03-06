(*Generated by Lem from ../../src/gen_lib/sail2_operators_mwords.lem.*)
open HolKernel Parse boolLib bossLib;
open lem_pervasives_extra_sailTheory lem_machine_wordTheory sail2_valuesTheory sail2_operatorsTheory sail2_prompt_monadTheory sail2_promptTheory;

val _ = numLib.prefer_num();



val _ = new_theory "sail2_operators_mwords"

(*open import Pervasives_extra*)
(*open import Machine_word*)
(*open import Sail2_values*)
(*open import Sail2_operators*)
(*open import Sail2_prompt_monad*)
(*open import Sail2_prompt*)
val _ = Define `
 ((uint_maybe:'a words$word ->(int)option) v=  (SOME (lem$w2ui v)))`;

val _ = Define `
 ((uint_fail:'a words$word -> 'b sail2_state_monad$sequential_state ->((int),'c)sail2_state_monad$result#'b sail2_state_monad$sequential_state) v=  (sail2_state_monad$returnS (lem$w2ui v)))`;

val _ = Define `
 ((uint_nondet:'a words$word -> 'b sail2_state_monad$sequential_state ->((int),'c)sail2_state_monad$result#'b sail2_state_monad$sequential_state) v=  (sail2_state_monad$returnS (lem$w2ui v)))`;

val _ = Define `
 ((sint_maybe:'a words$word ->(int)option) v=  (SOME (integer_word$w2i v)))`;

val _ = Define `
 ((sint_fail:'a words$word -> 'b sail2_state_monad$sequential_state ->((int),'c)sail2_state_monad$result#'b sail2_state_monad$sequential_state) v=  (sail2_state_monad$returnS (integer_word$w2i v)))`;

val _ = Define `
 ((sint_nondet:'a words$word -> 'b sail2_state_monad$sequential_state ->((int),'c)sail2_state_monad$result#'b sail2_state_monad$sequential_state) v=  (sail2_state_monad$returnS (integer_word$w2i v)))`;


(*val vec_of_bits_maybe    : forall 'a. Size 'a => list bitU -> maybe (mword 'a)*)
(*val vec_of_bits_fail     : forall 'rv 'a 'e. Size 'a => list bitU -> monad 'rv (mword 'a) 'e*)
(*val vec_of_bits_nondet   : forall 'rv 'a 'e. Size 'a => list bitU -> monad 'rv (mword 'a) 'e*)
(*val vec_of_bits_failwith : forall 'a. Size 'a => list bitU -> mword 'a*)
(*val vec_of_bits          : forall 'a. Size 'a => list bitU -> mword 'a*)
val _ = Define `
 ((vec_of_bits_maybe:(bitU)list ->('a words$word)option) bits=  (OPTION_MAP bitstring$v2w (just_list (MAP bool_of_bitU bits))))`;

val _ = Define `
 ((vec_of_bits_fail:(bitU)list -> 'rv sail2_state_monad$sequential_state ->(('a words$word),'e)sail2_state_monad$result#'rv sail2_state_monad$sequential_state) bits=  (sail2_state$of_bits_failS 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict bits))`;

val _ = Define `
 ((vec_of_bits_nondet:(bitU)list -> 'rv sail2_state_monad$sequential_state ->(('a words$word),'e)sail2_state_monad$result#'rv sail2_state_monad$sequential_state) bits=  (sail2_state$of_bits_nondetS 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict bits))`;

val _ = Define `
 ((vec_of_bits_failwith:(bitU)list -> 'a words$word) bits=  (of_bits_failwith 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict bits))`;

val _ = Define `
 ((vec_of_bits:(bitU)list -> 'a words$word) bits=  (of_bits_failwith 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict bits))`;


(*val access_vec_inc : forall 'a. Size 'a => mword 'a -> integer -> bitU*)
val _ = Define `
 ((access_vec_inc:'a words$word -> int -> bitU)= 
  (access_bv_inc instance_Sail2_values_Bitvector_Machine_word_mword_dict))`;


(*val access_vec_dec : forall 'a. Size 'a => mword 'a -> integer -> bitU*)
val _ = Define `
 ((access_vec_dec:'a words$word -> int -> bitU)= 
  (access_bv_dec instance_Sail2_values_Bitvector_Machine_word_mword_dict))`;


val _ = Define `
 ((update_vec_dec_maybe:'a words$word -> int -> bitU ->('a words$word)option) w i b=  (update_mword_dec w i b))`;

val _ = Define `
 ((update_vec_dec_fail:'a words$word -> int -> bitU -> 'b sail2_state_monad$sequential_state ->(('a words$word),'c)sail2_state_monad$result#'b sail2_state_monad$sequential_state) w i b=  (sail2_state_monad$bindS
  (sail2_state$bool_of_bitU_fail b) (\ b . 
  sail2_state_monad$returnS (update_mword_bool_dec w i b))))`;

val _ = Define `
 ((update_vec_dec_nondet:'a words$word -> int -> bitU -> 'b sail2_state_monad$sequential_state ->(('a words$word),'c)sail2_state_monad$result#'b sail2_state_monad$sequential_state) w i b=  (sail2_state_monad$bindS
  (sail2_state$bool_of_bitU_nondetS b) (\ b . 
  sail2_state_monad$returnS (update_mword_bool_dec w i b))))`;

val _ = Define `
 ((update_vec_dec:'a words$word -> int -> bitU -> 'a words$word) w i b=  (maybe_failwith (update_vec_dec_maybe w i b)))`;


val _ = Define `
 ((update_vec_inc_maybe:'a words$word -> int -> bitU ->('a words$word)option) w i b=  (update_mword_inc w i b))`;

val _ = Define `
 ((update_vec_inc_fail:'a words$word -> int -> bitU -> 'b sail2_state_monad$sequential_state ->(('a words$word),'c)sail2_state_monad$result#'b sail2_state_monad$sequential_state) w i b=  (sail2_state_monad$bindS
  (sail2_state$bool_of_bitU_fail b) (\ b . 
  sail2_state_monad$returnS (update_mword_bool_inc w i b))))`;

val _ = Define `
 ((update_vec_inc_nondet:'a words$word -> int -> bitU -> 'b sail2_state_monad$sequential_state ->(('a words$word),'c)sail2_state_monad$result#'b sail2_state_monad$sequential_state) w i b=  (sail2_state_monad$bindS
  (sail2_state$bool_of_bitU_nondetS b) (\ b . 
  sail2_state_monad$returnS (update_mword_bool_inc w i b))))`;

val _ = Define `
 ((update_vec_inc:'a words$word -> int -> bitU -> 'a words$word) w i b=  (maybe_failwith (update_vec_inc_maybe w i b)))`;


(*val subrange_vec_dec : forall 'a 'b. Size 'a, Size 'b => mword 'a -> integer -> integer -> mword 'b*)
val _ = Define `
 ((subrange_vec_dec:'a words$word -> int -> int -> 'b words$word) w i j=  (words$word_extract (nat_of_int i) (nat_of_int j) w))`;


(*val subrange_vec_inc : forall 'a 'b. Size 'a, Size 'b => mword 'a -> integer -> integer -> mword 'b*)
val _ = Define `
 ((subrange_vec_inc:'a words$word -> int -> int -> 'b words$word) w i j=  (subrange_vec_dec w ((int_of_num (words$word_len w) -( 1 : int)) - i) ((int_of_num (words$word_len w) -( 1 : int)) - j)))`;


(*val update_subrange_vec_dec : forall 'a 'b. Size 'a, Size 'b => mword 'a -> integer -> integer -> mword 'b -> mword 'a*)
val _ = Define `
 ((update_subrange_vec_dec:'a words$word -> int -> int -> 'b words$word -> 'a words$word) w i j w'=  (words$bit_field_insert (nat_of_int i) (nat_of_int j) w' w))`;


(*val update_subrange_vec_inc : forall 'a 'b. Size 'a, Size 'b => mword 'a -> integer -> integer -> mword 'b -> mword 'a*)
val _ = Define `
 ((update_subrange_vec_inc:'a words$word -> int -> int -> 'b words$word -> 'a words$word) w i j w'=  (update_subrange_vec_dec w ((int_of_num (words$word_len w) -( 1 : int)) - i) ((int_of_num (words$word_len w) -( 1 : int)) - j) w'))`;


(*val extz_vec : forall 'a 'b. Size 'a, Size 'b => integer -> mword 'a -> mword 'b*)
val _ = Define `
 ((extz_vec:int -> 'a words$word -> 'b words$word) _ w=  (words$w2w w))`;


(*val exts_vec : forall 'a 'b. Size 'a, Size 'b => integer -> mword 'a -> mword 'b*)
val _ = Define `
 ((exts_vec:int -> 'a words$word -> 'b words$word) _ w=  (words$sw2sw w))`;


(*val zero_extend : forall 'a 'b. Size 'a, Size 'b => mword 'a -> integer -> mword 'b*)
val _ = Define `
 ((zero_extend:'a words$word -> int -> 'b words$word) w _=  (words$w2w w))`;


(*val sign_extend : forall 'a 'b. Size 'a, Size 'b => mword 'a -> integer -> mword 'b*)
val _ = Define `
 ((sign_extend:'a words$word -> int -> 'b words$word) w _=  (words$sw2sw w))`;


(*val zeros : forall 'a. Size 'a => integer -> mword 'a*)
val _ = Define `
 ((zeros:int -> 'a words$word) _=  (words$n2w(( 0:num))))`;


(*val vector_truncate : forall 'a 'b. Size 'a, Size 'b => mword 'a -> integer -> mword 'b*)
val _ = Define `
 ((vector_truncate:'a words$word -> int -> 'b words$word) w _=  (words$w2w w))`;


(*val vector_truncateLSB : forall 'a 'b. Size 'a, Size 'b => mword 'a -> integer -> mword 'b*)
val _ = Define `
 ((vector_truncateLSB:'a words$word -> int -> 'b words$word) w len=
   (let len = (nat_of_int len) in
  let lo = (words$word_len w - len) in
  let hi = ((lo + len) -( 1 : num)) in
  words$word_extract hi lo w))`;


(*val concat_vec : forall 'a 'b 'c. Size 'a, Size 'b, Size 'c => mword 'a -> mword 'b -> mword 'c*)
val _ = Define `
 ((concat_vec:'a words$word -> 'b words$word -> 'c words$word)=  words$word_concat)`;


(*val cons_vec_bool : forall 'a 'b 'c. Size 'a, Size 'b => bool -> mword 'a -> mword 'b*)
val _ = Define `
 ((cons_vec_bool:bool -> 'a words$word -> 'b words$word) b w=  (bitstring$v2w (b :: bitstring$w2v w)))`;

val _ = Define `
 ((cons_vec_maybe:bitU -> 'c words$word ->('b words$word)option) b w=  (OPTION_MAP (\ b .  cons_vec_bool b w) (bool_of_bitU b)))`;

val _ = Define `
 ((cons_vec_fail:bitU -> 'c words$word -> 'd sail2_state_monad$sequential_state ->(('b words$word),'e)sail2_state_monad$result#'d sail2_state_monad$sequential_state) b w=  (sail2_state_monad$bindS (sail2_state$bool_of_bitU_fail b) (\ b .  sail2_state_monad$returnS (cons_vec_bool b w))))`;

val _ = Define `
 ((cons_vec_nondet:bitU -> 'c words$word -> 'd sail2_state_monad$sequential_state ->(('b words$word),'e)sail2_state_monad$result#'d sail2_state_monad$sequential_state) b w=  (sail2_state_monad$bindS (sail2_state$bool_of_bitU_nondetS b) (\ b .  sail2_state_monad$returnS (cons_vec_bool b w))))`;

val _ = Define `
 ((cons_vec:bitU -> 'a words$word -> 'b words$word) b w=  (maybe_failwith (cons_vec_maybe b w)))`;


(*val vec_of_bool : forall 'a. Size 'a => integer -> bool -> mword 'a*)
val _ = Define `
 ((vec_of_bool:int -> bool -> 'a words$word) _ b=  (bitstring$v2w [b]))`;

val _ = Define `
 ((vec_of_bit_maybe:int -> bitU ->('a words$word)option) len b=  (OPTION_MAP (vec_of_bool len) (bool_of_bitU b)))`;

val _ = Define `
 ((vec_of_bit_fail:int -> bitU -> 'b sail2_state_monad$sequential_state ->(('a words$word),'c)sail2_state_monad$result#'b sail2_state_monad$sequential_state) len b=  (sail2_state_monad$bindS (sail2_state$bool_of_bitU_fail b) (\ b .  sail2_state_monad$returnS (vec_of_bool len b))))`;

val _ = Define `
 ((vec_of_bit_nondet:int -> bitU -> 'b sail2_state_monad$sequential_state ->(('a words$word),'c)sail2_state_monad$result#'b sail2_state_monad$sequential_state) len b=  (sail2_state_monad$bindS (sail2_state$bool_of_bitU_nondetS b) (\ b .  sail2_state_monad$returnS (vec_of_bool len b))))`;

val _ = Define `
 ((vec_of_bit:int -> bitU -> 'a words$word) len b=  (maybe_failwith (vec_of_bit_maybe len b)))`;


(*val cast_bool_vec : bool -> mword ty1*)
val _ = Define `
 ((cast_bool_vec:bool ->(1)words$word) b=  (vec_of_bool(( 1 : int)) b))`;

val _ = Define `
 ((cast_unit_vec_maybe:bitU ->('a words$word)option) b=  (vec_of_bit_maybe(( 1 : int)) b))`;

val _ = Define `
 ((cast_unit_vec_fail:bitU -> 'a sail2_state_monad$sequential_state ->(((1)words$word),'b)sail2_state_monad$result#'a sail2_state_monad$sequential_state) b=  (sail2_state_monad$bindS (sail2_state$bool_of_bitU_fail b) (\ b .  sail2_state_monad$returnS (cast_bool_vec b))))`;

val _ = Define `
 ((cast_unit_vec_nondet:bitU -> 'a sail2_state_monad$sequential_state ->(((1)words$word),'b)sail2_state_monad$result#'a sail2_state_monad$sequential_state) b=  (sail2_state_monad$bindS (sail2_state$bool_of_bitU_nondetS b) (\ b .  sail2_state_monad$returnS (cast_bool_vec b))))`;

val _ = Define `
 ((cast_unit_vec:bitU -> 'a words$word) b=  (maybe_failwith (cast_unit_vec_maybe b)))`;


(*val msb : forall 'a. Size 'a => mword 'a -> bitU*)
val _ = Define `
 ((msb:'a words$word -> bitU)= 
  (most_significant instance_Sail2_values_Bitvector_Machine_word_mword_dict))`;


(*val int_of_vec : forall 'a. Size 'a => bool -> mword 'a -> integer*)
val _ = Define `
 ((int_of_vec:bool -> 'a words$word -> int) sign w=
   (if sign
  then integer_word$w2i w
  else lem$w2ui w))`;

val _ = Define `
 ((int_of_vec_maybe:bool -> 'a words$word ->(int)option) sign w=  (SOME (int_of_vec sign w)))`;

val _ = Define `
 ((int_of_vec_fail:bool -> 'a words$word -> 'b sail2_state_monad$sequential_state ->((int),'c)sail2_state_monad$result#'b sail2_state_monad$sequential_state) sign w=  (sail2_state_monad$returnS (int_of_vec sign w)))`;


(*val string_of_bits : forall 'a. Size 'a => mword 'a -> string*)
val _ = Define `
 ((string_of_bits:'a words$word -> string)= 
  (string_of_bv instance_Sail2_values_Bitvector_Machine_word_mword_dict))`;


(*val decimal_string_of_bits : forall 'a. Size 'a => mword 'a -> string*)
val _ = Define `
 ((decimal_string_of_bits:'a words$word -> string)= 
  (decimal_string_of_bv
     instance_Sail2_values_Bitvector_Machine_word_mword_dict))`;


(*val and_vec : forall 'a. Size 'a => mword 'a -> mword 'a -> mword 'a*)
(*val or_vec  : forall 'a. Size 'a => mword 'a -> mword 'a -> mword 'a*)
(*val xor_vec : forall 'a. Size 'a => mword 'a -> mword 'a -> mword 'a*)
(*val not_vec : forall 'a. Size 'a => mword 'a -> mword 'a*)
val _ = Define `
 ((and_vec:'a words$word -> 'a words$word -> 'a words$word)=  words$word_and)`;

val _ = Define `
 ((or_vec:'a words$word -> 'a words$word -> 'a words$word)=   words$word_or)`;

val _ = Define `
 ((xor_vec:'a words$word -> 'a words$word -> 'a words$word)=  words$word_xor)`;

val _ = Define `
 ((not_vec:'a words$word -> 'a words$word)=  words$word_1comp)`;


(*val add_vec   : forall 'a. Size 'a => mword 'a -> mword 'a -> mword 'a*)
(*val adds_vec  : forall 'a. Size 'a => mword 'a -> mword 'a -> mword 'a*)
(*val sub_vec   : forall 'a. Size 'a => mword 'a -> mword 'a -> mword 'a*)
(*val subs_vec  : forall 'a. Size 'a => mword 'a -> mword 'a -> mword 'a*)
(*val mult_vec  : forall 'a 'b. Size 'a, Size 'b => mword 'a -> mword 'a -> mword 'b*)
(*val mults_vec : forall 'a 'b. Size 'a, Size 'b => mword 'a -> mword 'a -> mword 'b*)
val _ = Define `
 ((add_vec:'a words$word -> 'a words$word -> 'a words$word)   l r=  (integer_word$i2w ((int_of_mword F l) + (int_of_mword F r))))`;

val _ = Define `
 ((adds_vec:'a words$word -> 'a words$word -> 'a words$word)  l r=  (integer_word$i2w ((int_of_mword T l) + (int_of_mword T r))))`;

val _ = Define `
 ((sub_vec:'a words$word -> 'a words$word -> 'a words$word)   l r=  (integer_word$i2w ((int_of_mword F l) - (int_of_mword F r))))`;

val _ = Define `
 ((subs_vec:'a words$word -> 'a words$word -> 'a words$word)  l r=  (integer_word$i2w ((int_of_mword T l) - (int_of_mword T r))))`;

val _ = Define `
 ((mult_vec:'a words$word -> 'a words$word -> 'b words$word)  l r=  (integer_word$i2w ((int_of_mword F (words$w2w l :  'b words$word)) * (int_of_mword F (words$w2w r :  'b words$word)))))`;

val _ = Define `
 ((mults_vec:'a words$word -> 'a words$word -> 'b words$word) l r=  (integer_word$i2w ((int_of_mword T (words$sw2sw l :  'b words$word)) * (int_of_mword T (words$sw2sw r :  'b words$word)))))`;


(*val add_vec_int   : forall 'a. Size 'a => mword 'a -> integer -> mword 'a*)
(*val sub_vec_int   : forall 'a. Size 'a => mword 'a -> integer -> mword 'a*)
(*val mult_vec_int  : forall 'a 'b. Size 'a, Size 'b => mword 'a -> integer -> mword 'b*)
val _ = Define `
 ((add_vec_int:'a words$word -> int -> 'a words$word)   l r=  (arith_op_bv_int 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict (+)   F l r))`;

val _ = Define `
 ((sub_vec_int:'a words$word -> int -> 'a words$word)   l r=  (arith_op_bv_int 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict (-) F l r))`;

val _ = Define `
 ((mult_vec_int:'a words$word -> int -> 'b words$word)  l r=  (arith_op_bv_int 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict ( * )  F (words$w2w l :  'b words$word) r))`;


(*val add_int_vec   : forall 'a. Size 'a => integer -> mword 'a -> mword 'a*)
(*val sub_int_vec   : forall 'a. Size 'a => integer -> mword 'a -> mword 'a*)
(*val mult_int_vec  : forall 'a 'b. Size 'a, Size 'b => integer -> mword 'a -> mword 'b*)
val _ = Define `
 ((add_int_vec:int -> 'a words$word -> 'a words$word)   l r=  (arith_op_int_bv 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict (+)   F l r))`;

val _ = Define `
 ((sub_int_vec:int -> 'a words$word -> 'a words$word)   l r=  (arith_op_int_bv 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict (-) F l r))`;

val _ = Define `
 ((mult_int_vec:int -> 'a words$word -> 'b words$word)  l r=  (arith_op_int_bv 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict ( * )  F l (words$w2w r :  'b words$word)))`;


(*val add_vec_bool  : forall 'a. Size 'a => mword 'a -> bool -> mword 'a*)
(*val adds_vec_bool : forall 'a. Size 'a => mword 'a -> bool -> mword 'a*)
(*val sub_vec_bool  : forall 'a. Size 'a => mword 'a -> bool -> mword 'a*)
(*val subs_vec_bool : forall 'a. Size 'a => mword 'a -> bool -> mword 'a*)

val _ = Define `
 ((add_vec_bool:'a words$word -> bool -> 'a words$word)        l r=  (arith_op_bv_bool 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict (+) F l r))`;

val _ = Define `
 ((add_vec_bit_maybe:'a words$word -> bitU ->('a words$word)option)   l r=  (OPTION_MAP (add_vec_bool l) (bool_of_bitU r)))`;

val _ = Define `
 ((add_vec_bit_fail:'a words$word -> bitU -> 'b sail2_state_monad$sequential_state ->(('a words$word),'c)sail2_state_monad$result#'b sail2_state_monad$sequential_state)    l r=  (sail2_state_monad$bindS (sail2_state$bool_of_bitU_fail r) (\ r .  sail2_state_monad$returnS (add_vec_bool l r))))`;

val _ = Define `
 ((add_vec_bit_nondet:'a words$word -> bitU -> 'b sail2_state_monad$sequential_state ->(('a words$word),'c)sail2_state_monad$result#'b sail2_state_monad$sequential_state)  l r=  (sail2_state_monad$bindS (sail2_state$bool_of_bitU_nondetS r) (\ r .  sail2_state_monad$returnS (add_vec_bool l r))))`;

val _ = Define `
 ((add_vec_bit:'a words$word -> bitU -> 'a words$word)         l r=  (maybe_failwith (add_vec_bit_maybe  l r)))`;


val _ = Define `
 ((adds_vec_bool:'a words$word -> bool -> 'a words$word)       l r=  (arith_op_bv_bool 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict (+) T  l r))`;

val _ = Define `
 ((adds_vec_bit_maybe:'a words$word -> bitU ->('a words$word)option)  l r=  (OPTION_MAP (adds_vec_bool l) (bool_of_bitU r)))`;

val _ = Define `
 ((adds_vec_bit_fail:'a words$word -> bitU -> 'b sail2_state_monad$sequential_state ->(('a words$word),'c)sail2_state_monad$result#'b sail2_state_monad$sequential_state)   l r=  (sail2_state_monad$bindS (sail2_state$bool_of_bitU_fail r) (\ r .  sail2_state_monad$returnS (adds_vec_bool l r))))`;

val _ = Define `
 ((adds_vec_bit_nondet:'a words$word -> bitU -> 'b sail2_state_monad$sequential_state ->(('a words$word),'c)sail2_state_monad$result#'b sail2_state_monad$sequential_state) l r=  (sail2_state_monad$bindS (sail2_state$bool_of_bitU_nondetS r) (\ r .  sail2_state_monad$returnS (adds_vec_bool l r))))`;

val _ = Define `
 ((adds_vec_bit:'a words$word -> bitU -> 'a words$word)        l r=  (maybe_failwith (adds_vec_bit_maybe l r)))`;


val _ = Define `
 ((sub_vec_bool:'a words$word -> bool -> 'a words$word)        l r=  (arith_op_bv_bool 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict (-) F l r))`;

val _ = Define `
 ((sub_vec_bit_maybe:'a words$word -> bitU ->('a words$word)option)   l r=  (OPTION_MAP (sub_vec_bool l) (bool_of_bitU r)))`;

val _ = Define `
 ((sub_vec_bit_fail:'a words$word -> bitU -> 'b sail2_state_monad$sequential_state ->(('a words$word),'c)sail2_state_monad$result#'b sail2_state_monad$sequential_state)    l r=  (sail2_state_monad$bindS (sail2_state$bool_of_bitU_fail r) (\ r .  sail2_state_monad$returnS (sub_vec_bool l r))))`;

val _ = Define `
 ((sub_vec_bit_nondet:'a words$word -> bitU -> 'b sail2_state_monad$sequential_state ->(('a words$word),'c)sail2_state_monad$result#'b sail2_state_monad$sequential_state)  l r=  (sail2_state_monad$bindS (sail2_state$bool_of_bitU_nondetS r) (\ r .  sail2_state_monad$returnS (sub_vec_bool l r))))`;

val _ = Define `
 ((sub_vec_bit:'a words$word -> bitU -> 'a words$word)         l r=  (maybe_failwith (sub_vec_bit_maybe  l r)))`;


val _ = Define `
 ((subs_vec_bool:'a words$word -> bool -> 'a words$word)       l r=  (arith_op_bv_bool 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict (-) T  l r))`;

val _ = Define `
 ((subs_vec_bit_maybe:'a words$word -> bitU ->('a words$word)option)  l r=  (OPTION_MAP (subs_vec_bool l) (bool_of_bitU r)))`;

val _ = Define `
 ((subs_vec_bit_fail:'a words$word -> bitU -> 'b sail2_state_monad$sequential_state ->(('a words$word),'c)sail2_state_monad$result#'b sail2_state_monad$sequential_state)   l r=  (sail2_state_monad$bindS (sail2_state$bool_of_bitU_fail r) (\ r .  sail2_state_monad$returnS (subs_vec_bool l r))))`;

val _ = Define `
 ((subs_vec_bit_nondet:'a words$word -> bitU -> 'b sail2_state_monad$sequential_state ->(('a words$word),'c)sail2_state_monad$result#'b sail2_state_monad$sequential_state) l r=  (sail2_state_monad$bindS (sail2_state$bool_of_bitU_nondetS r) (\ r .  sail2_state_monad$returnS (subs_vec_bool l r))))`;

val _ = Define `
 ((subs_vec_bit:'a words$word -> bitU -> 'a words$word)        l r=  (maybe_failwith (subs_vec_bit_maybe  l r)))`;


(* TODO
val maybe_mword_of_bits_overflow : forall 'a. Size 'a => (list bitU * bitU * bitU) -> maybe (mword 'a * bitU * bitU)
let maybe_mword_of_bits_overflow (bits, overflow, carry) =
  Maybe.map (fun w -> (w, overflow, carry)) (of_bits bits)

val add_overflow_vec   : forall 'a. Size 'a => mword 'a -> mword 'a -> maybe (mword 'a * bitU * bitU)
val adds_overflow_vec  : forall 'a. Size 'a => mword 'a -> mword 'a -> maybe (mword 'a * bitU * bitU)
val sub_overflow_vec   : forall 'a. Size 'a => mword 'a -> mword 'a -> maybe (mword 'a * bitU * bitU)
val subs_overflow_vec  : forall 'a. Size 'a => mword 'a -> mword 'a -> maybe (mword 'a * bitU * bitU)
val mult_overflow_vec  : forall 'a. Size 'a => mword 'a -> mword 'a -> maybe (mword 'a * bitU * bitU)
val mults_overflow_vec : forall 'a. Size 'a => mword 'a -> mword 'a -> maybe (mword 'a * bitU * bitU)
let add_overflow_vec   l r = maybe_mword_of_bits_overflow (add_overflow_bv l r)
let adds_overflow_vec  l r = maybe_mword_of_bits_overflow (adds_overflow_bv l r)
let sub_overflow_vec   l r = maybe_mword_of_bits_overflow (sub_overflow_bv l r)
let subs_overflow_vec  l r = maybe_mword_of_bits_overflow (subs_overflow_bv l r)
let mult_overflow_vec  l r = maybe_mword_of_bits_overflow (mult_overflow_bv l r)
let mults_overflow_vec l r = maybe_mword_of_bits_overflow (mults_overflow_bv l r)

val add_overflow_vec_bit         : forall 'a. Size 'a => mword 'a -> bitU -> (mword 'a * bitU * bitU)
val add_overflow_vec_bit_signed  : forall 'a. Size 'a => mword 'a -> bitU -> (mword 'a * bitU * bitU)
val sub_overflow_vec_bit         : forall 'a. Size 'a => mword 'a -> bitU -> (mword 'a * bitU * bitU)
val sub_overflow_vec_bit_signed  : forall 'a. Size 'a => mword 'a -> bitU -> (mword 'a * bitU * bitU)
let add_overflow_vec_bit         = add_overflow_bv_bit
let add_overflow_vec_bit_signed  = add_overflow_bv_bit_signed
let sub_overflow_vec_bit         = sub_overflow_bv_bit
let sub_overflow_vec_bit_signed  = sub_overflow_bv_bit_signed*)

(*val shiftl       : forall 'a. Size 'a => mword 'a -> integer -> mword 'a*)
(*val shiftr       : forall 'a. Size 'a => mword 'a -> integer -> mword 'a*)
(*val arith_shiftr : forall 'a. Size 'a => mword 'a -> integer -> mword 'a*)
(*val rotl         : forall 'a. Size 'a => mword 'a -> integer -> mword 'a*)
(*val rotr         : forall 'a. Size 'a => mword 'a -> integer -> mword 'a*)
val _ = Define `
 ((shiftl:'a words$word -> int -> 'a words$word)=        shiftl_mword)`;

val _ = Define `
 ((shiftr:'a words$word -> int -> 'a words$word)=        shiftr_mword)`;

val _ = Define `
 ((arith_shiftr:'a words$word -> int -> 'a words$word)=  arith_shiftr_mword)`;

val _ = Define `
 ((rotl:'a words$word -> int -> 'a words$word)=          rotl_mword)`;

val _ = Define `
 ((rotr:'a words$word -> int -> 'a words$word)=          rotr_mword)`;


(*val mod_vec        : forall 'a. Size 'a => mword 'a -> mword 'a -> mword 'a*)
(*val mod_vec_maybe  : forall 'a. Size 'a => mword 'a -> mword 'a -> maybe (mword 'a)*)
(*val mod_vec_fail   : forall 'rv 'a 'e. Size 'a => mword 'a -> mword 'a -> monad 'rv (mword 'a) 'e*)
(*val mod_vec_nondet : forall 'rv 'a 'e. Size 'a => mword 'a -> mword 'a -> monad 'rv (mword 'a) 'e*)
val _ = Define `
 ((mod_vec:'a words$word -> 'a words$word -> 'a words$word)        l r=  (mod_mword l r))`;

val _ = Define `
 ((mod_vec_maybe:'a words$word -> 'a words$word ->('a words$word)option)  l r=  (mod_bv 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict l r))`;

val _ = Define `
 ((mod_vec_fail:'a words$word -> 'a words$word -> 'rv sail2_state_monad$sequential_state ->(('a words$word),'e)sail2_state_monad$result#'rv sail2_state_monad$sequential_state)   l r=  (sail2_state_monad$maybe_failS "mod_vec" (mod_bv 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict l r)))`;

val _ = Define `
 ((mod_vec_nondet:'a words$word -> 'a words$word -> 'rv sail2_state_monad$sequential_state ->(('a words$word),'e)sail2_state_monad$result#'rv sail2_state_monad$sequential_state) l r=
   ((case (mod_bv instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict l r) of
      SOME w => sail2_state_monad$returnS w
    | NONE => sail2_state$mword_nondetS () 
  )))`;


(*val quot_vec        : forall 'a. Size 'a => mword 'a -> mword 'a -> mword 'a*)
(*val quot_vec_maybe  : forall 'a. Size 'a => mword 'a -> mword 'a -> maybe (mword 'a)*)
(*val quot_vec_fail   : forall 'rv 'a 'e. Size 'a => mword 'a -> mword 'a -> monad 'rv (mword 'a) 'e*)
(*val quot_vec_nondet : forall 'rv 'a 'e. Size 'a => mword 'a -> mword 'a -> monad 'rv (mword 'a) 'e*)
val _ = Define `
 ((quot_vec:'a words$word -> 'a words$word -> 'a words$word)        l r=  (quot_mword l r))`;

val _ = Define `
 ((quot_vec_maybe:'a words$word -> 'a words$word ->('a words$word)option)  l r=  (quot_bv 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict l r))`;

val _ = Define `
 ((quot_vec_fail:'a words$word -> 'a words$word -> 'rv sail2_state_monad$sequential_state ->(('a words$word),'e)sail2_state_monad$result#'rv sail2_state_monad$sequential_state)   l r=  (sail2_state_monad$maybe_failS "quot_vec" (quot_bv 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict l r)))`;

val _ = Define `
 ((quot_vec_nondet:'a words$word -> 'a words$word -> 'rv sail2_state_monad$sequential_state ->(('a words$word),'e)sail2_state_monad$result#'rv sail2_state_monad$sequential_state) l r=
   ((case (quot_bv instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict l r) of
      SOME w => sail2_state_monad$returnS w
    | NONE => sail2_state$mword_nondetS () 
  )))`;


(*val quots_vec        : forall 'a. Size 'a => mword 'a -> mword 'a -> mword 'a*)
(*val quots_vec_maybe  : forall 'a. Size 'a => mword 'a -> mword 'a -> maybe (mword 'a)*)
(*val quots_vec_fail   : forall 'rv 'a 'e. Size 'a => mword 'a -> mword 'a -> monad 'rv (mword 'a) 'e*)
(*val quots_vec_nondet : forall 'rv 'a 'e. Size 'a => mword 'a -> mword 'a -> monad 'rv (mword 'a) 'e*)
val _ = Define `
 ((quots_vec:'a words$word -> 'a words$word -> 'a words$word)        l r=  (quots_mword l r))`;

val _ = Define `
 ((quots_vec_maybe:'a words$word -> 'a words$word ->('a words$word)option)  l r=  (quots_bv 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict l r))`;

val _ = Define `
 ((quots_vec_fail:'a words$word -> 'a words$word -> 'rv sail2_state_monad$sequential_state ->(('a words$word),'e)sail2_state_monad$result#'rv sail2_state_monad$sequential_state)   l r=  (sail2_state_monad$maybe_failS "quots_vec" (quots_bv 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict l r)))`;

val _ = Define `
 ((quots_vec_nondet:'a words$word -> 'a words$word -> 'rv sail2_state_monad$sequential_state ->(('a words$word),'e)sail2_state_monad$result#'rv sail2_state_monad$sequential_state) l r=
   ((case (quots_bv instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict l r) of
      SOME w => sail2_state_monad$returnS w
    | NONE => sail2_state$mword_nondetS () 
  )))`;


(*val mod_vec_int        : forall 'a. Size 'a => mword 'a -> integer -> mword 'a*)
(*val mod_vec_int_maybe  : forall 'a. Size 'a => mword 'a -> integer -> maybe (mword 'a)*)
(*val mod_vec_int_fail   : forall 'rv 'a 'e. Size 'a => mword 'a -> integer -> monad 'rv (mword 'a) 'e*)
(*val mod_vec_int_nondet : forall 'rv 'a 'e. Size 'a => mword 'a -> integer -> monad 'rv (mword 'a) 'e*)
val _ = Define `
 ((mod_vec_int:'a words$word -> int -> 'a words$word)        l r=  (mod_mword_int l r))`;

val _ = Define `
 ((mod_vec_int_maybe:'a words$word -> int ->('a words$word)option)  l r=  (mod_bv_int 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict l r))`;

val _ = Define `
 ((mod_vec_int_fail:'a words$word -> int -> 'rv sail2_state_monad$sequential_state ->(('a words$word),'e)sail2_state_monad$result#'rv sail2_state_monad$sequential_state)   l r=  (sail2_state_monad$maybe_failS "mod_vec_int" (mod_bv_int 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict l r)))`;

val _ = Define `
 ((mod_vec_int_nondet:'a words$word -> int -> 'rv sail2_state_monad$sequential_state ->(('a words$word),'e)sail2_state_monad$result#'rv sail2_state_monad$sequential_state) l r=
   ((case (mod_bv_int 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict l r) of
      SOME w => sail2_state_monad$returnS w
    | NONE => sail2_state$mword_nondetS () 
  )))`;


(*val quot_vec_int        : forall 'a. Size 'a => mword 'a -> integer -> mword 'a*)
(*val quot_vec_int_maybe  : forall 'a. Size 'a => mword 'a -> integer -> maybe (mword 'a)*)
(*val quot_vec_int_fail   : forall 'rv 'a 'e. Size 'a => mword 'a -> integer -> monad 'rv (mword 'a) 'e*)
(*val quot_vec_int_nondet : forall 'rv 'a 'e. Size 'a => mword 'a -> integer -> monad 'rv (mword 'a) 'e*)
val _ = Define `
 ((quot_vec_int:'a words$word -> int -> 'a words$word)        l r=  (quot_mword_int l r))`;

val _ = Define `
 ((quot_vec_int_maybe:'a words$word -> int ->('a words$word)option)  l r=  (quot_bv_int 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict l r))`;

val _ = Define `
 ((quot_vec_int_fail:'a words$word -> int -> 'rv sail2_state_monad$sequential_state ->(('a words$word),'e)sail2_state_monad$result#'rv sail2_state_monad$sequential_state)   l r=  (sail2_state_monad$maybe_failS "quot_vec_int" (quot_bv_int 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict l r)))`;

val _ = Define `
 ((quot_vec_int_nondet:'a words$word -> int -> 'rv sail2_state_monad$sequential_state ->(('a words$word),'e)sail2_state_monad$result#'rv sail2_state_monad$sequential_state) l r=
   ((case (quot_bv_int 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict instance_Sail2_values_Bitvector_Machine_word_mword_dict l r) of
      SOME w => sail2_state_monad$returnS w
    | NONE => sail2_state$mword_nondetS () 
  )))`;


(*val replicate_bits : forall 'a 'b. Size 'a, Size 'b => mword 'a -> integer -> mword 'b*)
val _ = Define `
 ((replicate_bits:'a words$word -> int -> 'b words$word) v count1=  (bitstring$v2w (repeat (bitstring$w2v v) count1)))`;


(*val duplicate_bool : forall 'a. Size 'a => bool -> integer -> mword 'a*)
val _ = Define `
 ((duplicate_bool:bool -> int -> 'a words$word)   b n=  (bitstring$v2w (repeat [b] n)))`;

val _ = Define `
 ((duplicate_maybe:bitU -> int ->('a words$word)option)  b n=  (OPTION_MAP (\ b .  duplicate_bool b n) (bool_of_bitU b)))`;

val _ = Define `
 ((duplicate_fail:bitU -> int -> 'b sail2_state_monad$sequential_state ->(('a words$word),'c)sail2_state_monad$result#'b sail2_state_monad$sequential_state)   b n=  (sail2_state_monad$bindS (sail2_state$bool_of_bitU_fail b) (\ b .  sail2_state_monad$returnS (duplicate_bool b n))))`;

val _ = Define `
 ((duplicate_nondet:bitU -> int -> 'b sail2_state_monad$sequential_state ->(('a words$word),'c)sail2_state_monad$result#'b sail2_state_monad$sequential_state) b n=  (sail2_state_monad$bindS (sail2_state$bool_of_bitU_nondetS b) (\ b .  sail2_state_monad$returnS (duplicate_bool b n))))`;

val _ = Define `
 ((duplicate:bitU -> int -> 'a words$word)        b n=  (maybe_failwith (duplicate_maybe b n)))`;


(*val reverse_endianness : forall 'a. Size 'a => mword 'a -> mword 'a*)
val _ = Define `
 ((reverse_endianness:'a words$word -> 'a words$word) v=  (bitstring$v2w (reverse_endianness_list (bitstring$w2v v))))`;


(*val get_slice_int : forall 'a. Size 'a => integer -> integer -> integer -> mword 'a*)
val _ = Define `
 ((get_slice_int:int -> int -> int -> 'a words$word)= 
  (get_slice_int_bv instance_Sail2_values_Bitvector_Machine_word_mword_dict))`;


(*val set_slice_int : forall 'a. Size 'a => integer -> integer -> integer -> mword 'a -> integer*)
val _ = Define `
 ((set_slice_int:int -> int -> int -> 'a words$word -> int)= 
  (set_slice_int_bv instance_Sail2_values_Bitvector_Machine_word_mword_dict))`;


(*val slice : forall 'a 'b. Size 'a, Size 'b => mword 'a -> integer -> integer -> mword 'b*)
val _ = Define `
 ((slice:'a words$word -> int -> int -> 'b words$word) v lo len=
   (subrange_vec_dec v ((lo + len) -( 1 : int)) lo))`;


(*val set_slice : forall 'a 'b. Size 'a, Size 'b => integer -> integer -> mword 'a -> integer -> mword 'b -> mword 'a*)
val _ = Define `
 ((set_slice:int -> int -> 'a words$word -> int -> 'b words$word -> 'a words$word) (out_len:ii) (slice_len:ii) out (n:ii) v=
   (update_subrange_vec_dec out ((n + slice_len) -( 1 : int)) n v))`;


(*val eq_vec    : forall 'a. Size 'a => mword 'a -> mword 'a -> bool*)
(*val neq_vec   : forall 'a. Size 'a => mword 'a -> mword 'a -> bool*)

(*val count_leading_zeros : forall 'a. Size 'a => mword 'a -> integer*)
val _ = Define `
 ((count_leading_zeros:'a words$word -> int) v=  (count_leading_zeros_bv 
  instance_Sail2_values_Bitvector_Machine_word_mword_dict v))`;

val _ = export_theory()

