open HolKernel boolLib bossLib armv86aTheory monadsyntax
open stringTheory integerTheory arithmeticTheory intLib

val _ = new_theory "armv86a_termination";
val _ = Parse.set_grammar_ancestry ["armv86a"]

Type monad[pp] = ``:'a sequential_state ->
                      ('b, 'c) result # 'a sequential_state``;
Type monadR[pp] = ``:'a sequential_state ->
                      ('b, 'c + 'd) result # α sequential_state``;
Type M[pp] = ``:(regstate, 'a, exception) monad``;
Type MR[pp] = ``:(regstate, 'a, 'r, exception) monadR``;

val _ = enable_monad "sail2_state_monad";
val _ = enable_monadsyntax();

(******************************************************************************)

val (maybe_int_of_prefix_def, maybe_int_of_prefix_ind) = Defn.tprove_no_defn (
  (sail2_stringTheory.maybe_int_of_prefix_def,
   sail2_stringTheory.maybe_int_of_prefix_ind),
  WF_REL_TAC `measure STRLEN` >> EVAL_TAC >>
  fs[INT, INT_SUB_CALCULATE, INT_ADD_CALCULATE]);

Theorem maybe_int_of_prefix_def[compute] = maybe_int_of_prefix_def;
Theorem maybe_int_of_prefix_ind = maybe_int_of_prefix_ind;

val (n_leading_spaces_def, n_leading_spaces_ind) = Defn.tprove_no_defn (
  (sail2_stringTheory.n_leading_spaces_def,
   sail2_stringTheory.n_leading_spaces_ind),
  WF_REL_TAC `measure STRLEN` >> EVAL_TAC >>
  fs[INT_LT_NZ] >> rw[] >> Cases_on `STRLEN s` >> fs[] >>
  fs[INT, INT_SUB_CALCULATE, INT_ADD_CALCULATE]);

Theorem n_leading_spaces_def[compute] = n_leading_spaces_def;
Theorem n_leading_spaces_ind = n_leading_spaces_ind;

val (hex_str_aux_def, hex_str_aux_ind) = Defn.tprove_no_defn (
  (sail2_valuesTheory.hex_str_aux_def,
   sail2_valuesTheory.hex_str_aux_ind),
  WF_REL_TAC `measure FST` >> fs[]);

Theorem hex_str_aux_def[compute] = hex_str_aux_def;
Theorem hex_str_aux_ind = hex_str_aux_ind;

val (count_leading_zero_bits_def, count_leading_zero_bits_ind) = Defn.tprove_no_defn (
  (sail2_valuesTheory.count_leading_zero_bits_def,
   sail2_valuesTheory.count_leading_zero_bits_ind),
  WF_REL_TAC `measure LENGTH` >> fs[]);

Theorem count_leading_zero_bits_def[compute] = count_leading_zero_bits_def;
Theorem count_leading_zero_bits_ind = count_leading_zero_bits_ind;

val (rationalPowInteger_def, rationalPowInteger_ind) = Defn.tprove_no_defn (
  (lem_numTheory.rationalPowInteger_def,
   lem_numTheory.rationalPowInteger_ind),
   WF_REL_TAC `measure (Num o ABS o SND)` >> ARITH_TAC);

Theorem rationalPowInteger_def[compute] = rationalPowInteger_def;
Theorem rationalPowInteger_ind = rationalPowInteger_ind;

val (realPowInteger_def, realPowInteger_ind) = Defn.tprove_no_defn (
  (lem_numTheory.realPowInteger_def,
   lem_numTheory.realPowInteger_ind),
   WF_REL_TAC `measure (Num o ABS o SND)` >> ARITH_TAC);

Theorem realPowInteger_def[compute] = realPowInteger_def;
Theorem realPowInteger_ind = realPowInteger_ind;

val (splitAtAcc_def, splitAtAcc_ind) = Defn.tprove_no_defn (
  (lem_listTheory.splitAtAcc_def, lem_listTheory.splitAtAcc_ind),
  WF_REL_TAC `measure (λ (_,n,_). n)`);

Theorem splitAtAcc_def[compute] = splitAtAcc_def;
Theorem splitAtAcc_ind = splitAtAcc_ind;

val (catMaybes_def, catMaybes_ind) = Defn.tprove_no_defn (
  (lem_listTheory.catMaybes_def, lem_listTheory.catMaybes_ind),
  WF_REL_TAC `measure LENGTH` >> fs[]);

Theorem catMaybes_def[compute] = catMaybes_def;
Theorem catMaybes_ind = catMaybes_ind;

val (stringFromNatHelper_def, stringFromNatHelper_ind) = Defn.tprove_no_defn (
  (lem_string_extra_sailTheory.stringFromNatHelper_def,
   lem_string_extra_sailTheory.stringFromNatHelper_ind),
  WF_REL_TAC `measure FST` >> fs[]);

Theorem stringFromNatHelper_def[compute] = stringFromNatHelper_def;
Theorem stringFromNatHelper_ind = stringFromNatHelper_ind;

val (stringFromNaturalHelper_def, stringFromNaturalHelper_ind) = Defn.tprove_no_defn (
  (lem_string_extra_sailTheory.stringFromNaturalHelper_def,
   lem_string_extra_sailTheory.stringFromNaturalHelper_ind),
  WF_REL_TAC `measure FST` >> fs[]);

Theorem stringFromNaturalHelper_def[compute] = stringFromNaturalHelper_def;
Theorem stringFromNaturalHelper_ind = stringFromNaturalHelper_ind;

(******************************************************************************)

val _ = export_theory();

