induction n with m hm,
rw zero_add,
rw ← one_eq_succ_zero,
refl,

rw hm,
rw ← succ_add,
rw ← hm,
refl,