induction b with c hc,
rw add_zero,
rw mul_zero,
rw mul_zero,
refl,

rw mul_succ (succ a) c,
rw mul_succ a c,
rw hc,
rw succ_eq_add_one,
rw succ_eq_add_one,
rw ← add_assoc (a*c+c) a 1,
rw ← add_assoc (a*c+a) c 1,
rw add_right_comm (a*c) a c,
refl,