induction b with c hc,
rw mul_zero,
rw zero_mul,
refl,

rw mul_succ,
rw succ_mul,
rw hc,
refl,