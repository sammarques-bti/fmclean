induction m with p hm,
rw pow_zero,
rw zero_mul,
rw pow_zero,
rw one_pow,
refl,

rw pow_succ,
rw succ_mul,
rw mul_pow,
rw hm,
rw pow_add,
refl,