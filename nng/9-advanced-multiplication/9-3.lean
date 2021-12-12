split,
intro h1,
apply eq_zero_or_eq_zero_of_mul_eq_zero,
exact h1,

intro h2,
cases h2,
rw h2,
rw zero_mul,
refl,

rw h2,
rw mul_zero,
refl,