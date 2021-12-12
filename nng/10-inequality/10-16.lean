intro h1,
cases h1 with c h2,
split,
use succ c,
rw add_succ,
rw ← succ_add,
exact h2,

intro h3,
cases h3 with d h4,
rw h4 at h2,
rw ← add_succ at h2,
rw add_assoc at h2,
rw succ_add at h2,
symmetry at h2,
have h5 := eq_zero_of_add_right_eq_self h2,
symmetry at h5,
apply zero_ne_succ (d+c),
exact h5,