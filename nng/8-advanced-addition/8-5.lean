intro h1,
induction t with v h2,
repeat {rw add_zero at h1},
exact h1,

repeat {rw add_succ at h1},
have h3:= succ_inj(h1),
have h4:= h2(h3),
exact h4,