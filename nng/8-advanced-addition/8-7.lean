split,
intro h1,
have h2:= add_right_cancel a t b(h1),
exact h2,
intro h3,
rw h3,
refl,