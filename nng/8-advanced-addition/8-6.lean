rw add_comm t a,
rw add_comm t b,
intro h1,
have h2:= add_right_cancel a t b(h1),
exact h2,