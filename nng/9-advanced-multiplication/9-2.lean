cases b,
right,
refl,

rw mul_succ at h,
rw add_comm at h,
have p:= add_right_eq_zero (h),
left,
exact p,