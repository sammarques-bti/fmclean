intro h,
intro c,
cases h with d h,

use d,
rw h,
rw add_right_comm,
refl,