intro h,
rw le_iff_exists_add at h ⊢,
cases h with c hc,
use succ c,
rw hc,
rw add_succ,
refl,