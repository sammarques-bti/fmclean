  intro h1,
  cases h1 with h2 h3,
  cases h2 with c h4,
  cases c with d h5,
  rw h4 at h3,
  rw add_zero at h3,
  have hf := le_refl a,
  exfalso,
  exact h3 hf,

  use d,
  rw succ_add,
  rw add_succ at h4,
  exact h4,