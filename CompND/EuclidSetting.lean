import CompND.EuclideanCarnotSettingExists

/-- A *name* for the Euclidean sub-elliptic setting on `ℝᴺ`: one setting witnessing
`EuclideanCarnotSettingExists N`, chosen once and for all for each `N`. The existence
theorem supplies the witness and all of its properties; this definition only fixes one, so
that the setting can be *named in a statement*. That is what is needed: a hypothesis such as
`CitedResults (EuclidSetting m)` -- the cited results at the Euclidean setting on `ℝᵐ`, which
case (iii) of thm:uncond applies there -- cannot be written at all while the setting is only
known to exist inside a proof. Nothing beyond the seven identities of
`EuclideanCarnotSettingExists`, and the fields every setting carries, is available about it;
in particular its first-layer projection is *not* assumed to be the identity. -/
noncomputable def EuclidSetting (N : ℕ) : CarnotSetting :=
  (EuclideanCarnotSettingExists N).choose
